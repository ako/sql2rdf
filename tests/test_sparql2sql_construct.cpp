/**
 * Structural tests for CONSTRUCT translation. The DuckDB execution tests
 * (tests/duckdb/, "construct_*") check the triples themselves.
 */

#include <catch2/catch.hpp>

#include <string>

#ifndef SOURCE_R2RML_DIR
#define SOURCE_R2RML_DIR ""
#endif

#include "r2rml/R2RMLMapping.h"
#include "r2rml/R2RMLParser.h"
#include "sparql-parser/Parser.h"
#include "sparql2sql/DuckDbDialect.h"
#include "sparql2sql/TranslationError.h"
#include "sparql2sql/Translator.h"
#include "sparql2sql/VocabularyCheck.h"

using r2rml::R2RMLMapping;
using r2rml::R2RMLParser;
using sparql::Parser;
using sparql2sql::DuckDbDialect;
using sparql2sql::translateQuery;
using sparql2sql::TranslationError;

namespace {

std::string translateConstruct(const std::string &query, const char *mappingFile = "example_emp_dept.ttl") {
	Parser parser;
	auto q = parser.parseString("PREFIX ex: <http://example.com/ns#>\n" + query);
	R2RMLParser mappingParser;
	R2RMLMapping mapping = mappingParser.parse(std::string(SOURCE_R2RML_DIR) + mappingFile);
	DuckDbDialect dialect;
	return translateQuery(*q, mapping, dialect);
}

} // namespace

TEST_CASE("CONSTRUCT: the result has read_rdf's triple columns", "[sparql2sql]") {
	const std::string sql = translateConstruct("CONSTRUCT { ?e ex:label ?n } WHERE { ?e ex:name ?n }");
	for (const char *col : {"\"subject\"", "\"predicate\"", "\"object\"", "\"object_datatype\"", "\"object_lang\""}) {
		CHECK(sql.find(col) != std::string::npos);
	}
	CHECK(sql.find("SELECT DISTINCT CAST(") != std::string::npos);
	// One template triple needs no arm numbering.
	CHECK(sql.find("VALUES") == std::string::npos);
}

TEST_CASE("CONSTRUCT: several template triples come from one scan of the solutions", "[sparql2sql]") {
	const std::string sql =
	    translateConstruct("CONSTRUCT { ?e ex:label ?n ; ex:inDept ?d } WHERE { ?e ex:name ?n ; ex:department ?d }");
	CHECK(sql.find("CROSS JOIN (VALUES (1), (2))") != std::string::npos);
	CHECK(sql.find("UNION") == std::string::npos);
}

TEST_CASE("CONSTRUCT: a template blank node numbers the solutions", "[sparql2sql]") {
	const std::string sql = translateConstruct("CONSTRUCT { ?e ex:card _:c } WHERE { ?e ex:name ?n }");
	CHECK(sql.find("ROW_NUMBER() OVER ()") != std::string::npos);
	CHECK(sql.find("'_:c_'") != std::string::npos);
}

TEST_CASE("CONSTRUCT: a template triple that can never be valid is left out", "[sparql2sql]") {
	// ?n is always a literal, so it can never be a subject; nothing else remains.
	const std::string sql = translateConstruct("CONSTRUCT { ?n ex:nameOf ?e } WHERE { ?e ex:name ?n }");
	CHECK(sql.find("WHERE FALSE") != std::string::npos);
	// A variable the WHERE clause never binds yields no triple either.
	CHECK(translateConstruct("CONSTRUCT { ?e ex:x ?unbound } WHERE { ?e ex:name ?n }").find("WHERE FALSE") !=
	      std::string::npos);
}

TEST_CASE("CONSTRUCT: a term kind the mapping leaves open is decided from the row's tag", "[sparql2sql]") {
	const std::string sql =
	    translateConstruct("CONSTRUCT { ?x ex:back ?m } WHERE { ?m ex:mixed ?x }", "sparql2sql_terms.ttl");
	CHECK(sql.find("\"d_x\"") != std::string::npos);
	CHECK(sql.find("IN ('I', 'B')") != std::string::npos);
}

TEST_CASE("CONSTRUCT: the vocabulary check reads the WHERE clause, not the template", "[sparql2sql]") {
	// ex:label is a new term the query writes, not one the mapping must produce.
	Parser parser;
	auto q = parser.parseString("PREFIX ex: <http://example.com/ns#>\n"
	                            "CONSTRUCT { ?e ex:label ?n } WHERE { ?e ex:name ?n }");
	R2RMLParser mappingParser;
	R2RMLMapping mapping = mappingParser.parse(SOURCE_R2RML_DIR "example_emp_dept.ttl");
	CHECK_NOTHROW(sparql2sql::checkVocabulary(*q, mapping));
}

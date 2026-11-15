/**
 * Structural tests for result term tags (TranslateOptions::termTags). The
 * DuckDB execution tests ("term tags: ...") check the tag values per row.
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
#include "sparql2sql/Translator.h"

using r2rml::R2RMLMapping;
using r2rml::R2RMLParser;
using sparql::Parser;
using sparql2sql::DuckDbDialect;
using sparql2sql::TranslateOptions;
using sparql2sql::translateQuery;

namespace {

std::string translate(const std::string &body, bool tags, bool typed = false) {
	Parser parser;
	auto q = parser.parseString("PREFIX ex: <http://example.com/ns#>\n" + body);
	R2RMLParser mappingParser;
	R2RMLMapping mapping = mappingParser.parse(SOURCE_R2RML_DIR "sparql2sql_terms.ttl");
	DuckDbDialect dialect;
	TranslateOptions options;
	options.termTags = tags;
	options.typedResults = typed;
	return translateQuery(*q, mapping, dialect, nullptr, options);
}

} // namespace

TEST_CASE("term tags: settled terms get constant tags, guarded by the value", "[sparql2sql]") {
	const std::string sql = translate("SELECT ?m ?a ?t WHERE { ?m ex:amount ?a ; ex:title ?t }", true);
	CHECK(sql.find("ELSE 'I' END AS \"d_m\"") != std::string::npos);
	CHECK(sql.find("ELSE 'Dhttp://www.w3.org/2001/XMLSchema#integer' END AS \"d_a\"") != std::string::npos);
	CHECK(sql.find("ELSE '@en' END AS \"d_t\"") != std::string::npos);
}

TEST_CASE("term tags: a per-row term kind carries the computed tag column", "[sparql2sql]") {
	const std::string sql = translate("SELECT ?x WHERE { ?m ex:mixed ?x }", true);
	CHECK(sql.find(".\"d_x\" AS \"d_x\"") != std::string::npos);
	CHECK(sql.find("CASE WHEN") == std::string::npos);
}

TEST_CASE("term tags: SELECT * tags every query variable", "[sparql2sql]") {
	const std::string sql = translate("SELECT * WHERE { ?m ex:amount ?a }", true);
	CHECK(sql.find("AS \"d_m\"") != std::string::npos);
	CHECK(sql.find("AS \"d_a\"") != std::string::npos);
}

TEST_CASE("term tags: combine with typed results; off by default", "[sparql2sql]") {
	const std::string both = translate("SELECT ?m ?a WHERE { ?m ex:amount ?a }", true, true);
	CHECK(both.find("REPLACE (TRY_CAST(") != std::string::npos);
	CHECK(both.find("AS \"d_a\"") != std::string::npos);
	CHECK(translate("SELECT ?m ?a WHERE { ?m ex:amount ?a }", false).find("d_") == std::string::npos);
	// ASK and CONSTRUCT keep their fixed shapes.
	CHECK(translate("ASK { ?m ex:amount ?a }", true).find("d_") == std::string::npos);
}

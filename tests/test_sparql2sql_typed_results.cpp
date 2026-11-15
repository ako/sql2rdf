/**
 * Structural tests for typed results (TranslateOptions::typedResults). The
 * DuckDB execution tests ("typed results: ...") check the actual column types.
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
#include "sparql2sql/TypeCatalog.h"

using r2rml::R2RMLMapping;
using r2rml::R2RMLParser;
using sparql::Parser;
using sparql2sql::DuckDbDialect;
using sparql2sql::TranslateOptions;
using sparql2sql::translateQuery;

namespace {

std::string translate(const std::string &body, bool typed, const sparql2sql::TypeCatalog *catalog = nullptr) {
	Parser parser;
	auto q = parser.parseString("PREFIX ex: <http://example.com/ns#>\n" + body);
	R2RMLParser mappingParser;
	R2RMLMapping mapping = mappingParser.parse(SOURCE_R2RML_DIR "sparql2sql_terms.ttl");
	DuckDbDialect dialect;
	TranslateOptions options;
	options.typedResults = typed;
	return translateQuery(*q, mapping, dialect, catalog, options);
}

} // namespace

TEST_CASE("typed results: settled columns are cast in a REPLACE wrapper", "[sparql2sql]") {
	const std::string sql = translate("SELECT ?m ?a WHERE { ?m ex:amount ?a }", true);
	CHECK(sql.find("SELECT * REPLACE (TRY_CAST(") != std::string::npos);
	CHECK(sql.find("\"v_a\" AS BIGINT) AS \"v_a\"") != std::string::npos);
	// The IRI column is not touched.
	CHECK(sql.find("\"v_m\" AS") == std::string::npos);
}

TEST_CASE("typed results: the declared column type wins when it matches the datatype", "[sparql2sql]") {
	sparql2sql::TypeCatalog cat;
	cat.columnTypes["MEASURES"]["AMOUNT"] = "INTEGER";
	CHECK(translate("SELECT ?a WHERE { ?m ex:amount ?a }", true, &cat).find("AS INTEGER) AS \"v_a\"") !=
	      std::string::npos);
	// A computed item is not a copy of the column, so it gets the generic type.
	CHECK(translate("SELECT (?a AS ?b) WHERE { ?m ex:amount ?a }", true, &cat).find("AS BIGINT) AS \"v_b\"") !=
	      std::string::npos);
}

TEST_CASE("typed results: nothing to type means no wrapper; off means no change", "[sparql2sql]") {
	CHECK(translate("SELECT ?m ?t WHERE { ?m ex:title ?t }", true).find("REPLACE") == std::string::npos);
	const std::string body = "SELECT ?a WHERE { ?m ex:amount ?a }";
	CHECK(translate(body, false) == translate(body, false, nullptr));
	CHECK(translate(body, false).find("REPLACE") == std::string::npos);
	// ASK and CONSTRUCT keep their own shapes.
	CHECK(translate("ASK { ?m ex:amount ?a }", true).find("REPLACE") == std::string::npos);
	CHECK(translate("CONSTRUCT { ?m ex:a ?a } WHERE { ?m ex:amount ?a }", true).find("REPLACE") == std::string::npos);
}

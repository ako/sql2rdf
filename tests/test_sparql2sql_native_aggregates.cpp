/**
 * Structural tests for native aggregates. The DuckDB execution tests
 * ("native aggregates: ...") check that results match the text path.
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

namespace {

std::string translate(const std::string &body, const sparql2sql::TypeCatalog *catalog) {
	sparql::Parser parser;
	auto q = parser.parseString("PREFIX ex: <http://example.com/ns#>\n" + body);
	r2rml::R2RMLParser mappingParser;
	r2rml::R2RMLMapping mapping = mappingParser.parse(SOURCE_R2RML_DIR "sparql2sql_native_aggregates.ttl");
	sparql2sql::DuckDbDialect dialect;
	return sparql2sql::translateQuery(*q, mapping, dialect, catalog, sparql2sql::TranslateOptions());
}

sparql2sql::TypeCatalog aggCatalog() {
	sparql2sql::TypeCatalog cat;
	cat.columnTypes["AGG_ROWS"] = {{"ID", "INTEGER"},  {"QTY", "INTEGER"}, {"PRICE", "DECIMAL(10,2)"},
	                               {"RATE", "DOUBLE"}, {"CODE", "VARCHAR"}, {"OWNER", "INTEGER"}};
	return cat;
}

} // namespace

TEST_CASE("native aggregates: COUNT of an always-bound variable counts rows", "[sparql2sql]") {
	const std::string sql = translate("SELECT (COUNT(?m) AS ?n) WHERE { ?m ex:qty ?q }", nullptr);
	CHECK(sql.find("COUNT(*)") != std::string::npos);
	// Without a catalog nothing native is projected.
	CHECK(sql.find("n_") == std::string::npos);
}

TEST_CASE("native aggregates: with a catalog, SUM reads the companion column", "[sparql2sql]") {
	const auto cat = aggCatalog();
	const std::string sql = translate("SELECT (SUM(?q) AS ?s) WHERE { ?m ex:qty ?q }", &cat);
	CHECK(sql.find("AS \"n_q\"") != std::string::npos);
	CHECK(sql.find("\"v_q\" AS BIGINT") == std::string::npos); // no text re-parse ...
	CHECK(sql.find(".\"n_q\" AS BIGINT") != std::string::npos); // ... the native value instead
	// A union root (two maps for one predicate) gets no companions.
	const std::string none = translate("SELECT (SUM(?q) AS ?s) WHERE { { ?m ex:qty ?q } UNION { ?m ex:price ?q } }", &cat);
	CHECK(none.find("n_q") == std::string::npos);
}

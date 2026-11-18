/**
 * rr:tableName as a schema-qualified name (R2RML 5.1): split into its SQL
 * identifiers, each quoted on its own, so a mapping can name a table outside
 * the default schema.
 */

#include <catch2/catch.hpp>

#include <string>
#include <vector>

#ifndef SOURCE_R2RML_DIR
#define SOURCE_R2RML_DIR ""
#endif

#include "r2rml/BaseTableOrView.h"
#include "r2rml/R2RMLMapping.h"
#include "r2rml/R2RMLParser.h"
#include "sparql-parser/Parser.h"
#include "sparql2sql/DuckDbDialect.h"
#include "sparql2sql/Ontology.h"
#include "sparql2sql/Translator.h"

using r2rml::BaseTableOrView;
using Parts = std::vector<std::string>;

namespace {

bool contains(const std::string &haystack, const std::string &needle) {
	return haystack.find(needle) != std::string::npos;
}

} // namespace

TEST_CASE("rr:tableName splits into its identifiers", "[r2rml]") {
	CHECK(BaseTableOrView::splitQualifiedName("EMP") == Parts {"EMP"});
	CHECK(BaseTableOrView::splitQualifiedName("hr.EMP") == Parts {"hr", "EMP"});
	CHECK(BaseTableOrView::splitQualifiedName("db.hr.EMP") == Parts {"db", "hr", "EMP"});
	CHECK(BaseTableOrView::splitQualifiedName("\"EMP\"") == Parts {"EMP"});
	CHECK(BaseTableOrView::splitQualifiedName("\"my.table\"") == Parts {"my.table"});
	CHECK(BaseTableOrView::splitQualifiedName("hr.\"Dept.Info\"") == Parts {"hr", "Dept.Info"});
	CHECK(BaseTableOrView::splitQualifiedName("\"a\"\"b\".c") == Parts {"a\"b", "c"});
}

TEST_CASE("an rr:tableName that does not parse stays one identifier", "[r2rml]") {
	for (const std::string name : {"a..b", ".a", "a.", "\"open", "\"a\"b", "a\"b"}) {
		CAPTURE(name);
		CHECK(BaseTableOrView::splitQualifiedName(name) == Parts {name});
	}
}

TEST_CASE("a base table's SQL name quotes each part", "[r2rml]") {
	CHECK(BaseTableOrView("EMP").sqlName() == "\"EMP\"");
	CHECK(BaseTableOrView("hr.EMP").sqlName() == "\"hr\".\"EMP\"");
	CHECK(BaseTableOrView("\"sales\".\"Dept.Info\"").sqlName() == "\"sales\".\"Dept.Info\"");
	CHECK(BaseTableOrView("a\"b").sqlName() == "\"a\"\"b\"");
}

TEST_CASE("the translator reads a schema-qualified table from its schema", "[sparql2sql]") {
	r2rml::R2RMLParser mappingParser;
	r2rml::R2RMLMapping mapping = mappingParser.parse(SOURCE_R2RML_DIR "sparql2sql_schema_table.ttl");
	REQUIRE(mapping.isValid());
	sparql::Parser parser;
	auto query = parser.parseString("PREFIX ex: <http://example.com/ns#>\nSELECT ?s ?n WHERE { ?s ex:name ?n }");
	sparql2sql::DuckDbDialect dialect;
	const std::string sql = sparql2sql::translateQuery(*query, mapping, dialect);
	INFO(sql);
	CHECK(contains(sql, "\"hr\".\"EMP\" AS "));
	CHECK(contains(sql, "\"sales\".\"Dept.Info\" AS "));
	CHECK_FALSE(contains(sql, "\"hr.EMP\""));
}

TEST_CASE("ontology views read a schema-qualified table from its schema", "[sparql2sql]") {
	r2rml::R2RMLParser mappingParser;
	r2rml::R2RMLMapping mapping = mappingParser.parse(SOURCE_R2RML_DIR "sparql2sql_schema_table.ttl");
	// A domain on a column-valued property derives a class from the rows where
	// the column is not NULL: a view over the table, which must name it by schema.
	sparql2sql::Ontology ontology;
	REQUIRE(ontology.addTriple("http://example.com/ns#name", "http://www.w3.org/2000/01/rdf-schema#domain",
	                           "http://example.com/ns#Named"));
	sparql2sql::saturateMapping(mapping, ontology);
	sparql::Parser parser;
	auto query = parser.parseString("PREFIX ex: <http://example.com/ns#>\nSELECT ?s WHERE { ?s a ex:Named }");
	sparql2sql::DuckDbDialect dialect;
	const std::string sql = sparql2sql::translateQuery(*query, mapping, dialect);
	INFO(sql);
	CHECK(contains(sql, "\"hr\".\"EMP\""));
	CHECK_FALSE(contains(sql, "\"hr.EMP\""));
}

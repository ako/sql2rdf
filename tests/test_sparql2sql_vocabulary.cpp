/**
 * Tests for checkVocabulary(): a constant class or property that no map in
 * the mapping can produce is reported (with a "did you mean" suggestion)
 * instead of silently yielding zero rows.
 */

#include <catch2/catch.hpp>

#include <string>

#ifndef SOURCE_R2RML_DIR
#define SOURCE_R2RML_DIR ""
#endif

#include "r2rml/R2RMLMapping.h"
#include "r2rml/R2RMLParser.h"
#include "sparql-parser/Parser.h"
#include "sparql2sql/TranslationError.h"
#include "sparql2sql/VocabularyCheck.h"

using r2rml::R2RMLMapping;
using r2rml::R2RMLParser;
using sparql::Parser;
using sparql2sql::checkVocabulary;
using sparql2sql::collectVocabulary;
using sparql2sql::findUnknownTerms;
using sparql2sql::TranslationError;
using sparql2sql::UnknownTerm;

namespace {

const char *const kPrefix = "PREFIX ex: <http://example.com/ns#>\n"
                            "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n";

const R2RMLMapping &empDept() {
	static R2RMLParser parser;
	static R2RMLMapping mapping = parser.parse(SOURCE_R2RML_DIR "example_emp_dept.ttl");
	return mapping;
}

const R2RMLMapping &genericTriples() {
	static R2RMLParser parser;
	static R2RMLMapping mapping = parser.parse(SOURCE_R2RML_DIR "sparql2sql_generic_triples.ttl");
	return mapping;
}

std::vector<UnknownTerm> unknownIn(const std::string &body, const R2RMLMapping &mapping) {
	Parser parser;
	auto query = parser.parseString(kPrefix + body);
	return findUnknownTerms(*query, collectVocabulary(mapping));
}

std::string errorFor(const std::string &body, const R2RMLMapping &mapping) {
	Parser parser;
	auto query = parser.parseString(kPrefix + body);
	try {
		checkVocabulary(*query, mapping);
	} catch (const TranslationError &e) {
		return e.what();
	}
	return "";
}

const std::string kEx = "http://example.com/ns#";

} // namespace

TEST_CASE("vocabulary: collects constant properties and rr:class classes", "[sparql2sql][vocabulary]") {
	const auto vocabulary = collectVocabulary(empDept());
	CHECK_FALSE(vocabulary.openProperties);
	CHECK_FALSE(vocabulary.openClasses);
	CHECK(vocabulary.properties.count(kEx + "name") == 1);
	CHECK(vocabulary.properties.count(kEx + "department") == 1);
	CHECK(vocabulary.properties.count("http://www.w3.org/1999/02/22-rdf-syntax-ns#type") == 1);
	CHECK(vocabulary.classes.count(kEx + "Employee") == 1);
	CHECK(vocabulary.classes.count(kEx + "Department") == 1);
}

TEST_CASE("vocabulary: a known query has no unknown terms", "[sparql2sql][vocabulary]") {
	CHECK(unknownIn("SELECT ?e ?n WHERE { ?e a ex:Employee ; ex:name ?n ; ex:department/ex:location ?l }", empDept())
	          .empty());
	CHECK(errorFor("SELECT ?e WHERE { ?e ex:name ?n }", empDept()).empty());
}

TEST_CASE("vocabulary: a misspelled property is reported with a suggestion", "[sparql2sql][vocabulary]") {
	const auto unknown = unknownIn("SELECT ?e ?n WHERE { ?e ex:nmae ?n }", empDept());
	REQUIRE(unknown.size() == 1);
	CHECK(unknown[0].kind == UnknownTerm::Kind::Property);
	CHECK(unknown[0].iri == kEx + "nmae");
	CHECK(unknown[0].suggestion == kEx + "name");

	const std::string message = errorFor("SELECT ?e ?n WHERE { ?e ex:nmae ?n }", empDept());
	CHECK(message.find("property <" + kEx + "nmae>") != std::string::npos);
	CHECK(message.find("did you mean <" + kEx + "name>?") != std::string::npos);
}

TEST_CASE("vocabulary: a misspelled class is reported with a suggestion", "[sparql2sql][vocabulary]") {
	const auto unknown = unknownIn("SELECT ?e WHERE { ?e a ex:Employe }", empDept());
	REQUIRE(unknown.size() == 1);
	CHECK(unknown[0].kind == UnknownTerm::Kind::Class);
	CHECK(unknown[0].suggestion == kEx + "Employee");
}

TEST_CASE("vocabulary: no suggestion for a term that is nothing like the vocabulary", "[sparql2sql][vocabulary]") {
	const auto unknown = unknownIn("SELECT ?e WHERE { ?e ex:completelyDifferentThing ?x }", empDept());
	REQUIRE(unknown.size() == 1);
	CHECK(unknown[0].suggestion.empty());
	CHECK(errorFor("SELECT ?e WHERE { ?e ex:completelyDifferentThing ?x }", empDept()).find("did you mean") ==
	      std::string::npos);
}

TEST_CASE("vocabulary: terms inside OPTIONAL, UNION, MINUS, GRAPH, EXISTS, paths and subqueries are checked",
          "[sparql2sql][vocabulary]") {
	CHECK(unknownIn("SELECT ?e WHERE { ?e ex:name ?n OPTIONAL { ?e ex:bogus1 ?x } }", empDept()).size() == 1);
	CHECK(unknownIn("SELECT ?e WHERE { { ?e ex:name ?n } UNION { ?e ex:bogus2 ?n } }", empDept()).size() == 1);
	CHECK(unknownIn("SELECT ?e WHERE { ?e ex:name ?n MINUS { ?e ex:bogus3 ?d } }", empDept()).size() == 1);
	CHECK(unknownIn("SELECT ?e WHERE { GRAPH ?g { ?e ex:bogus4 ?n } }", empDept()).size() == 1);
	CHECK(unknownIn("SELECT ?e WHERE { ?e ex:name ?n FILTER NOT EXISTS { ?e ex:bogus5 ?d } }", empDept()).size() == 1);
	CHECK(unknownIn("SELECT ?e WHERE { ?e ex:department/^ex:bogus6* ?d }", empDept()).size() == 1);
	CHECK(unknownIn("SELECT ?e WHERE { { SELECT ?e WHERE { ?e ex:bogus7 ?n } } }", empDept()).size() == 1);
}

TEST_CASE("vocabulary: negated property sets and repeated terms", "[sparql2sql][vocabulary]") {
	// A negated set lists IRIs to exclude - naming an absent one is harmless.
	CHECK(unknownIn("SELECT ?e WHERE { ?e !(ex:bogus) ?x }", empDept()).empty());
	// The same unknown term twice is reported once.
	CHECK(unknownIn("SELECT ?e WHERE { ?e ex:bogus ?x . ?y ex:bogus ?z }", empDept()).size() == 1);
}

TEST_CASE("vocabulary: a generic triple map makes properties and classes open", "[sparql2sql][vocabulary]") {
	const auto vocabulary = collectVocabulary(genericTriples());
	CHECK(vocabulary.openProperties);
	CHECK(vocabulary.openClasses);
	// Ontology-style queries over a generic map must never be rejected.
	CHECK(unknownIn("SELECT ?c WHERE { ?c rdfs:subClassOf* ex:Party . ?x a ex:Anything }", genericTriples()).empty());
	CHECK(errorFor("SELECT ?x WHERE { ?x ex:whatever ?y }", genericTriples()).empty());
}

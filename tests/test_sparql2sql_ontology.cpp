/**
 * Unit tests for Ontology and saturateMapping (RDFS-style query answering by
 * expanding the mapping). The DuckDB execution tests ("reasoning: ...") check
 * the answers against real rows.
 */

#include <catch2/catch.hpp>

#include <set>
#include <string>

#ifndef SOURCE_R2RML_DIR
#define SOURCE_R2RML_DIR ""
#endif

#include "r2rml/R2RMLMapping.h"
#include "r2rml/R2RMLParser.h"
#include "r2rml/SubjectMap.h"
#include "r2rml/TriplesMap.h"
#include "sparql-parser/Parser.h"
#include "sparql2sql/DuckDbDialect.h"
#include "sparql2sql/Ontology.h"
#include "sparql2sql/Translator.h"
#include "sparql2sql/VocabularyCheck.h"

using r2rml::R2RMLMapping;
using r2rml::R2RMLParser;
using sparql2sql::Ontology;
using sparql2sql::saturateMapping;

namespace {

const std::string kEx = "http://example.com/ns#";
const std::string kSubClassOf = "http://www.w3.org/2000/01/rdf-schema#subClassOf";
const std::string kSubPropertyOf = "http://www.w3.org/2000/01/rdf-schema#subPropertyOf";
const std::string kEquivalentClass = "http://www.w3.org/2002/07/owl#equivalentClass";
const std::string kRdfsLabel = "http://www.w3.org/2000/01/rdf-schema#label";

Ontology hrOntology() {
	Ontology o;
	o.addTriple(kEx + "Engineer", kSubClassOf, kEx + "Staff");
	o.addTriple(kEx + "Manager", kSubClassOf, kEx + "Staff");
	o.addTriple(kEx + "Staff", kSubClassOf, kEx + "Person");
	o.addTriple(kEx + "Unit", kEquivalentClass, kEx + "Org");
	o.addTriple(kEx + "fullName", kSubPropertyOf, kEx + "label");
	o.addTriple(kEx + "deptName", kSubPropertyOf, kEx + "label");
	o.addTriple(kEx + "label", kSubPropertyOf, kRdfsLabel);
	return o;
}

std::string translate(R2RMLMapping &mapping, const std::string &body) {
	sparql::Parser parser;
	auto q = parser.parseString(
	    "PREFIX ex: <http://example.com/ns#>\nPREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n" + body);
	sparql2sql::DuckDbDialect dialect;
	return sparql2sql::translateQuery(*q, mapping, dialect);
}

} // namespace

TEST_CASE("Ontology: hierarchies are transitive, equivalences go both ways", "[sparql2sql]") {
	Ontology o = hrOntology();
	CHECK(o.superClassesOf(kEx + "Engineer") == std::set<std::string> {kEx + "Staff", kEx + "Person"});
	CHECK(o.superClassesOf(kEx + "Person").empty());
	CHECK(o.superClassesOf(kEx + "Unit") == std::set<std::string> {kEx + "Org"});
	CHECK(o.superClassesOf(kEx + "Org") == std::set<std::string> {kEx + "Unit"});
	CHECK(o.superPropertiesOf(kEx + "fullName") == std::set<std::string> {kEx + "label", kRdfsLabel});
	CHECK(o.axiomCount() == 7);
}

TEST_CASE("Ontology: other triples, blank nodes and cycles are handled", "[sparql2sql]") {
	Ontology o;
	CHECK_FALSE(o.addTriple(kEx + "A", "http://www.w3.org/2000/01/rdf-schema#comment", kEx + "B"));
	CHECK_FALSE(o.addTriple(kEx + "A", kSubClassOf, "_:restriction1"));
	CHECK(o.addTriple(kEx + "A", kSubClassOf, kEx + "B"));
	CHECK(o.addTriple(kEx + "B", kSubClassOf, kEx + "C"));
	CHECK(o.addTriple(kEx + "C", kSubClassOf, kEx + "A"));
	// A cycle terminates, and a class is not its own superclass.
	CHECK(o.superClassesOf(kEx + "A") == std::set<std::string> {kEx + "B", kEx + "C"});
}

TEST_CASE("saturateMapping: adds superclasses and superproperties to the maps", "[sparql2sql]") {
	R2RMLParser parser;
	R2RMLMapping mapping = parser.parse(SOURCE_R2RML_DIR "sparql2sql_reasoning.ttl");
	REQUIRE(mapping.isValid());
	auto result = saturateMapping(mapping, hrOntology());
	// Engineers and Managers each gain Staff and Person; the Unit object gains Org.
	CHECK(result.classesAdded == 5);
	// fullName and deptName each gain ex:label and rdfs:label.
	CHECK(result.predicatesAdded == 4);
	// Saturating again adds nothing.
	auto again = saturateMapping(mapping, hrOntology());
	CHECK(again.classesAdded == 0);
	CHECK(again.predicatesAdded == 0);
}

TEST_CASE("saturateMapping: a superclass query reaches the subclass maps", "[sparql2sql]") {
	R2RMLParser parser;
	R2RMLMapping plain = parser.parse(SOURCE_R2RML_DIR "sparql2sql_reasoning.ttl");
	// Without the ontology ex:Person is unknown: no candidate, an empty relation.
	CHECK(translate(plain, "SELECT ?x WHERE { ?x a ex:Person }").find("\"EMP\"") == std::string::npos);
	CHECK_THROWS(sparql2sql::checkVocabulary(*sparql::Parser().parseString("PREFIX ex: <http://example.com/ns#>\n"
	                                                                       "SELECT ?x WHERE { ?x a ex:Person }"),
	                                         plain));

	R2RMLMapping saturated = parser.parse(SOURCE_R2RML_DIR "sparql2sql_reasoning.ttl");
	saturateMapping(saturated, hrOntology());
	CHECK(translate(saturated, "SELECT ?x WHERE { ?x a ex:Person }").find("\"EMP\"") != std::string::npos);
	CHECK(translate(saturated, "SELECT ?x ?l WHERE { ?x rdfs:label ?l }").find("\"DEPT\"") != std::string::npos);
	// The vocabulary check sees the inferred terms too.
	CHECK_NOTHROW(sparql2sql::checkVocabulary(*sparql::Parser().parseString("PREFIX ex: <http://example.com/ns#>\n"
	                                                                        "SELECT ?x WHERE { ?x a ex:Person }"),
	                                          saturated));
}

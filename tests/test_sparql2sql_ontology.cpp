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

namespace {

const std::string kRdfs = "http://www.w3.org/2000/01/rdf-schema#";
const std::string kOwl = "http://www.w3.org/2002/07/owl#";
const std::string kType = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";

// The ontology the DuckDB "reasoning: ..." cases use with sparql2sql_owl.ttl.
Ontology owlOntology() {
	Ontology o;
	o.addTriple(kEx + "worksIn", kRdfs + "domain", kEx + "Worker");
	o.addTriple(kEx + "Worker", kSubClassOf, kEx + "Agent");
	o.addTriple(kEx + "worksIn", kRdfs + "range", kEx + "Unit");
	o.addTriple(kEx + "memberOf", kRdfs + "domain", kEx + "Member");
	o.addTriple(kEx + "memberOf", kRdfs + "range", kEx + "Team");
	o.addTriple(kEx + "homepage", kRdfs + "domain", kEx + "HasPage");
	o.addTriple(kEx + "name", kRdfs + "domain", kEx + "Named");
	o.addTriple(kEx + "name", kRdfs + "range", kEx + "NotForLiterals");
	o.addTriple(kEx + "worksIn", kOwl + "inverseOf", kEx + "hasWorker");
	o.addTriple(kEx + "hasMember", kOwl + "inverseOf", kEx + "memberOf");
	o.addTriple(kEx + "manager", kOwl + "inverseOf", kEx + "manages");
	o.addTriple(kEx + "manages", kSubPropertyOf, kEx + "leads");
	o.addTriple(kEx + "leads", kRdfs + "domain", kEx + "Lead");
	o.addTriple(kEx + "next", kType, kOwl + "TransitiveProperty");
	return o;
}

std::size_t transitiveRewrites(const std::string &body) {
	auto q = sparql::Parser().parseString("PREFIX ex: <http://example.com/ns#>\n" + body);
	return sparql2sql::applyTransitiveProperties(*q, owlOntology());
}

} // namespace

TEST_CASE("Ontology: domain, range, inverse, symmetric and transitive axioms", "[sparql2sql]") {
	Ontology o = owlOntology();
	CHECK(o.axiomCount() == 14);
	CHECK(o.domainsOf(kEx + "worksIn") == std::set<std::string> {kEx + "Worker"});
	CHECK(o.rangesOf(kEx + "worksIn") == std::set<std::string> {kEx + "Unit"});
	CHECK(o.domainsOf(kEx + "nothing").empty());
	// owl:inverseOf works in both directions.
	CHECK(o.inversesOf(kEx + "memberOf") == std::set<std::string> {kEx + "hasMember"});
	CHECK(o.inversesOf(kEx + "hasMember") == std::set<std::string> {kEx + "memberOf"});

	CHECK(o.addTriple(kEx + "knows", kType, kOwl + "SymmetricProperty"));
	CHECK(o.inversesOf(kEx + "knows") == std::set<std::string> {kEx + "knows"});
	CHECK(o.addTriple(kEx + "partOf", kOwl + "inverseOf", kEx + "partOf"));
	CHECK(o.inversesOf(kEx + "partOf") == std::set<std::string> {kEx + "partOf"});
	CHECK_FALSE(o.addTriple(kEx + "x", kType, kOwl + "FunctionalProperty"));

	// Transitive: declared, the inverse of one, an equivalent of one; not a subproperty.
	o.addTriple(kEx + "ancestorOf", kType, kOwl + "TransitiveProperty");
	o.addTriple(kEx + "descendantOf", kOwl + "inverseOf", kEx + "ancestorOf");
	o.addTriple(kEx + "forebearOf", "http://www.w3.org/2002/07/owl#equivalentProperty", kEx + "ancestorOf");
	o.addTriple(kEx + "parentOf", kSubPropertyOf, kEx + "ancestorOf");
	CHECK(o.isTransitive(kEx + "ancestorOf"));
	CHECK(o.isTransitive(kEx + "descendantOf"));
	CHECK(o.isTransitive(kEx + "forebearOf"));
	CHECK_FALSE(o.isTransitive(kEx + "parentOf"));
}

TEST_CASE("saturateMapping: derives maps for inverses, domains and ranges", "[sparql2sql]") {
	R2RMLParser parser;
	R2RMLMapping mapping = parser.parse(SOURCE_R2RML_DIR "sparql2sql_owl.ttl");
	REQUIRE(mapping.isValid());
	const std::size_t before = mapping.triplesMaps.size();
	auto result = saturateMapping(mapping, owlOntology());
	// Inverses: hasWorker, hasMember (the join reversed), manages. Domains and
	// ranges: name (domain), worksIn (domain, range), memberOf (domain, range),
	// and leads' domain on the manages inverse. homepage's domain goes on the
	// subject map; name's range is skipped (a literal).
	CHECK(result.triplesMapsAdded == 9);
	CHECK(mapping.triplesMaps.size() == before + 9);
	REQUIRE(mapping.isValid());

	// A domain over a nullable object reads only the rows where it is set.
	const std::string worker = translate(mapping, "SELECT ?x WHERE { ?x a ex:Worker }");
	CHECK(worker.find("\"t\".\"DEPTNO\" IS NOT NULL") != std::string::npos);
	// Through a join: rows whose join finds a parent row.
	const std::string member = translate(mapping, "SELECT ?x WHERE { ?x a ex:Member }");
	CHECK(member.find("EXISTS (SELECT 1 FROM \"DEPT\" AS \"o\" WHERE \"o\".\"DEPTNO\" = \"t\".\"DEPTNO\"") !=
	      std::string::npos);
	// A domain whose object is made of the subject's columns needs no filtered view.
	const std::string page = translate(mapping, "SELECT ?x WHERE { ?x a ex:HasPage }");
	CHECK(page.find("AS \"t\"") == std::string::npos);
	CHECK(page.find("\"EMP\"") != std::string::npos);
}

TEST_CASE("saturateMapping: no domain view for a class the subject map already has", "[sparql2sql]") {
	R2RMLParser parser;
	R2RMLMapping mapping = parser.parse(SOURCE_R2RML_DIR "sparql2sql_owl.ttl");
	REQUIRE(mapping.isValid());
	// The employees map declares ex:Worker itself, so worksIn's domain adds nothing.
	for (auto &tm : mapping.triplesMaps) {
		if (tm && tm->id.find("Employees") != std::string::npos) {
			tm->subjectMap->classIRIs.push_back(kEx + "Worker");
		}
	}
	auto result = saturateMapping(mapping, owlOntology());
	CHECK(result.triplesMapsAdded == 8); // one fewer than without the class
	const std::string worker = translate(mapping, "SELECT ?x WHERE { ?x a ex:Worker }");
	CHECK(worker.find("\"DEPTNO\" IS NOT NULL") == std::string::npos);
	CHECK(worker.find("\"EMP\"") != std::string::npos);
}

TEST_CASE("applyTransitiveProperties: rewrites transitive steps to P+", "[sparql2sql]") {
	CHECK(transitiveRewrites("SELECT * WHERE { ?a ex:next ?b }") == 1);
	CHECK(transitiveRewrites("SELECT * WHERE { ?a ex:name ?b }") == 0);
	CHECK(transitiveRewrites("SELECT * WHERE { ?a ex:next/ex:next ?b }") == 2);
	CHECK(transitiveRewrites("SELECT * WHERE { ?a ^ex:next|ex:name ?b }") == 1);
	// Already a closure: left alone.
	CHECK(transitiveRewrites("SELECT * WHERE { ?a ex:next* ?b }") == 0);
	CHECK(transitiveRewrites("SELECT * WHERE { ?a ex:next+ ?b }") == 0);
	// Nested patterns, EXISTS and subqueries.
	CHECK(transitiveRewrites("SELECT * WHERE { ?a ex:name ?n OPTIONAL { ?a ex:next ?b } "
	                         "FILTER EXISTS { ?b ex:next ?c } { SELECT ?d WHERE { ?d ex:next ?e } } }") == 3);
	// CONSTRUCT WHERE: the parser copied the template, so only the pattern changes.
	CHECK(transitiveRewrites("CONSTRUCT WHERE { ?a ex:next ?b }") == 1);
	CHECK(transitiveRewrites("CONSTRUCT { ?a ex:next ?b } WHERE { ?a ex:next ?b }") == 1);

	// The rewritten query translates to a recursive CTE.
	R2RMLParser parser;
	R2RMLMapping mapping = parser.parse(SOURCE_R2RML_DIR "sparql2sql_owl.ttl");
	auto q = sparql::Parser().parseString("PREFIX ex: <http://example.com/ns#>\nSELECT * WHERE { ?a ex:next ?b }");
	sparql2sql::applyTransitiveProperties(*q, owlOntology());
	sparql2sql::DuckDbDialect dialect;
	CHECK(sparql2sql::translateQuery(*q, mapping, dialect).find("RECURSIVE") != std::string::npos);
}

#pragma once

#include <cstddef>
#include <map>
#include <set>
#include <string>

namespace r2rml {
class R2RMLMapping;
} // namespace r2rml

namespace sparql2sql {

/// The part of an ontology that query answering can use by expanding the
/// mapping: the class and property hierarchies. Built from plain
/// (subject, predicate, object) IRI triples, so the caller decides where the
/// ontology comes from (a Turtle file, a table, a triple store).
///
/// Recognised axioms, all between named IRIs:
///   - rdfs:subClassOf, rdfs:subPropertyOf
///   - owl:equivalentClass, owl:equivalentProperty (a sub-relation both ways)
/// Everything else is ignored, including axioms whose object is a blank node
/// (OWL restrictions and other class expressions).
class Ontology {
public:
	/// Record one triple; returns true if it was one of the recognised axioms.
	bool addTriple(const std::string &subject, const std::string &predicate, const std::string &object);

	/// Every class `cls` is a subclass of, directly or through a chain, not
	/// including `cls` itself. Cycles (equivalent classes) are handled.
	std::set<std::string> superClassesOf(const std::string &cls) const;

	/// The same for properties.
	std::set<std::string> superPropertiesOf(const std::string &property) const;

	/// Number of recognised axioms recorded.
	std::size_t axiomCount() const {
		return axioms_;
	}

private:
	std::map<std::string, std::set<std::string>> subClassOf_;
	std::map<std::string, std::set<std::string>> subPropertyOf_;
	std::size_t axioms_ = 0;
};

/// What saturateMapping added.
struct SaturationResult {
	std::size_t classesAdded = 0;    ///< rr:class (or rdf:type object) entries added
	std::size_t predicatesAdded = 0; ///< rr:predicate entries added
};

/// RDFS-style query answering by mapping saturation (the "T-mapping" approach
/// Ontop uses): every map that produces class C also produces each superclass
/// of C, and every predicate-object map with constant predicate P also
/// produces each superproperty of P. A query for ex:Person then matches the
/// ex:Employee rows with no change to the query or the translator, and
/// because a triple pattern's candidate maps are combined with a
/// duplicate-removing union, a resource typed by several subclasses still
/// appears once.
///
/// Only constant classes and predicates can be expanded: a triples map whose
/// predicate or rdf:type object comes from a column (a generic triple map) is
/// left as it is, so facts it produces are not reasoned over.
SaturationResult saturateMapping(r2rml::R2RMLMapping &mapping, const Ontology &ontology);

} // namespace sparql2sql

#pragma once

#include <cstddef>
#include <map>
#include <set>
#include <string>

namespace r2rml {
class R2RMLMapping;
} // namespace r2rml

namespace sparql::ast {
class Query;
} // namespace sparql::ast

namespace sparql2sql {

/// The part of an ontology that query answering can use, either by expanding
/// the mapping (saturateMapping) or by rewriting the query
/// (applyTransitiveProperties). Built from plain (subject, predicate, object)
/// IRI triples, so the caller decides where the ontology comes from (a Turtle
/// file, a table, a triple store).
///
/// Recognised axioms, all between named IRIs:
///   - rdfs:subClassOf, rdfs:subPropertyOf
///   - owl:equivalentClass, owl:equivalentProperty (a sub-relation both ways)
///   - rdfs:domain, rdfs:range
///   - owl:inverseOf; `P rdf:type owl:SymmetricProperty` (P is its own inverse)
///   - `P rdf:type owl:TransitiveProperty`
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

	/// The classes rdfs:domain / rdfs:range declare for `property` (directly;
	/// a superproperty's domain reaches the property's triples through
	/// saturation, which gives them the superproperty too).
	std::set<std::string> domainsOf(const std::string &property) const;
	std::set<std::string> rangesOf(const std::string &property) const;

	/// The properties declared inverse to `property` (owl:inverseOf in either
	/// direction; a symmetric property is its own inverse).
	std::set<std::string> inversesOf(const std::string &property) const;

	/// Whether `property` is transitive: declared owl:TransitiveProperty, or
	/// the inverse or an equivalent of one that is.
	bool isTransitive(const std::string &property) const;

	/// Number of recognised axioms recorded.
	std::size_t axiomCount() const {
		return axioms_;
	}

private:
	std::map<std::string, std::set<std::string>> subClassOf_;
	std::map<std::string, std::set<std::string>> subPropertyOf_;
	std::map<std::string, std::set<std::string>> domain_;
	std::map<std::string, std::set<std::string>> range_;
	std::map<std::string, std::set<std::string>> inverseOf_;
	std::set<std::string> transitive_;
	std::size_t axioms_ = 0;
};

/// What saturateMapping added.
struct SaturationResult {
	std::size_t classesAdded = 0;     ///< rr:class (or rdf:type object) entries added
	std::size_t predicatesAdded = 0;  ///< rr:predicate entries added
	std::size_t triplesMapsAdded = 0; ///< triples maps derived for inverses, domains and ranges
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
/// Inverse properties, domains and ranges are expanded the same way, by adding
/// triples maps that produce the entailed triples:
///   - owl:inverseOf Q on predicate P: a map with subject and object swapped
///     produces (o Q s) for every (s P o). For a referencing object map the
///     join is reversed: the new map runs over the parent's logical table.
///   - rdfs:domain D: the subject gets class D. When the object is produced
///     whenever the subject is (a constant, or only the subject's columns) the
///     class is added to the subject map itself; otherwise a new map does it
///     over the rows where the object (and any graph) is not NULL, or, for a
///     referencing object map, where the join finds a parent row.
///   - rdfs:range R: the object, when it is an IRI or blank node, becomes the
///     subject of a new map with class R, over the rows that produce the triple.
/// The filtered maps are rr:sqlQuery views over the original logical table,
/// with ANSI double-quoted identifiers, so they hold for any dialect that
/// accepts those. Literal objects get no class from a range (they cannot be
/// subjects), and a referencing object map whose triple has a graph map that
/// reads child columns gets no range class (the graph cannot be evaluated over
/// the parent's rows).
///
/// The steps run in a fixed order, not to a fixpoint: superproperties,
/// inverses, superproperties again (of the inverses), domains and ranges, and
/// last superclasses (of every class added). That covers chains such as
/// "the inverse of a superproperty has a domain whose superclass is queried".
///
/// Only constant classes and predicates can be expanded: a triples map whose
/// predicate or rdf:type object comes from a column (a generic triple map) is
/// left as it is, so facts it produces are not reasoned over.
SaturationResult saturateMapping(r2rml::R2RMLMapping &mapping, const Ontology &ontology);

/// Transitive properties cannot be expanded in the mapping: a chain of any
/// length is entailed. Instead, every triple pattern or property path step
/// whose predicate is a transitive property P is rewritten to the path P+ (one
/// or more P steps, translated through a recursive CTE). Steps already under
/// `*` or `+` are left alone. Returns the number of steps rewritten.
std::size_t applyTransitiveProperties(sparql::ast::Query &query, const Ontology &ontology);

} // namespace sparql2sql

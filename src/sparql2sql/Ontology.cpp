#include "sparql2sql/Ontology.h"

#include <algorithm>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "r2rml/ConstantTermMap.h"
#include "r2rml/PredicateObjectMap.h"
#include "r2rml/R2RMLMapping.h"
#include "r2rml/SubjectMap.h"
#include "r2rml/TermMap.h"
#include "r2rml/TriplesMap.h"
#include "rdf/Term.h"

namespace sparql2sql {

namespace {

const char *const kRdfType = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const char *const kSubClassOf = "http://www.w3.org/2000/01/rdf-schema#subClassOf";
const char *const kSubPropertyOf = "http://www.w3.org/2000/01/rdf-schema#subPropertyOf";
const char *const kEquivalentClass = "http://www.w3.org/2002/07/owl#equivalentClass";
const char *const kEquivalentProperty = "http://www.w3.org/2002/07/owl#equivalentProperty";

bool isBlankNode(const std::string &term) {
	return term.rfind("_:", 0) == 0;
}

// Everything reachable from `start` along `edges`, excluding `start`.
std::set<std::string> reachable(const std::map<std::string, std::set<std::string>> &edges, const std::string &start) {
	std::set<std::string> seen;
	std::vector<std::string> todo = {start};
	while (!todo.empty()) {
		const std::string current = todo.back();
		todo.pop_back();
		auto it = edges.find(current);
		if (it == edges.end()) {
			continue;
		}
		for (const auto &next : it->second) {
			if (next != start && seen.insert(next).second) {
				todo.push_back(next);
			}
		}
	}
	return seen;
}

// The constant IRI a term map always produces, or "" if it is not one.
std::string constantIri(const std::unique_ptr<r2rml::TermMap> &map) {
	const auto *constant = dynamic_cast<const r2rml::ConstantTermMap *>(map.get());
	if (constant == nullptr || constant->constantValue.kind() != rdf::TermKind::Iri) {
		return std::string();
	}
	return constant->constantValue.lexical();
}

std::unique_ptr<r2rml::TermMap> constantIriMap(const std::string &iri) {
	auto map = std::make_unique<r2rml::ConstantTermMap>(rdf::Term::iri(iri));
	map->termType = r2rml::TermType::IRI;
	return map;
}

// Append to `maps` a constant map for each IRI in `add` it does not already
// produce. Returns how many were added.
std::size_t addConstantIris(std::vector<std::unique_ptr<r2rml::TermMap>> &maps, const std::set<std::string> &add) {
	std::set<std::string> present;
	for (const auto &m : maps) {
		present.insert(constantIri(m));
	}
	std::size_t added = 0;
	for (const auto &iri : add) {
		if (present.insert(iri).second) {
			maps.push_back(constantIriMap(iri));
			++added;
		}
	}
	return added;
}

} // namespace

bool Ontology::addTriple(const std::string &subject, const std::string &predicate, const std::string &object) {
	if (isBlankNode(subject) || isBlankNode(object) || subject == object) {
		return false;
	}
	if (predicate == kSubClassOf) {
		subClassOf_[subject].insert(object);
	} else if (predicate == kEquivalentClass) {
		subClassOf_[subject].insert(object);
		subClassOf_[object].insert(subject);
	} else if (predicate == kSubPropertyOf) {
		subPropertyOf_[subject].insert(object);
	} else if (predicate == kEquivalentProperty) {
		subPropertyOf_[subject].insert(object);
		subPropertyOf_[object].insert(subject);
	} else {
		return false;
	}
	++axioms_;
	return true;
}

std::set<std::string> Ontology::superClassesOf(const std::string &cls) const {
	return reachable(subClassOf_, cls);
}

std::set<std::string> Ontology::superPropertiesOf(const std::string &property) const {
	return reachable(subPropertyOf_, property);
}

SaturationResult saturateMapping(r2rml::R2RMLMapping &mapping, const Ontology &ontology) {
	SaturationResult result;
	if (ontology.axiomCount() == 0) {
		return result;
	}
	for (auto &tmPtr : mapping.triplesMaps) {
		if (!tmPtr) {
			continue;
		}
		r2rml::TriplesMap &tm = *tmPtr;

		// rr:class on the subject map.
		if (tm.subjectMap) {
			std::vector<std::string> &classes = tm.subjectMap->classIRIs;
			std::set<std::string> present(classes.begin(), classes.end());
			const std::vector<std::string> declared = classes;
			for (const auto &cls : declared) {
				for (const auto &super : ontology.superClassesOf(cls)) {
					if (present.insert(super).second) {
						classes.push_back(super);
						++result.classesAdded;
					}
				}
			}
		}

		for (auto &pomPtr : tm.predicateObjectMaps) {
			if (!pomPtr) {
				continue;
			}
			r2rml::PredicateObjectMap &pom = *pomPtr;
			std::set<std::string> predicates;
			bool typePredicate = false;
			for (const auto &pm : pom.predicateMaps) {
				const std::string iri = constantIri(pm);
				if (iri == kRdfType) {
					typePredicate = true;
				} else if (!iri.empty()) {
					predicates.insert(iri);
				}
			}

			// Superproperties of each constant predicate.
			std::set<std::string> supers;
			for (const auto &p : predicates) {
				const std::set<std::string> up = ontology.superPropertiesOf(p);
				supers.insert(up.begin(), up.end());
			}
			result.predicatesAdded += addConstantIris(pom.predicateMaps, supers);

			// `rr:predicate rdf:type; rr:object <C>` written as a predicate-object map.
			// Only safe when rdf:type is this map's only predicate: otherwise the
			// added objects would also be produced for the other predicates.
			if (typePredicate && pom.predicateMaps.size() == 1) {
				std::set<std::string> superClasses;
				for (const auto &om : pom.objectMaps) {
					const std::string cls = constantIri(om);
					if (!cls.empty()) {
						const std::set<std::string> up = ontology.superClassesOf(cls);
						superClasses.insert(up.begin(), up.end());
					}
				}
				result.classesAdded += addConstantIris(pom.objectMaps, superClasses);
			}
		}
	}
	return result;
}

} // namespace sparql2sql

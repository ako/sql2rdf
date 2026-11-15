#pragma once

#include <set>
#include <string>
#include <vector>

namespace sparql {
namespace ast {
class Query;
} // namespace ast
} // namespace sparql

namespace r2rml {
class R2RMLMapping;
} // namespace r2rml

namespace sparql2sql {

/// The classes and properties an R2RML mapping can produce.
///
/// A predicate map that is not a constant (rr:column / rr:template) can
/// produce any predicate IRI, so the property set is then "open" and no
/// property is unknown; likewise an rdf:type object that is not a constant
/// makes the class set open. A mapping with a generic triple map (for
/// example an ontology loaded as subject/predicate/object rows) is
/// therefore never checked - that is the conservative answer, never a false
/// error.
struct MappingVocabulary {
	std::set<std::string> properties;
	std::set<std::string> classes;
	bool openProperties {false};
	bool openClasses {false};
};

[[nodiscard]] MappingVocabulary collectVocabulary(const r2rml::R2RMLMapping &mapping);

/// One constant IRI in a query that the mapping can never produce.
struct UnknownTerm {
	enum class Kind { Property, Class };
	Kind kind;
	std::string iri;
	std::string suggestion; // closest known IRI of the same kind, or empty
};

/// Every constant property (in a predicate position or property path) and
/// every constant class (the object of an `a` / rdf:type pattern) in `query`,
/// including those inside OPTIONAL, UNION, MINUS, GRAPH, EXISTS and
/// subqueries, that `vocabulary` cannot produce. Negated property sets and
/// SERVICE blocks are not checked: the former names IRIs to exclude, the
/// latter is answered elsewhere.
[[nodiscard]] std::vector<UnknownTerm> findUnknownTerms(const sparql::ast::Query &query,
                                                        const MappingVocabulary &vocabulary);

/// Throws TranslationError listing every unknown term (with a "did you mean"
/// suggestion where one is close) when `query` uses a class or property no
/// map in `mapping` can produce. Such a pattern can never match, so without
/// this check a misspelled term silently yields zero rows, which reads like
/// "no data". Callers decide whether to run it: translateQuery() does not.
void checkVocabulary(const sparql::ast::Query &query, const r2rml::R2RMLMapping &mapping);

} // namespace sparql2sql

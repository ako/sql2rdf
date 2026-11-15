#include "sparql2sql/VocabularyCheck.h"

#include "r2rml/ConstantTermMap.h"
#include "r2rml/PredicateObjectMap.h"
#include "r2rml/R2RMLMapping.h"
#include "r2rml/SubjectMap.h"
#include "r2rml/TriplesMap.h"
#include "rdf/Term.h"
#include "sparql-parser/ast/Expression.h"
#include "sparql-parser/ast/GraphPattern.h"
#include "sparql-parser/ast/Path.h"
#include "sparql-parser/ast/Query.h"
#include "sparql-parser/ast/Term.h"
#include "sparql2sql/TranslationError.h"

#include <algorithm>
#include <cstddef>
#include <vector>

namespace sparql2sql {

namespace {

namespace ast = sparql::ast;

/// The IRI a term map always produces, or nullptr when it is not a constant IRI.
const rdf::Term *constantIri(const r2rml::TermMap &map) {
	const auto *constant = dynamic_cast<const r2rml::ConstantTermMap *>(&map);
	if (constant == nullptr || !constant->constantValue.isIri()) {
		return nullptr;
	}
	return &constant->constantValue;
}

// --- Query walk ---------------------------------------------------------------

struct Walker {
	const MappingVocabulary &vocabulary;
	std::vector<UnknownTerm> found;
	std::set<std::string> reported;

	void unknown(UnknownTerm::Kind kind, const std::string &iri) {
		const bool isClass = kind == UnknownTerm::Kind::Class;
		if (isClass ? (vocabulary.openClasses || vocabulary.classes.count(iri) > 0)
		            : (vocabulary.openProperties || vocabulary.properties.count(iri) > 0)) {
			return;
		}
		if (!reported.insert((isClass ? "c " : "p ") + iri).second) {
			return;
		}
		found.push_back(UnknownTerm {kind, iri, std::string()});
	}

	void path(const ast::PropertyPathExpr &expr) {
		switch (expr.kind()) {
		case ast::PathKind::Predicate:
			unknown(UnknownTerm::Kind::Property, static_cast<const ast::PredicatePath &>(expr).iri->value);
			return;
		case ast::PathKind::Inverse:
			path(*static_cast<const ast::InversePath &>(expr).child);
			return;
		case ast::PathKind::Sequence: {
			const auto &seq = static_cast<const ast::SequencePath &>(expr);
			path(*seq.left);
			path(*seq.right);
			return;
		}
		case ast::PathKind::Alternative: {
			const auto &alt = static_cast<const ast::AlternativePath &>(expr);
			path(*alt.left);
			path(*alt.right);
			return;
		}
		case ast::PathKind::ZeroOrMore:
			path(*static_cast<const ast::ZeroOrMorePath &>(expr).child);
			return;
		case ast::PathKind::OneOrMore:
			path(*static_cast<const ast::OneOrMorePath &>(expr).child);
			return;
		case ast::PathKind::ZeroOrOne:
			path(*static_cast<const ast::ZeroOrOnePath &>(expr).child);
			return;
		case ast::PathKind::Variable:
		case ast::PathKind::NegatedPropertySet:
			return;
		}
	}

	void triple(const ast::TriplePattern &tp) {
		if (!tp.predicate) {
			return;
		}
		path(*tp.predicate);
		// A plain `?s a <Class>` (not a longer path) names a class.
		if (tp.predicate->kind() == ast::PathKind::Predicate && tp.object && tp.object->kind() == ast::TermKind::Iri &&
		    static_cast<const ast::PredicatePath &>(*tp.predicate).iri->value == rdf::RDF_TYPE) {
			unknown(UnknownTerm::Kind::Class, static_cast<const ast::Iri &>(*tp.object).value);
		}
	}

	void expression(const ast::Expression *expr) {
		if (expr == nullptr) {
			return;
		}
		switch (expr->kind()) {
		case ast::ExprKind::Exists:
			group(static_cast<const ast::ExistsExpr *>(expr)->pattern.get());
			return;
		case ast::ExprKind::Unary:
			expression(static_cast<const ast::UnaryExpr *>(expr)->operand.get());
			return;
		case ast::ExprKind::Binary: {
			const auto *bin = static_cast<const ast::BinaryExpr *>(expr);
			expression(bin->left.get());
			expression(bin->right.get());
			return;
		}
		case ast::ExprKind::In: {
			const auto *in = static_cast<const ast::InExpr *>(expr);
			expression(in->lhs.get());
			for (const auto &item : in->list) {
				expression(item.get());
			}
			return;
		}
		case ast::ExprKind::FunctionCall:
			for (const auto &arg : static_cast<const ast::FunctionCallExpr *>(expr)->args) {
				expression(arg.get());
			}
			return;
		case ast::ExprKind::BuiltInCall:
			for (const auto &arg : static_cast<const ast::BuiltInCallExpr *>(expr)->args) {
				expression(arg.get());
			}
			return;
		case ast::ExprKind::Aggregate:
			expression(static_cast<const ast::AggregateExpr *>(expr)->arg.get());
			return;
		case ast::ExprKind::Literal:
		case ast::ExprKind::VarRef:
		case ast::ExprKind::IriRef:
			return;
		}
	}

	void group(const ast::GroupGraphPattern *pattern) {
		if (pattern == nullptr) {
			return;
		}
		for (const auto &element : pattern->elements) {
			switch (element->kind()) {
			case ast::ElementKind::BasicGraphPattern:
				for (const auto &tp : static_cast<const ast::BasicGraphPattern &>(*element).triples) {
					triple(tp);
				}
				break;
			case ast::ElementKind::GroupGraphPattern:
				group(static_cast<const ast::GroupGraphPattern *>(element.get()));
				break;
			case ast::ElementKind::UnionGraphPattern:
				for (const auto &branch : static_cast<const ast::UnionGraphPattern &>(*element).branches) {
					group(branch.get());
				}
				break;
			case ast::ElementKind::OptionalGraphPattern:
				group(static_cast<const ast::OptionalGraphPattern &>(*element).pattern.get());
				break;
			case ast::ElementKind::MinusGraphPattern:
				group(static_cast<const ast::MinusGraphPattern &>(*element).pattern.get());
				break;
			case ast::ElementKind::GraphGraphPattern:
				group(static_cast<const ast::GraphGraphPattern &>(*element).pattern.get());
				break;
			case ast::ElementKind::Filter:
				expression(static_cast<const ast::Filter &>(*element).constraint.get());
				break;
			case ast::ElementKind::Bind:
				expression(static_cast<const ast::Bind &>(*element).expr.get());
				break;
			case ast::ElementKind::SubSelect:
				query(*static_cast<const ast::SubSelectElement &>(*element).query);
				break;
			case ast::ElementKind::ServiceGraphPattern:
			case ast::ElementKind::InlineData:
				break;
			}
		}
	}

	void query(const ast::Query &q) {
		for (const auto &item : q.selectItems) {
			expression(item.expr.get());
		}
		group(q.where.get());
		for (const auto &having : q.solutionModifier.having) {
			expression(having.get());
		}
	}
};

// --- Suggestions --------------------------------------------------------------

std::size_t editDistance(const std::string &a, const std::string &b) {
	std::vector<std::size_t> prev(b.size() + 1);
	std::vector<std::size_t> cur(b.size() + 1);
	for (std::size_t j = 0; j <= b.size(); ++j) {
		prev[j] = j;
	}
	for (std::size_t i = 1; i <= a.size(); ++i) {
		cur[0] = i;
		for (std::size_t j = 1; j <= b.size(); ++j) {
			const std::size_t substitution = prev[j - 1] + (a[i - 1] == b[j - 1] ? 0 : 1);
			cur[j] = std::min({prev[j] + 1, cur[j - 1] + 1, substitution});
		}
		std::swap(prev, cur);
	}
	return prev[b.size()];
}

/// The part after the last '#' or '/', which is what people misspell.
std::string localName(const std::string &iri) {
	const std::size_t cut = iri.find_last_of("#/");
	return cut == std::string::npos ? iri : iri.substr(cut + 1);
}

std::string closest(const std::string &iri, const std::set<std::string> &known) {
	std::string best;
	std::size_t bestDistance = 0;
	for (const std::string &candidate : known) {
		const std::size_t distance = editDistance(iri, candidate);
		if (best.empty() || distance < bestDistance) {
			best = candidate;
			bestDistance = distance;
		}
	}
	// Only offer a suggestion that looks like a typo, not any IRI at all.
	const std::size_t limit = std::max<std::size_t>(2, localName(iri).size() / 3);
	return (!best.empty() && bestDistance <= limit) ? best : std::string();
}

} // namespace

MappingVocabulary collectVocabulary(const r2rml::R2RMLMapping &mapping) {
	MappingVocabulary vocabulary;
	for (const auto &triplesMap : mapping.triplesMaps) {
		if (triplesMap->subjectMap) {
			vocabulary.classes.insert(triplesMap->subjectMap->classIRIs.begin(),
			                          triplesMap->subjectMap->classIRIs.end());
		}
		for (const auto &pom : triplesMap->predicateObjectMaps) {
			for (const auto &predicateMap : pom->predicateMaps) {
				const rdf::Term *predicate = constantIri(*predicateMap);
				if (predicate == nullptr) {
					// Any predicate - rdf:type included - can come out of this map.
					vocabulary.openProperties = true;
					vocabulary.openClasses = true;
					continue;
				}
				vocabulary.properties.insert(predicate->lexical());
				if (predicate->lexical() != rdf::RDF_TYPE) {
					continue;
				}
				for (const auto &objectMap : pom->objectMaps) {
					const rdf::Term *klass = constantIri(*objectMap);
					if (klass == nullptr) {
						vocabulary.openClasses = true;
					} else {
						vocabulary.classes.insert(klass->lexical());
					}
				}
			}
		}
	}
	if (!vocabulary.classes.empty()) {
		vocabulary.properties.insert(rdf::RDF_TYPE); // rr:class produces rdf:type triples
	}
	return vocabulary;
}

std::vector<UnknownTerm> findUnknownTerms(const sparql::ast::Query &query, const MappingVocabulary &vocabulary) {
	Walker walker {vocabulary, {}, {}};
	walker.query(query); // a trailing VALUES clause binds variables only: nothing to check there
	for (UnknownTerm &term : walker.found) {
		term.suggestion =
		    closest(term.iri, term.kind == UnknownTerm::Kind::Class ? vocabulary.classes : vocabulary.properties);
	}
	return walker.found;
}

void checkVocabulary(const sparql::ast::Query &query, const r2rml::R2RMLMapping &mapping) {
	const std::vector<UnknownTerm> unknown = findUnknownTerms(query, collectVocabulary(mapping));
	if (unknown.empty()) {
		return;
	}
	std::string message = "the query uses ";
	for (std::size_t i = 0; i < unknown.size(); ++i) {
		const UnknownTerm &term = unknown[i];
		if (i > 0) {
			message += "; ";
		}
		message += (term.kind == UnknownTerm::Kind::Class ? "class <" : "property <") + term.iri + ">";
		if (!term.suggestion.empty()) {
			message += " (did you mean <" + term.suggestion + ">?)";
		}
	}
	message += unknown.size() == 1 ? ", which no map in the mapping produces, so a pattern using it can never match"
	                               : ", which no map in the mapping produces, so patterns using them can never match";
	throw TranslationError(message);
}

} // namespace sparql2sql

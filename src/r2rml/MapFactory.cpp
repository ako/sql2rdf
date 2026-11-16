#include "r2rml/MapFactory.h"

#include "ConcreteMaps.h"
#include "r2rml/ColumnTermMap.h"
#include "r2rml/ConstantTermMap.h"
#include "r2rml/TemplateTermMap.h"

namespace r2rml {

namespace {

void copyTermMapFields(const TermMap &from, TermMap &to) {
	to.termType = from.termType;
	if (from.languageTag) {
		to.languageTag = std::make_unique<std::string>(*from.languageTag);
	}
	if (from.datatypeIRI) {
		to.datatypeIRI = std::make_unique<std::string>(*from.datatypeIRI);
	}
	if (from.inverseExpression) {
		to.inverseExpression = std::make_unique<std::string>(*from.inverseExpression);
	}
}

} // namespace

std::unique_ptr<TermMap> cloneTermMap(const TermMap &map) {
	std::unique_ptr<TermMap> copy;
	if (const auto *c = dynamic_cast<const ConstantTermMap *>(&map)) {
		copy = std::make_unique<ConstantTermMap>(c->constantValue);
	} else if (const auto *col = dynamic_cast<const ColumnTermMap *>(&map)) {
		copy = std::make_unique<ColumnTermMap>(col->columnName);
	} else if (const auto *t = dynamic_cast<const TemplateTermMap *>(&map)) {
		copy = std::make_unique<TemplateTermMap>(t->templateString);
	} else {
		return nullptr;
	}
	copyTermMapFields(map, *copy);
	return copy;
}

std::unique_ptr<SubjectMap> makeSubjectMap(std::unique_ptr<TermMap> value) {
	auto sm = std::make_unique<ConcreteSubjectMap>();
	sm->termType = value ? value->termType : TermType::IRI;
	sm->valueMap = std::move(value);
	return sm;
}

std::unique_ptr<GraphMap> cloneGraphMap(const GraphMap &map) {
	const TermMap *value = map.valueTermMap();
	if (!value) {
		return nullptr;
	}
	auto copy = cloneTermMap(*value);
	if (!copy) {
		return nullptr;
	}
	auto gm = std::make_unique<ConcreteGraphMap>();
	copyTermMapFields(map, *gm);
	gm->valueMap = std::move(copy);
	return gm;
}

std::unique_ptr<ReferencingObjectMap> makeReferencingObjectMap(TriplesMap *parent,
                                                               std::vector<JoinCondition> joinConditions) {
	auto rom = std::make_unique<ConcreteReferencingObjectMap>();
	rom->parentTriplesMap = parent;
	rom->joinConditions = std::move(joinConditions);
	return rom;
}

} // namespace r2rml

#include "sparql2sql/Ontology.h"

#include <algorithm>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "r2rml/BaseTableOrView.h"
#include "r2rml/ColumnTermMap.h"
#include "r2rml/ConstantTermMap.h"
#include "r2rml/GraphMap.h"
#include "r2rml/MapFactory.h"
#include "r2rml/PredicateObjectMap.h"
#include "r2rml/R2RMLView.h"
#include "r2rml/ReferencingObjectMap.h"
#include "r2rml/TemplateTermMap.h"
#include "r2rml/R2RMLMapping.h"
#include "r2rml/SubjectMap.h"
#include "r2rml/TermMap.h"
#include "r2rml/TriplesMap.h"
#include "rdf/Term.h"
#include "sparql-parser/ast/Expression.h"
#include "sparql-parser/ast/GraphPattern.h"
#include "sparql-parser/ast/Path.h"
#include "sparql-parser/ast/Query.h"
#include "sparql2sql/LogicalTableSource.h"
#include "sparql2sql/TemplateUtil.h"

namespace sparql2sql {

namespace {

const char *const kRdfType = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const char *const kSubClassOf = "http://www.w3.org/2000/01/rdf-schema#subClassOf";
const char *const kSubPropertyOf = "http://www.w3.org/2000/01/rdf-schema#subPropertyOf";
const char *const kEquivalentClass = "http://www.w3.org/2002/07/owl#equivalentClass";
const char *const kEquivalentProperty = "http://www.w3.org/2002/07/owl#equivalentProperty";
const char *const kDomain = "http://www.w3.org/2000/01/rdf-schema#domain";
const char *const kRange = "http://www.w3.org/2000/01/rdf-schema#range";
const char *const kInverseOf = "http://www.w3.org/2002/07/owl#inverseOf";
const char *const kTransitiveProperty = "http://www.w3.org/2002/07/owl#TransitiveProperty";
const char *const kSymmetricProperty = "http://www.w3.org/2002/07/owl#SymmetricProperty";

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

namespace {

// ANSI SQL identifier quoting, the same rule the translator's dialects use for
// table and column names.
std::string quoteIdent(const std::string &identifier) {
	std::string out = "\"";
	for (char c : identifier) {
		out += c;
		if (c == '"') {
			out += '"';
		}
	}
	return out + "\"";
}

// Add to `out` the columns `map` reads. False if it cannot tell (a kind of term
// map other than constant, column or template).
bool columnsOf(const r2rml::TermMap *map, std::set<std::string> &out) {
	if (map == nullptr || dynamic_cast<const r2rml::ConstantTermMap *>(map) != nullptr) {
		return true;
	}
	if (const auto *column = dynamic_cast<const r2rml::ColumnTermMap *>(map)) {
		out.insert(column->columnName);
		return true;
	}
	if (const auto *templ = dynamic_cast<const r2rml::TemplateTermMap *>(map)) {
		for (const auto &c : referencedColumns(parseTemplate(templ->templateString))) {
			out.insert(c);
		}
		return true;
	}
	return false;
}

bool graphColumns(const std::vector<std::unique_ptr<r2rml::GraphMap>> &graphMaps, std::set<std::string> &out) {
	for (const auto &gm : graphMaps) {
		if (gm && !columnsOf(gm->valueTermMap(), out)) {
			return false;
		}
	}
	return true;
}

const r2rml::TermMap *subjectValue(const r2rml::TriplesMap &tm) {
	return tm.subjectMap ? tm.subjectMap->valueTermMap() : nullptr;
}

// The logical table as a FROM item: a quoted table name or a parenthesised query.
std::string sourceSql(const r2rml::LogicalTable &table) {
	if (const auto *base = dynamic_cast<const r2rml::BaseTableOrView *>(&table)) {
		return quoteIdent(base->tableName);
	}
	if (const auto *view = dynamic_cast<const r2rml::R2RMLView *>(&table)) {
		return "(" + stripTrailingSemicolon(view->sqlQuery) + ")";
	}
	return std::string();
}

std::unique_ptr<r2rml::LogicalTable> copyLogicalTable(const r2rml::LogicalTable &table) {
	std::unique_ptr<r2rml::LogicalTable> copy;
	if (const auto *base = dynamic_cast<const r2rml::BaseTableOrView *>(&table)) {
		copy = std::make_unique<r2rml::BaseTableOrView>(base->tableName);
	} else if (const auto *view = dynamic_cast<const r2rml::R2RMLView *>(&table)) {
		auto v = std::make_unique<r2rml::R2RMLView>(view->sqlQuery);
		v->sqlVersions = view->sqlVersions;
		copy = std::move(v);
	} else {
		return nullptr;
	}
	copy->effectiveSqlQuery = table.effectiveSqlQuery;
	return copy;
}

// `table` restricted to the rows where every column in `notNull` is set and
// `extra` (a condition over alias "t", may be empty) holds. The table itself
// when there is nothing to restrict.
std::unique_ptr<r2rml::LogicalTable> filteredTable(const r2rml::LogicalTable &table,
                                                   const std::set<std::string> &notNull, const std::string &extra) {
	if (notNull.empty() && extra.empty()) {
		return copyLogicalTable(table);
	}
	const std::string from = sourceSql(table);
	if (from.empty()) {
		return nullptr;
	}
	std::string where;
	for (const auto &c : notNull) {
		where += (where.empty() ? "" : " AND ") + std::string("\"t\".") + quoteIdent(c) + " IS NOT NULL";
	}
	if (!extra.empty()) {
		where += (where.empty() ? "" : " AND ") + extra;
	}
	return std::make_unique<r2rml::R2RMLView>("SELECT * FROM " + from + " AS \"t\" WHERE " + where);
}

// EXISTS over `other` (alias "o") joined to the filtered table (alias "t"),
// `pairs` being (column of "t", column of "o"), with `otherNotNull` set in "o".
std::string existsJoin(const r2rml::LogicalTable &other, const std::vector<std::pair<std::string, std::string>> &pairs,
                       const std::set<std::string> &otherNotNull) {
	const std::string from = sourceSql(other);
	if (from.empty()) {
		return std::string();
	}
	std::string cond;
	for (const auto &p : pairs) {
		cond += (cond.empty() ? "" : " AND ") + std::string("\"o\".") + quoteIdent(p.second) + " = \"t\"." +
		        quoteIdent(p.first);
	}
	for (const auto &c : otherNotNull) {
		cond += (cond.empty() ? "" : " AND ") + std::string("\"o\".") + quoteIdent(c) + " IS NOT NULL";
	}
	return "EXISTS (SELECT 1 FROM " + from + " AS \"o\"" + (cond.empty() ? "" : " WHERE " + cond) + ")";
}

void appendGraphCopies(const std::vector<std::unique_ptr<r2rml::GraphMap>> &from,
                       std::vector<std::unique_ptr<r2rml::GraphMap>> &to) {
	for (const auto &gm : from) {
		if (gm) {
			if (auto copy = r2rml::cloneGraphMap(*gm)) {
				to.push_back(std::move(copy));
			}
		}
	}
}

// A new triples map over `table` whose subject is a copy of `subject` with
// `classes`, in the graphs of `graphs1` and `graphs2`. Null if a part cannot
// be copied.
std::unique_ptr<r2rml::TriplesMap> classMap(const std::string &id, std::unique_ptr<r2rml::LogicalTable> table,
                                            const r2rml::TermMap &subject, const std::set<std::string> &classes,
                                            const std::vector<std::unique_ptr<r2rml::GraphMap>> &graphs1,
                                            const std::vector<std::unique_ptr<r2rml::GraphMap>> &graphs2) {
	auto value = r2rml::cloneTermMap(subject);
	if (!table || !value || value->termType == r2rml::TermType::Literal) {
		return nullptr;
	}
	auto tm = std::make_unique<r2rml::TriplesMap>();
	tm->id = id;
	tm->logicalTable = std::move(table);
	tm->subjectMap = r2rml::makeSubjectMap(std::move(value));
	tm->subjectMap->classIRIs.assign(classes.begin(), classes.end());
	appendGraphCopies(graphs1, tm->subjectMap->graphMaps);
	appendGraphCopies(graphs2, tm->subjectMap->graphMaps);
	return tm;
}

std::vector<std::string> constantPredicates(const r2rml::PredicateObjectMap &pom) {
	std::vector<std::string> out;
	for (const auto &pm : pom.predicateMaps) {
		const std::string iri = constantIri(pm);
		if (!iri.empty() && iri != kRdfType) {
			out.push_back(iri);
		}
	}
	return out;
}

// Superproperties of every constant predicate, on every predicate-object map.
void saturateProperties(r2rml::R2RMLMapping &mapping, const Ontology &ontology, SaturationResult &result) {
	for (auto &tmPtr : mapping.triplesMaps) {
		if (!tmPtr) {
			continue;
		}
		for (auto &pomPtr : tmPtr->predicateObjectMaps) {
			if (!pomPtr) {
				continue;
			}
			std::set<std::string> supers;
			for (const auto &p : constantPredicates(*pomPtr)) {
				const std::set<std::string> up = ontology.superPropertiesOf(p);
				supers.insert(up.begin(), up.end());
			}
			result.predicatesAdded += addConstantIris(pomPtr->predicateMaps, supers);
		}
	}
}

// Superclasses of every class: rr:class on subject maps, and the objects of an
// `rdf:type` predicate-object map.
void saturateClasses(r2rml::R2RMLMapping &mapping, const Ontology &ontology, SaturationResult &result) {
	for (auto &tmPtr : mapping.triplesMaps) {
		if (!tmPtr) {
			continue;
		}
		r2rml::TriplesMap &tm = *tmPtr;
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
			// Only safe when rdf:type is this map's only predicate: otherwise the
			// added objects would also be produced for the other predicates.
			if (pom.predicateMaps.size() != 1 || constantIri(pom.predicateMaps.front()) != kRdfType) {
				continue;
			}
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

// For each inverse Q of a constant predicate P: a map producing (o Q s) for
// every (s P o) of the first `count` triples maps.
void addInverses(r2rml::R2RMLMapping &mapping, std::size_t count, const Ontology &ontology, SaturationResult &result) {
	std::vector<std::unique_ptr<r2rml::TriplesMap>> added;
	for (std::size_t i = 0; i < count; ++i) {
		if (!mapping.triplesMaps[i] || !mapping.triplesMaps[i]->logicalTable ||
		    !subjectValue(*mapping.triplesMaps[i])) {
			continue;
		}
		r2rml::TriplesMap &tm = *mapping.triplesMaps[i];
		for (const auto &pomPtr : tm.predicateObjectMaps) {
			if (!pomPtr) {
				continue;
			}
			const r2rml::PredicateObjectMap &pom = *pomPtr;
			std::set<std::string> inverses;
			for (const auto &p : constantPredicates(pom)) {
				const std::set<std::string> inv = ontology.inversesOf(p);
				inverses.insert(inv.begin(), inv.end());
			}
			if (inverses.empty()) {
				continue;
			}
			for (const auto &om : pom.objectMaps) {
				if (!om) {
					continue;
				}
				for (const auto &q : inverses) {
					auto inv = std::make_unique<r2rml::TriplesMap>();
					inv->id = tm.id + "#inverse-" + q;
					auto newPom = std::make_unique<r2rml::PredicateObjectMap>();
					newPom->predicateMaps.push_back(constantIriMap(q));
					if (const auto *rom = dynamic_cast<const r2rml::ReferencingObjectMap *>(om.get())) {
						// The join reversed: run over the parent's rows and refer back to this map.
						r2rml::TriplesMap *parent = rom->parentTriplesMap;
						std::set<std::string> childGraphColumns;
						if (!parent || !parent->logicalTable || !subjectValue(*parent) ||
						    !graphColumns(tm.subjectMap->graphMaps, childGraphColumns) ||
						    !graphColumns(pom.graphMaps, childGraphColumns) || !childGraphColumns.empty()) {
							continue; // the graph would have to be read from the child's columns
						}
						std::vector<r2rml::JoinCondition> swapped;
						swapped.reserve(rom->joinConditions.size());
						for (const auto &jc : rom->joinConditions) {
							swapped.emplace_back(jc.parentColumn, jc.childColumn);
						}
						inv->logicalTable = copyLogicalTable(*parent->logicalTable);
						auto value = r2rml::cloneTermMap(*subjectValue(*parent));
						if (!inv->logicalTable || !value) {
							continue;
						}
						inv->subjectMap = r2rml::makeSubjectMap(std::move(value));
						newPom->objectMaps.push_back(r2rml::makeReferencingObjectMap(&tm, std::move(swapped)));
					} else {
						auto subject = r2rml::cloneTermMap(*om);
						auto object = r2rml::cloneTermMap(*subjectValue(tm));
						if (!subject || !object || subject->termType == r2rml::TermType::Literal) {
							continue; // a literal cannot be a subject
						}
						inv->logicalTable = copyLogicalTable(*tm.logicalTable);
						if (!inv->logicalTable) {
							continue;
						}
						inv->subjectMap = r2rml::makeSubjectMap(std::move(subject));
						newPom->objectMaps.push_back(std::move(object));
					}
					appendGraphCopies(tm.subjectMap->graphMaps, newPom->graphMaps);
					appendGraphCopies(pom.graphMaps, newPom->graphMaps);
					inv->predicateObjectMaps.push_back(std::move(newPom));
					added.push_back(std::move(inv));
				}
			}
		}
	}
	result.triplesMapsAdded += added.size();
	for (auto &tm : added) {
		mapping.triplesMaps.push_back(std::move(tm));
	}
}

// rdfs:domain and rdfs:range classes for the predicates of the first `count`
// triples maps.
void addDomainsAndRanges(r2rml::R2RMLMapping &mapping, std::size_t count, const Ontology &ontology,
                         SaturationResult &result) {
	std::vector<std::unique_ptr<r2rml::TriplesMap>> added;
	for (std::size_t i = 0; i < count; ++i) {
		if (!mapping.triplesMaps[i] || !mapping.triplesMaps[i]->logicalTable ||
		    !subjectValue(*mapping.triplesMaps[i])) {
			continue;
		}
		r2rml::TriplesMap &tm = *mapping.triplesMaps[i];
		const r2rml::TermMap &subject = *subjectValue(tm);
		std::set<std::string> subjectColumns;
		std::set<std::string> subjectGraphColumns;
		if (!columnsOf(&subject, subjectColumns) || !graphColumns(tm.subjectMap->graphMaps, subjectGraphColumns)) {
			continue;
		}
		for (const auto &pomPtr : tm.predicateObjectMaps) {
			if (!pomPtr) {
				continue;
			}
			const r2rml::PredicateObjectMap &pom = *pomPtr;
			std::set<std::string> domains;
			std::set<std::string> ranges;
			for (const auto &p : constantPredicates(pom)) {
				const std::set<std::string> d = ontology.domainsOf(p);
				const std::set<std::string> r = ontology.rangesOf(p);
				domains.insert(d.begin(), d.end());
				ranges.insert(r.begin(), r.end());
			}
			std::set<std::string> pomGraphColumns;
			if ((domains.empty() && ranges.empty()) || !graphColumns(pom.graphMaps, pomGraphColumns)) {
				continue;
			}
			// The columns that must be set for this map's triples to exist,
			// besides the object's: the subject's and the graphs'.
			std::set<std::string> tripleColumns = subjectColumns;
			tripleColumns.insert(subjectGraphColumns.begin(), subjectGraphColumns.end());
			tripleColumns.insert(pomGraphColumns.begin(), pomGraphColumns.end());

			// Domain: when some object is produced whenever the subject is, the
			// class goes on the subject map itself.
			bool domainOnSubject = false;
			if (!domains.empty() && pom.graphMaps.empty()) {
				for (const auto &om : pom.objectMaps) {
					std::set<std::string> cols;
					if (om && dynamic_cast<const r2rml::ReferencingObjectMap *>(om.get()) == nullptr &&
					    columnsOf(om.get(), cols) &&
					    std::includes(subjectColumns.begin(), subjectColumns.end(), cols.begin(), cols.end())) {
						domainOnSubject = true;
					}
				}
			}
			if (domainOnSubject) {
				std::vector<std::string> &classes = tm.subjectMap->classIRIs;
				std::set<std::string> present(classes.begin(), classes.end());
				for (const auto &d : domains) {
					if (present.insert(d).second) {
						classes.push_back(d);
						++result.classesAdded;
					}
				}
			}

			for (const auto &om : pom.objectMaps) {
				if (!om) {
					continue;
				}
				const auto *rom = dynamic_cast<const r2rml::ReferencingObjectMap *>(om.get());
				if (rom) {
					r2rml::TriplesMap *parent = rom->parentTriplesMap;
					if (!parent || !parent->logicalTable || !subjectValue(*parent)) {
						continue;
					}
					std::set<std::string> parentColumns;
					if (!columnsOf(subjectValue(*parent), parentColumns)) {
						continue;
					}
					if (!domains.empty() && !domainOnSubject) {
						// Child rows whose join finds a parent row (with no join
						// condition, parent and child are the same row).
						std::set<std::string> notNull = tripleColumns;
						std::string extra;
						if (rom->joinConditions.empty()) {
							notNull.insert(parentColumns.begin(), parentColumns.end());
						} else {
							std::vector<std::pair<std::string, std::string>> pairs;
							pairs.reserve(rom->joinConditions.size());
							for (const auto &jc : rom->joinConditions) {
								pairs.emplace_back(jc.childColumn, jc.parentColumn);
							}
							extra = existsJoin(*parent->logicalTable, pairs, parentColumns);
						}
						if (auto m = classMap(tm.id + "#domain", filteredTable(*tm.logicalTable, notNull, extra),
						                      subject, domains, tm.subjectMap->graphMaps, pom.graphMaps)) {
							added.push_back(std::move(m));
						}
					}
					if (!ranges.empty()) {
						if (!subjectGraphColumns.empty() || !pomGraphColumns.empty()) {
							continue; // the graph would have to be read from the child's columns
						}
						std::set<std::string> notNull;
						std::string extra;
						if (rom->joinConditions.empty()) {
							notNull = subjectColumns; // same row
						} else {
							std::vector<std::pair<std::string, std::string>> pairs;
							pairs.reserve(rom->joinConditions.size());
							for (const auto &jc : rom->joinConditions) {
								pairs.emplace_back(jc.parentColumn, jc.childColumn);
							}
							extra = existsJoin(*tm.logicalTable, pairs, subjectColumns);
						}
						if (auto m =
						        classMap(tm.id + "#range", filteredTable(*parent->logicalTable, notNull, extra),
						                 *subjectValue(*parent), ranges, tm.subjectMap->graphMaps, pom.graphMaps)) {
							added.push_back(std::move(m));
						}
					}
					continue;
				}
				std::set<std::string> objectColumns;
				if (!columnsOf(om.get(), objectColumns)) {
					continue;
				}
				if (!domains.empty() && !domainOnSubject) {
					std::set<std::string> notNull = objectColumns;
					notNull.insert(subjectGraphColumns.begin(), subjectGraphColumns.end());
					notNull.insert(pomGraphColumns.begin(), pomGraphColumns.end());
					for (const auto &c : subjectColumns) {
						notNull.erase(c); // set wherever the subject is
					}
					if (auto m = classMap(tm.id + "#domain", filteredTable(*tm.logicalTable, notNull, ""), subject,
					                      domains, tm.subjectMap->graphMaps, pom.graphMaps)) {
						added.push_back(std::move(m));
					}
				}
				if (!ranges.empty() && om->termType != r2rml::TermType::Literal) {
					std::set<std::string> notNull = tripleColumns;
					for (const auto &c : objectColumns) {
						notNull.erase(c); // set wherever the new subject is
					}
					if (auto m = classMap(tm.id + "#range", filteredTable(*tm.logicalTable, notNull, ""), *om, ranges,
					                      tm.subjectMap->graphMaps, pom.graphMaps)) {
						added.push_back(std::move(m));
					}
				}
			}
		}
	}
	result.triplesMapsAdded += added.size();
	for (auto &tm : added) {
		mapping.triplesMaps.push_back(std::move(tm));
	}
}

using sparql::ast::PathKind;
using sparql::ast::PropertyPathExpr;

void rewriteGroup(sparql::ast::GroupGraphPattern *group, const Ontology &ontology, std::size_t &count);
void rewriteQuery(sparql::ast::Query &query, const Ontology &ontology, std::size_t &count);

void rewritePath(std::unique_ptr<PropertyPathExpr> &path, const Ontology &ontology, bool underClosure,
                 std::size_t &count) {
	if (!path) {
		return;
	}
	switch (path->kind()) {
	case PathKind::Predicate: {
		auto *step = static_cast<sparql::ast::PredicatePath *>(path.get());
		if (!underClosure && step->iri && ontology.isTransitive(step->iri->value)) {
			path = std::make_unique<sparql::ast::OneOrMorePath>(std::move(path));
			++count;
		}
		return;
	}
	case PathKind::Inverse:
		rewritePath(static_cast<sparql::ast::InversePath *>(path.get())->child, ontology, underClosure, count);
		return;
	case PathKind::Sequence: {
		auto *seq = static_cast<sparql::ast::SequencePath *>(path.get());
		rewritePath(seq->left, ontology, underClosure, count);
		rewritePath(seq->right, ontology, underClosure, count);
		return;
	}
	case PathKind::Alternative: {
		auto *alt = static_cast<sparql::ast::AlternativePath *>(path.get());
		rewritePath(alt->left, ontology, underClosure, count);
		rewritePath(alt->right, ontology, underClosure, count);
		return;
	}
	case PathKind::ZeroOrOne:
		rewritePath(static_cast<sparql::ast::ZeroOrOnePath *>(path.get())->child, ontology, underClosure, count);
		return;
	case PathKind::ZeroOrMore:
		rewritePath(static_cast<sparql::ast::ZeroOrMorePath *>(path.get())->child, ontology, true, count);
		return;
	case PathKind::OneOrMore:
		rewritePath(static_cast<sparql::ast::OneOrMorePath *>(path.get())->child, ontology, true, count);
		return;
	case PathKind::Variable:
	case PathKind::NegatedPropertySet:
		return;
	}
}

void rewriteExpression(sparql::ast::Expression *expr, const Ontology &ontology, std::size_t &count) {
	using sparql::ast::ExprKind;
	if (!expr) {
		return;
	}
	switch (expr->kind()) {
	case ExprKind::Exists:
		rewriteGroup(static_cast<sparql::ast::ExistsExpr *>(expr)->pattern.get(), ontology, count);
		return;
	case ExprKind::Unary:
		rewriteExpression(static_cast<sparql::ast::UnaryExpr *>(expr)->operand.get(), ontology, count);
		return;
	case ExprKind::Binary: {
		auto *b = static_cast<sparql::ast::BinaryExpr *>(expr);
		rewriteExpression(b->left.get(), ontology, count);
		rewriteExpression(b->right.get(), ontology, count);
		return;
	}
	case ExprKind::In: {
		auto *in = static_cast<sparql::ast::InExpr *>(expr);
		rewriteExpression(in->lhs.get(), ontology, count);
		for (auto &e : in->list) {
			rewriteExpression(e.get(), ontology, count);
		}
		return;
	}
	case ExprKind::FunctionCall:
		for (auto &e : static_cast<sparql::ast::FunctionCallExpr *>(expr)->args) {
			rewriteExpression(e.get(), ontology, count);
		}
		return;
	case ExprKind::BuiltInCall:
		for (auto &e : static_cast<sparql::ast::BuiltInCallExpr *>(expr)->args) {
			rewriteExpression(e.get(), ontology, count);
		}
		return;
	case ExprKind::Aggregate:
		rewriteExpression(static_cast<sparql::ast::AggregateExpr *>(expr)->arg.get(), ontology, count);
		return;
	case ExprKind::Literal:
	case ExprKind::VarRef:
	case ExprKind::IriRef:
		return;
	}
}

void rewriteGroup(sparql::ast::GroupGraphPattern *group, const Ontology &ontology, std::size_t &count) {
	using sparql::ast::ElementKind;
	if (!group) {
		return;
	}
	for (auto &element : group->elements) {
		if (!element) {
			continue;
		}
		switch (element->kind()) {
		case ElementKind::BasicGraphPattern:
			for (auto &triple : static_cast<sparql::ast::BasicGraphPattern *>(element.get())->triples) {
				rewritePath(triple.predicate, ontology, false, count);
			}
			break;
		case ElementKind::GroupGraphPattern:
			rewriteGroup(static_cast<sparql::ast::GroupGraphPattern *>(element.get()), ontology, count);
			break;
		case ElementKind::UnionGraphPattern:
			for (auto &branch : static_cast<sparql::ast::UnionGraphPattern *>(element.get())->branches) {
				rewriteGroup(branch.get(), ontology, count);
			}
			break;
		case ElementKind::OptionalGraphPattern:
			rewriteGroup(static_cast<sparql::ast::OptionalGraphPattern *>(element.get())->pattern.get(), ontology,
			             count);
			break;
		case ElementKind::MinusGraphPattern:
			rewriteGroup(static_cast<sparql::ast::MinusGraphPattern *>(element.get())->pattern.get(), ontology, count);
			break;
		case ElementKind::GraphGraphPattern:
			rewriteGroup(static_cast<sparql::ast::GraphGraphPattern *>(element.get())->pattern.get(), ontology, count);
			break;
		case ElementKind::ServiceGraphPattern:
			break; // answered elsewhere
		case ElementKind::Filter:
			rewriteExpression(static_cast<sparql::ast::Filter *>(element.get())->constraint.get(), ontology, count);
			break;
		case ElementKind::Bind:
			rewriteExpression(static_cast<sparql::ast::Bind *>(element.get())->expr.get(), ontology, count);
			break;
		case ElementKind::InlineData:
			break;
		case ElementKind::SubSelect: {
			auto *sub = static_cast<sparql::ast::SubSelectElement *>(element.get());
			if (sub->query) {
				rewriteQuery(*sub->query, ontology, count);
			}
			break;
		}
		}
	}
}

void rewriteQuery(sparql::ast::Query &query, const Ontology &ontology, std::size_t &count) {
	rewriteGroup(query.where.get(), ontology, count);
	for (auto &item : query.selectItems) {
		rewriteExpression(item.expr.get(), ontology, count);
	}
	for (auto &e : query.solutionModifier.having) {
		rewriteExpression(e.get(), ontology, count);
	}
	for (auto &o : query.solutionModifier.orderBy) {
		rewriteExpression(o.expr.get(), ontology, count);
	}
}

} // namespace

bool Ontology::addTriple(const std::string &subject, const std::string &predicate, const std::string &object) {
	if (isBlankNode(subject) || isBlankNode(object)) {
		return false;
	}
	if (predicate == kInverseOf) {
		inverseOf_[subject].insert(object);
		inverseOf_[object].insert(subject);
	} else if (predicate == kRdfType && object == kSymmetricProperty) {
		inverseOf_[subject].insert(subject);
	} else if (predicate == kRdfType && object == kTransitiveProperty) {
		transitive_.insert(subject);
	} else if (subject == object) {
		return false;
	} else if (predicate == kSubClassOf) {
		subClassOf_[subject].insert(object);
	} else if (predicate == kEquivalentClass) {
		subClassOf_[subject].insert(object);
		subClassOf_[object].insert(subject);
	} else if (predicate == kSubPropertyOf) {
		subPropertyOf_[subject].insert(object);
	} else if (predicate == kEquivalentProperty) {
		subPropertyOf_[subject].insert(object);
		subPropertyOf_[object].insert(subject);
	} else if (predicate == kDomain) {
		domain_[subject].insert(object);
	} else if (predicate == kRange) {
		range_[subject].insert(object);
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

namespace {
std::set<std::string> lookup(const std::map<std::string, std::set<std::string>> &m, const std::string &key) {
	auto it = m.find(key);
	return it == m.end() ? std::set<std::string>() : it->second;
}
} // namespace

std::set<std::string> Ontology::domainsOf(const std::string &property) const {
	return lookup(domain_, property);
}

std::set<std::string> Ontology::rangesOf(const std::string &property) const {
	return lookup(range_, property);
}

std::set<std::string> Ontology::inversesOf(const std::string &property) const {
	return lookup(inverseOf_, property);
}

bool Ontology::isTransitive(const std::string &property) const {
	if (transitive_.count(property)) {
		return true;
	}
	for (const auto &q : inversesOf(property)) {
		if (transitive_.count(q)) {
			return true;
		}
	}
	// An equivalent property: each a superproperty of the other.
	for (const auto &q : superPropertiesOf(property)) {
		if (transitive_.count(q) && superPropertiesOf(q).count(property)) {
			return true;
		}
	}
	return false;
}

SaturationResult saturateMapping(r2rml::R2RMLMapping &mapping, const Ontology &ontology) {
	SaturationResult result;
	if (ontology.axiomCount() == 0) {
		return result;
	}
	saturateProperties(mapping, ontology, result);
	addInverses(mapping, mapping.triplesMaps.size(), ontology, result);
	saturateProperties(mapping, ontology, result);
	addDomainsAndRanges(mapping, mapping.triplesMaps.size(), ontology, result);
	saturateClasses(mapping, ontology, result);
	return result;
}

std::size_t applyTransitiveProperties(sparql::ast::Query &query, const Ontology &ontology) {
	std::size_t count = 0;
	rewriteQuery(query, ontology, count);
	return count;
}

} // namespace sparql2sql

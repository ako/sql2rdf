#pragma once

#include "r2rml/JoinCondition.h"

#include <memory>
#include <vector>

namespace r2rml {

class GraphMap;
class ReferencingObjectMap;
class SubjectMap;
class TermMap;
class TriplesMap;

/// Build and copy the parts of a mapping after it has been parsed, for code
/// that derives new maps from existing ones (mapping saturation in
/// sparql2sql/Ontology.h). The concrete subject, graph and referencing object
/// map classes are private to the library; these functions are the way in.

/// A copy of a constant, column or template term map, including its term
/// type, datatype, language tag and inverse expression. Returns nullptr for
/// any other kind (a referencing object map, or a subject or graph map: copy
/// those with the functions below).
std::unique_ptr<TermMap> cloneTermMap(const TermMap &map);

/// A subject map that produces the terms of `value` (an IRI or blank node
/// term map), with no classes and no graph maps.
std::unique_ptr<SubjectMap> makeSubjectMap(std::unique_ptr<TermMap> value);

/// A copy of a graph map. Returns nullptr when its value map cannot be copied.
std::unique_ptr<GraphMap> cloneGraphMap(const GraphMap &map);

/// A referencing object map joining to `parent` on `joinConditions`
/// (child column = parent column).
std::unique_ptr<ReferencingObjectMap> makeReferencingObjectMap(TriplesMap *parent,
                                                               std::vector<JoinCondition> joinConditions);

} // namespace r2rml

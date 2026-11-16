#pragma once
// Concrete subclasses of the abstract SubjectMap, GraphMap and
// ReferencingObjectMap. Private to the r2rml library: R2RMLParser builds them
// while parsing, MapFactory (include/r2rml/MapFactory.h) for code that builds
// or copies maps afterwards.

#include "r2rml/GraphMap.h"
#include "r2rml/ReferencingObjectMap.h"
#include "r2rml/SQLRow.h"
#include "r2rml/SubjectMap.h"

#include <memory>
#include <ostream>

namespace r2rml {

// ---------------------------------------------------------------------------
// ConcreteSubjectMap – private to this translation unit.
//
// SubjectMap inherits TermMap's pure-virtual generateRDFTerm without
// overriding it, making SubjectMap abstract.  ConcreteSubjectMap adds an
// inner TermMap that supplies the value-generation strategy.
// ---------------------------------------------------------------------------
class ConcreteSubjectMap : public SubjectMap {
public:
	std::unique_ptr<TermMap> valueMap;

	void generateRDFTerm(const SQLRow &row, rdf::Term &out) const override {
		if (valueMap) {
			valueMap->generateRDFTerm(row, out);
			return;
		}
		out.clear();
	}

	const TermMap *valueTermMap() const override {
		return valueMap.get();
	}

	std::ostream &print(std::ostream &os) const override {
		os << "SubjectMap {";
		if (valueMap) {
			os << " valueMap=" << *valueMap;
		}
		if (!classIRIs.empty()) {
			os << " classes=[";
			for (std::size_t i = 0; i < classIRIs.size(); ++i) {
				if (i) {
					os << ", ";
				}
				os << classIRIs[i];
			}
			os << "]";
		}
		if (!graphMaps.empty()) {
			os << " graphMaps=[";
			for (std::size_t i = 0; i < graphMaps.size(); ++i) {
				if (i) {
					os << ", ";
				}
				if (graphMaps[i]) {
					os << *graphMaps[i];
				}
			}
			os << "]";
		}
		os << " }";
		return os;
	}
};

// ---------------------------------------------------------------------------
// ConcreteGraphMap – private to this translation unit.
//
// GraphMap inherits TermMap's pure-virtual generateRDFTerm without
// overriding it, making it abstract; ConcreteGraphMap adds an inner TermMap
// (built via ParseContext::buildTermMap, so it shares the same
// column/template/constant machinery as predicate/object maps) that
// supplies the value-generation strategy.
// ---------------------------------------------------------------------------
class ConcreteGraphMap : public GraphMap {
public:
	std::unique_ptr<TermMap> valueMap;

	void generateRDFTerm(const SQLRow &row, rdf::Term &out) const override {
		if (valueMap) {
			valueMap->generateRDFTerm(row, out);
			return;
		}
		out.clear();
	}

	const TermMap *valueTermMap() const override {
		return valueMap.get();
	}

	std::ostream &print(std::ostream &os) const override {
		os << "GraphMap {";
		if (valueMap) {
			os << " valueMap=" << *valueMap;
		}
		os << " }";
		return os;
	}
};

// ---------------------------------------------------------------------------
// ConcreteReferencingObjectMap – private to this translation unit.
//
// ReferencingObjectMap only declares the two-row generateRDFTerm variant, so
// it remains abstract with respect to TermMap's single-row pure virtual.
// This wrapper satisfies the interface; actual resolution requires both rows.
// ---------------------------------------------------------------------------
class ConcreteReferencingObjectMap : public ReferencingObjectMap {
public:
	void generateRDFTerm(const SQLRow & /*row*/, rdf::Term &out) const override {
		out.clear(); // use the two-row overload for actual generation
	}
};

} // namespace r2rml

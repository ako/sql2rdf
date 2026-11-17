#include "sparql2sql/ir/SqlRenderer.h"

#include <algorithm>
#include <cctype>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "sparql2sql/ExpressionTranslator.h"
#include "sparql2sql/SqlDialect.h"
#include "sparql2sql/TagSql.h"
#include "sparql2sql/TemplateUtil.h"
#include "sparql2sql/TranslationError.h"
#include "sparql2sql/TypeCatalog.h"
#include "sparql2sql/ir/NativeKey.h"
#include "sparql2sql/ir/RelNode.h"

namespace sparql2sql {

namespace {

std::string renderNode(const RelNode &node, TranslationContext &ctx);
using ExtraProjections = std::vector<std::pair<std::string, std::string>>;
std::string renderTransitiveClosure(const TransitiveClosureNode &tc, TranslationContext &ctx,
                                    const ExtraProjections *extra);
std::size_t closureArmCount(const TransitiveClosureNode &tc);
// The start set of a seeded pairs closure (see renderJoin): a CTE holding the
// join partner's values for one endpoint, as IRI text and, when the partner
// column is a template, as its raw placeholder columns too.
struct ClosureSeed {
	std::string cte;
	std::string iriCol;               // mangled endpoint variable in `cte`
	std::vector<std::string> keyCols; // raw placeholder columns in `cte`, may be empty
	const ColumnInfo *col = nullptr;  // the partner's column for the endpoint
	bool onFrom = true;               // seeds the subject end (else the object end)
};

std::string renderSplitClosure(const TransitiveClosureNode &tc, TranslationContext &ctx, const ClosureSeed *seed,
                               const ColumnInfo *outCol = nullptr, std::size_t *outKeys = nullptr);

// A TranslatedPattern carrying a node's schema *description* but no SQL -
// enough for translateExpression's in-scope/optionality checks and its static
// term-dimension lookups (it never reads scope.sql).
TranslatedPattern scopeOf(const RelNode &node) {
	TranslatedPattern tp;
	fillScopeFromSchema(tp, node.schema());
	return tp;
}

// The SQL expression producing `col`'s runtime type tag from within the owning
// node's own FROM scope - i.e. the constant the producer minted.
//
// Throws rather than substituting NULL when there is no such constant, because
// NULL is this representation's spelling of *unbound*: emitting one for a term
// that is bound would make isLITERAL() answer "error" for a perfectly good
// literal. The only shapes that reach here without a constant are a transitive
// closure whose step relation's endpoint term maps disagree, and a Raw leaf
// whose producer had no constant either - both of which threw at translation
// time before tags existed too, so this is not a new refusal, only a
// better-explained one.
std::string producedTag(const ColumnInfo &col, const char *nodeDescription) {
	if (col.tagExpr.empty()) {
		throw TranslationError(
		    std::string("unsupported: the RDF term dimension of ?") + col.var + " is needed at run time, but " +
		    nodeDescription +
		    " cannot supply one - its contributing term maps "
		    "disagree and it is not re-rendered late enough to carry a per-row tag column. Declare a "
		    "consistent rr:datatype/rr:termType across the contributing term maps, or avoid asking "
		    "about this variable's type.");
	}
	return col.tagExpr;
}

// ", <tag> AS d_<var>" for one transitive-closure endpoint column, or "" when
// no tag is wanted.
//
// The closure's own recursive CTE deliberately carries only the endpoint node
// text: threading a tag column through it would change what the terminating
// UNION deduplicates on. That is sound because the step relation's endpoint term
// maps determine the tag statically in every mapping shape that reaches here -
// and where they disagree, producedTag says so rather than guessing.
std::string closureTagProjection(const ColumnInfo &col, TranslationContext &ctx) {
	if (!ctx.needsTag(col.var)) {
		return std::string();
	}
	return ", " + producedTag(col, "a transitive-closure (`+`/`*`) path") + " AS " +
	       mangleVarTag(col.var, ctx.dialect());
}

// Render one equi-key comparison across a derived-table boundary (where only
// the mangled `v_<name>` columns are in scope, so no native-column rewrite is
// possible here - see nativeKeyProjections).
//
// A null-tolerant key only needs the IS NULL disjunct for the side that can
// actually be NULL, and needs neither when both sides are guaranteed non-NULL.
// This matters far more than the redundant text suggests: an OR'd comparison is
// a non-equi predicate, which stops the engine from decorrelating a
// correlated/anti-join into a hash semi-join and leaves it a nested loop over
// the inner relation.
std::string keyComparison(const EquiKey &k, const std::string &lcol, const std::string &rcol) {
	std::string cond;
	cond.reserve(128);
	cond = lcol + " = " + rcol;
	if (!k.nullSafe) {
		return cond;
	}
	if (!k.leftCol.nonNull) {
		cond += " OR " + lcol + " IS NULL";
	}
	if (!k.rightCol.nonNull) {
		cond += " OR " + rcol + " IS NULL";
	}
	if (cond.find(" OR ") == std::string::npos) {
		return cond; // Flagged null-safe, but provably neither side is nullable.
	}
	return "(" + cond + ")";
}

// The tag-column half of one equi-key comparison, or "" when there is nothing
// to compare.
//
// An equi-join on a shared variable is RDF *term* equality, so two candidate
// sources whose dimensions can differ must compare tags as well as lexical
// text - the un-merged counterpart of Optimizer's termDimensionEquality, and
// gated on exactly the conditions markJoinKeys used when it decided to demand
// the d_<var> columns this reads:
//
//  - both sides can supply a runtime tag and those tags are not provably
//    identical (tagsMayDiffer - either differing hoisted constants, or either
//    side a heterogeneous union's tagProjectable column), and the two
//    annotations can actually conflict (dimensionsMayConflict). Equal hoisted
//    tags are trivially equal at run time too, so a well-typed mapping keeps
//    generating the SQL it generated before tags existed; a side with no
//    runtime tag at all means the mapping does not determine the dimension,
//    and there is nothing better than today's lexical-only comparison (never a
//    synthesised default).
//  - a null-tolerant key is vacuous when either side is unbound, so the
//    dimension check is guarded with the same IS NULL disjunct on both value
//    columns; when both sides are actually bound it still enforces RDF term
//    equality, matching the merged path's guard in mergeInner.
std::string keyTagComparison(const EquiKey &k, TranslationContext &ctx, const std::string &leftAlias,
                             const std::string &rightAlias, const std::string &lcol, const std::string &rcol) {
	if (!ctx.needsTag(k.var)) {
		return std::string();
	}
	if (!tagsMayDiffer(k.leftCol, k.rightCol)) {
		return std::string();
	}
	if (!dimensionsMayConflict(k.leftCol.term, k.rightCol.term)) {
		return std::string();
	}
	const SqlDialect &dialect = ctx.dialect();
	std::string tagCond = tagDimensionsCompatible(leftAlias + "." + mangleVarTag(k.var, dialect),
	                                              rightAlias + "." + mangleVarTag(k.var, dialect), dialect);
	if (!k.nullSafe) {
		return tagCond;
	}
	return "(" + lcol + " IS NULL OR " + rcol + " IS NULL OR " + tagCond + ")";
}

// Extra projected columns to append to an SpjRelation's SELECT list: the
// (mangled name, SQL expression) pairs a join renderer needs exposed through
// the derived-table boundary so it can compare native key columns.
// Some magic numbers for the reserve call, try and allocate sufficient space
// for the common case without over-allocating too much.

bool isIdentChar(char ch) {
	return std::isalnum(static_cast<unsigned char>(ch)) != 0 || ch == '_';
}

// Replace every occurrence of the column reference `ref` (e.g. t5."cid") that is
// not the tail of a longer identifier (t15."cid").
std::string replaceRef(const std::string &text, const std::string &ref, const std::string &with) {
	std::string out;
	std::size_t pos = 0;
	while (true) {
		const std::size_t hit = text.find(ref, pos);
		if (hit == std::string::npos) {
			out.append(text, pos, std::string::npos);
			return out;
		}
		out.append(text, pos, hit - pos);
		if (hit > 0 && isIdentChar(text[hit - 1])) {
			out += ref;
		} else {
			out += with;
		}
		pos = hit + ref.size();
	}
}

// True when some `<identifier>."` column reference other than `allowedAlias."`
// is left in `text`, i.e. the expression still reaches into a FROM source.
bool referencesOtherAlias(const std::string &text, const std::string &allowedAlias) {
	for (std::size_t pos = text.find(".\""); pos != std::string::npos; pos = text.find(".\"", pos + 1)) {
		std::size_t start = pos;
		while (start > 0 && isIdentChar(text[start - 1])) {
			--start;
		}
		if (start < pos && text.compare(start, pos - start, allowedAlias) != 0) {
			return true;
		}
	}
	return false;
}

// How a column's raw values may stand in for its text when deduplicating.
// Exact: the text rendering is one-to-one with the value. Floating: one-to-one
// except that -0.0 and 0.0 are equal but print differently, so the dedup key
// also needs the sign bit. None: unknown type, or anything else.
enum class RawKind { None, Exact, Floating };

RawKind rawKind(const TypeCatalog &cat, const std::string &table, const std::string &column) {
	if (cat.isIntegerType(table, column) || cat.isStringType(table, column)) {
		return RawKind::Exact;
	}
	std::string type = cat.typeOf(table, column);
	std::transform(type.begin(), type.end(), type.begin(), ::toupper);
	for (const char *prefix : {"DECIMAL", "NUMERIC", "DATE", "TIMESTAMP", "BOOLEAN"}) {
		if (type.rfind(prefix, 0) == 0) {
			return RawKind::Exact;
		}
	}
	for (const char *prefix : {"DOUBLE", "FLOAT", "REAL"}) {
		if (type.rfind(prefix, 0) == 0) {
			return RawKind::Floating;
		}
	}
	return RawKind::None;
}

// Deduplicate on raw columns: a DISTINCT block whose every term is a constant, a
// plain column or an invertible template over typed columns (see rawKind) is rendered
// as SELECT <terms> FROM (SELECT DISTINCT <raw columns> FROM ... WHERE ...), so
// the engine hashes the raw values instead of building every IRI and text value
// first. Each term is a one-to-one function of its columns and every raw column
// feeds some term, so both forms keep the same rows. Returns "" when the block
// does not qualify, or when any projected expression would still reach into a
// FROM source after substitution.
std::string renderRawDistinct(const SpjRelation &rel, const std::vector<std::string> &cols, TranslationContext &ctx) {
	if (ctx.catalog() == nullptr || rel.schema().empty()) {
		return std::string();
	}
	const TypeCatalog &cat = *ctx.catalog();
	const SqlDialect &dialect = ctx.dialect();
	std::vector<std::string> refs;
	std::set<std::string> floating;
	// False when the column cannot take part; a floating column needs the dialect's sign bit.
	auto addRef = [&](const std::string &ref, const std::string &table, const std::string &column) {
		const RawKind kind = rawKind(cat, table, column);
		if (kind == RawKind::None || (kind == RawKind::Floating && dialect.floatSignBit(ref).empty())) {
			return false;
		}
		if (std::find(refs.begin(), refs.end(), ref) == refs.end()) {
			refs.push_back(ref);
		}
		if (kind == RawKind::Floating) {
			floating.insert(ref);
		}
		return true;
	};
	for (const auto &c : rel.schema()) {
		switch (c.prov) {
		case Provenance::ConstantExpr:
			break;
		case Provenance::PureColumn:
			if (c.nativeColumnRef.empty() || !addRef(c.nativeColumnRef, c.tableIdentity, c.columnName)) {
				return std::string();
			}
			break;
		case Provenance::TemplateExpr:
			if (!c.templateInvertible || c.templateColumnRefs.empty() ||
			    c.templateColumnRefs.size() != c.templateColumnNames.size()) {
				return std::string();
			}
			for (std::size_t i = 0; i < c.templateColumnRefs.size(); ++i) {
				if (!addRef(c.templateColumnRefs[i], c.tableIdentity, c.templateColumnNames[i])) {
					return std::string();
				}
			}
			break;
		default:
			return std::string();
		}
	}
	if (refs.empty()) {
		return std::string();
	}
	const std::string alias = ctx.nextAlias();
	std::vector<std::string> inner;
	std::vector<std::string> outer;
	for (std::size_t i = 0; i < refs.size(); ++i) {
		inner.push_back(refs[i] + " AS " + dialect.quoteIdentifier("r" + std::to_string(i)));
		if (floating.count(refs[i]) != 0) {
			inner.push_back(dialect.floatSignBit(refs[i]) + " AS " + dialect.quoteIdentifier("s" + std::to_string(i)));
		}
	}
	for (const auto &col : cols) {
		std::string text = col;
		for (std::size_t i = 0; i < refs.size(); ++i) {
			text = replaceRef(text, refs[i], alias + "." + dialect.quoteIdentifier("r" + std::to_string(i)));
		}
		if (referencesOtherAlias(text, alias)) {
			return std::string();
		}
		outer.push_back(text);
	}
	std::string sql = "SELECT DISTINCT" + joinColumnList(inner, ctx) + ctx.clauseSep() + "FROM ";
	for (std::size_t i = 0; i < rel.sources.size(); ++i) {
		sql += (i > 0 ? ", " : "") + rel.sources[i].sql;
	}
	if (!rel.whereConds.empty()) {
		std::vector<std::string> conds;
		conds.reserve(rel.whereConds.size());
		for (const auto &c : rel.whereConds) {
			conds.push_back("(" + c + ")");
		}
		sql += ctx.clauseSep() + "WHERE " + joinConditions(conds, ctx);
	}
	return "SELECT" + joinColumnList(outer, ctx) + ctx.clauseSep() + "FROM (" + sql + ") AS " + alias;
}

std::string renderSpj(const SpjRelation &rel, TranslationContext &ctx, const ExtraProjections *extra) {
	const SqlDialect &dialect = ctx.dialect();
	std::string sql;
	sql.reserve(256 + rel.schema().size() * 64 + rel.sources.size() * 128 + rel.whereConds.size() * 64);
	sql = "SELECT";
	if (rel.distinct) {
		sql += " DISTINCT";
	}
	if (rel.schema().empty() && (extra == nullptr || extra->empty())) {
		sql += joinColumnList({"1 AS " + dialect.quoteIdentifier("_dummy")}, ctx);
	} else {
		std::vector<std::string> cols;
		for (const auto &c : rel.schema()) {
			cols.push_back(c.renderedExpr + " AS " + mangleVar(c.var, dialect));
			if (ctx.needsTag(c.var)) {
				cols.push_back(producedTag(c, "this select-project-join block") + " AS " +
				               mangleVarTag(c.var, dialect));
			}
		}
		if (extra != nullptr) {
			for (const auto &e : *extra) {
				cols.push_back(e.second + " AS " + e.first);
			}
		}
		if (ctx.nativeRoot() == &rel) {
			// A function of a column already projected here, so it never changes
			// what a DISTINCT on this block keeps.
			for (const auto &n : ctx.nativeRootExprs()) {
				cols.push_back(n.second + " AS " + mangleVarNative(n.first, dialect));
			}
		}
		if (rel.distinct) {
			std::string raw = renderRawDistinct(rel, cols, ctx);
			if (!raw.empty()) {
				return raw;
			}
		}
		sql += joinColumnList(cols, ctx);
	}
	sql += ctx.clauseSep() + "FROM ";
	for (std::size_t i = 0; i < rel.sources.size(); ++i) {
		if (i > 0) {
			// Multi-source (post-flatten) spine: cross-join sources; the
			// inter-source join equalities live in whereConds.
			sql += ", ";
		}
		sql += rel.sources[i].sql;
	}
	if (!rel.whereConds.empty()) {
		std::vector<std::string> conds;
		conds.reserve(rel.whereConds.size());
		for (const auto &c : rel.whereConds) {
			conds.push_back("(" + c + ")");
		}
		sql += ctx.clauseSep() + "WHERE " + joinConditions(conds, ctx);
	}
	return sql;
}

// The raw keys a transitive closure can recurse on: one pair of placeholder
// columns per template placeholder, `from` side and `to` side of the step.
// Non-empty only when the step is one SPJ block whose two endpoints are the
// same invertible template over type-comparable columns (nativeKeyPairs's
// conditions), so that equal keys mean equal IRIs and the other way round.
// Then each hop joins on integer (or whatever the key type is) columns rather
// than on IRI text built for every edge, and the closure can hand its keys to
// the join above it.
std::vector<NativeKeyPair> closureKeyPairs(const TransitiveClosureNode &tc, const TypeCatalog *catalog) {
	if (tc.step == nullptr || tc.step->kind() != RelKind::Spj) {
		return {};
	}
	const ColumnInfo *from = tc.step->column(tc.fromVar);
	const ColumnInfo *to = tc.step->column(tc.toVar);
	if (from == nullptr || to == nullptr) {
		return {};
	}
	return nativeKeyPairs(*from, *to, catalog);
}

// Bare names of the closure CTE's key columns: `cte_k<i>` for the reached
// node of a unary closure, `cte_fk<i>`/`cte_tk<i>` for the pairs closure.
std::string closureKeyName(const std::string &prefix, std::size_t i, const SqlDialect &dialect) {
	return dialect.quoteIdentifier(prefix + std::to_string(i));
}

// A ColumnInfo describing `var` of a key-carrying closure as the template it
// is, with placeholder refs that name the closure's own key columns - so
// planNativeKeys can join the closure to a neighbouring scan on keys, the
// same way it joins two scans. Null when `var` is not an endpoint the closure
// carries keys for.
std::unique_ptr<ColumnInfo> closureColumnInfo(const TransitiveClosureNode &tc, const std::string &var,
                                              const TypeCatalog *catalog, const SqlDialect &dialect) {
	if (tc.mode == TransitiveClosureNode::Mode::BothBound || closureKeyPairs(tc, catalog).empty()) {
		return nullptr;
	}
	const auto &schema = tc.schema();
	std::string prefix;
	const ColumnInfo *source = nullptr;
	if (tc.mode == TransitiveClosureNode::Mode::BothVars) {
		if (!schema.empty() && schema[0].var == var) {
			prefix = "cte_fk";
			source = tc.step->column(tc.fromVar);
		} else if (!tc.sameEndpointVar && schema.size() > 1 && schema[1].var == var) {
			prefix = "cte_tk";
			source = tc.step->column(tc.toVar);
		}
	} else if (!schema.empty() && schema[0].var == var) {
		prefix = "cte_k";
		bool forward = tc.mode != TransitiveClosureNode::Mode::BackwardFromObject;
		source = tc.step->column(forward ? tc.toVar : tc.fromVar);
	}
	if (source == nullptr) {
		return nullptr;
	}
	std::unique_ptr<ColumnInfo> info(new ColumnInfo(*source));
	info->var = var;
	for (std::size_t i = 0; i < info->templateColumnRefs.size(); ++i) {
		info->templateColumnRefs[i] = closureKeyName(prefix, i, dialect);
	}
	return info;
}

// The column a native-key plan sees for `var` on one side of a join: the
// key's own ColumnInfo for a scan, the key-carrying description for a closure.
// Null when the side cannot expose native columns at all.
const ColumnInfo *nativeSideColumn(const RelNode &side, const ColumnInfo &keyCol, TranslationContext &ctx,
                                   std::unique_ptr<ColumnInfo> &holder) {
	if (side.kind() == RelKind::Spj) {
		// The block's own column, not the key's copy: the key was described
		// when the join was built, and flattening may since have merged this
		// side into a block whose column has different (better) provenance.
		const ColumnInfo *own = side.column(keyCol.var);
		return own != nullptr ? own : &keyCol;
	}
	if (side.kind() == RelKind::TransitiveClosure) {
		holder = closureColumnInfo(static_cast<const TransitiveClosureNode &>(side), keyCol.var, ctx.catalog(),
		                           ctx.dialect());
		return holder.get();
	}
	return nullptr;
}

// Plan native-column comparisons for a join across the derived-table boundary.
// Only the projected term text is in scope out there, so a native comparison
// needs each side's base columns exposed as extra hidden projections, which is
// only possible when the child renders its own SELECT list - i.e. when it is
// directly an SpjRelation (the shape flattening produces), or a transitive
// closure that recurses on raw keys (closureColumnInfo). Anything else, and any
// null-tolerant key, keeps the term-text comparison.
//
// This is the rewrite an engine cannot perform for itself: R2RML subjects are
// nearly always rr:template IRIs, so without it every subject join hashes
// constructed IRI strings instead of the underlying key columns.
void planNativeKeys(const std::vector<EquiKey> &keys, const RelNode &left, const RelNode &right,
                    TranslationContext &ctx, const std::string &leftAlias, const std::string &rightAlias,
                    ExtraProjections &leftExtra, ExtraProjections &rightExtra, std::vector<std::string> &conds,
                    std::vector<bool> &rewritten) {
	rewritten.assign(keys.size(), false);
	auto exposes = [](const RelNode &n) {
		return n.kind() == RelKind::Spj || n.kind() == RelKind::TransitiveClosure;
	};
	if (!exposes(left) || !exposes(right)) {
		return;
	}
	const SqlDialect &dialect = ctx.dialect();
	for (std::size_t i = 0; i < keys.size(); ++i) {
		if (keys[i].nullSafe) {
			continue;
		}
		std::unique_ptr<ColumnInfo> leftHolder;
		std::unique_ptr<ColumnInfo> rightHolder;
		const ColumnInfo *lc = nativeSideColumn(left, keys[i].leftCol, ctx, leftHolder);
		const ColumnInfo *rc = nativeSideColumn(right, keys[i].rightCol, ctx, rightHolder);
		if (lc == nullptr || rc == nullptr) {
			continue;
		}
		std::vector<NativeKeyPair> pairs = nativeKeyPairs(*lc, *rc, ctx.catalog());
		if (pairs.empty()) {
			continue;
		}
		for (const auto &p : pairs) {
			std::string hidden = dialect.quoteIdentifier("k_" + std::to_string(leftExtra.size()));
			leftExtra.emplace_back(hidden, p.leftRef);
			rightExtra.emplace_back(hidden, p.rightRef);
			conds.push_back(leftAlias + "." + hidden + " = " + rightAlias + "." + hidden);
		}
		rewritten[i] = true;
	}
}

// Render a join/anti-join child, appending `extra` hidden projections when the
// native-key plan asked for them (only ever non-empty for a direct Spj child).
std::string renderChild(const RelNode &node, TranslationContext &ctx, const ExtraProjections &extra) {
	if (!extra.empty() && node.kind() == RelKind::Spj) {
		return renderSpj(static_cast<const SpjRelation &>(node), ctx, &extra);
	}
	if (!extra.empty() && node.kind() == RelKind::TransitiveClosure) {
		return renderTransitiveClosure(static_cast<const TransitiveClosureNode &>(node), ctx, &extra);
	}
	return renderNode(node, ctx);
}

// A seeded pairs closure (magic sets): `?x :p+ ?y` with both ends variable
// is a closure over every pair, but joined to a partner that binds ?x (or ?y)
// only the pairs starting (or ending) at the partner's values can survive. So
// the partner is rendered once as a CTE, the closure walks from its distinct
// values (renderSplitClosure with a ClosureSeed), and the join reads both.
// Returns the closure's SQL, or "" when the join does not have that shape or the
// closure cannot be seeded; `partnerSql` then holds nothing.
std::string seededClosure(const RelNode &left, const RelNode &right, const std::vector<EquiKey> &keys, JoinKind kind,
                          TranslationContext &ctx, bool &closureOnRight, std::string &partnerSql,
                          std::size_t &startKeys, std::string &seedVar) {
	startKeys = 0;
	if (kind != JoinKind::Inner) {
		return std::string();
	}
	const RelNode *tcNode = nullptr;
	const RelNode *partner = nullptr;
	if (right.kind() == RelKind::TransitiveClosure) {
		tcNode = &right;
		partner = &left;
		closureOnRight = true;
	} else if (left.kind() == RelKind::TransitiveClosure) {
		tcNode = &left;
		partner = &right;
		closureOnRight = false;
	} else {
		return std::string();
	}
	const auto &tc = static_cast<const TransitiveClosureNode &>(*tcNode);
	if (tc.mode != TransitiveClosureNode::Mode::BothVars || tc.sameEndpointVar || !tc.invariantVars.empty() ||
	    tc.schema().size() < 2) {
		return std::string();
	}
	// Seed the end the partner binds in every row; prefer the subject end.
	const ColumnInfo *seedCol = nullptr;
	bool onFrom = true;
	for (int end = 0; end < 2 && seedCol == nullptr; ++end) {
		const ColumnInfo *c = partner->column(tc.schema()[end].var);
		bool keyed = false;
		for (const auto &k : keys) {
			keyed = keyed || (k.var == tc.schema()[end].var && !k.nullSafe);
		}
		if (c != nullptr && c->nonNull && keyed) {
			seedCol = c;
			onFrom = end == 0;
		}
	}
	if (seedCol == nullptr) {
		return std::string();
	}
	seedVar = seedCol->var;
	const SqlDialect &dialect = ctx.dialect();
	ClosureSeed seed;
	seed.cte = ctx.nextCteName();
	seed.iriCol = mangleVar(seedCol->var, dialect);
	seed.col = seedCol;
	seed.onFrom = onFrom;
	ExtraProjections seedKeys;
	if (partner->kind() == RelKind::Spj && seedCol->prov == Provenance::TemplateExpr && seedCol->templateInvertible) {
		for (const auto &ref : seedCol->templateColumnRefs) {
			const std::string name = dialect.quoteIdentifier("sk_" + std::to_string(seedKeys.size()));
			seedKeys.emplace_back(name, ref);
			seed.keyCols.push_back(name);
		}
	}
	std::string cteSql = renderChild(*partner, ctx, seedKeys);
	ctx.addCte(seed.cte, cteSql);
	std::string closureSql = renderSplitClosure(tc, ctx, &seed, nullptr, &startKeys);
	if (closureSql.empty()) {
		// Not seedable after all: still read the partner from its CTE.
		closureSql = renderNode(tc, ctx);
		startKeys = 0;
	}
	partnerSql = "SELECT * FROM " + seed.cte;
	return closureSql;
}

// A unary closure (one end anchored) joined to a scan on the node it reaches:
// render the closure restricted to what the scan's template can meet, and join
// on raw key columns when every remaining part carries them. A question about
// districts then never scans the address links below them, and a question
// about addresses joins them on their keys, not on built IRI text.
// Closure output already rendered for one union arm, by partner template, so
// the other arms of a distributed join (renderJoin) read the same CTE.
using ClosureMemo = std::map<std::string, std::pair<std::string, std::size_t>>;

bool closureKeyJoin(const RelNode &left, const RelNode &right, const std::vector<EquiKey> &keys, JoinKind kind,
                    TranslationContext &ctx, const std::string &leftAlias, const std::string &rightAlias,
                    std::string &leftSql, std::string &rightSql, std::vector<std::string> &nativeConds,
                    std::vector<bool> &rewritten, std::set<std::string> &fromRight, ClosureMemo *memo) {
	if (kind != JoinKind::Inner) {
		return false;
	}
	const bool tcRight = right.kind() == RelKind::TransitiveClosure;
	const RelNode &tcNode = tcRight ? right : left;
	const RelNode &partner = tcRight ? left : right;
	if (tcNode.kind() != RelKind::TransitiveClosure || partner.kind() != RelKind::Spj) {
		return false;
	}
	const auto &tc = static_cast<const TransitiveClosureNode &>(tcNode);
	if (tc.mode != TransitiveClosureNode::Mode::ForwardFromSubject &&
	    tc.mode != TransitiveClosureNode::Mode::BackwardFromObject) {
		return false;
	}
	if (tc.schema().empty()) {
		return false;
	}
	const std::string &var = tc.schema()[0].var;
	std::size_t keyIndex = keys.size();
	for (std::size_t i = 0; i < keys.size(); ++i) {
		if (keys[i].var == var && !keys[i].nullSafe) {
			keyIndex = i;
		}
	}
	const ColumnInfo *outCol = partner.column(var);
	if (keyIndex == keys.size() || outCol == nullptr) {
		return false;
	}
	std::size_t nOut = 0;
	std::string tcSql;
	const std::string memoKey = outCol->templateString + "|" + std::to_string(outCol->templateColumnRefs.size());
	if (memo != nullptr && memo->count(memoKey) != 0) {
		tcSql = "SELECT * FROM " + (*memo)[memoKey].first;
		nOut = (*memo)[memoKey].second;
	} else {
		{
			TranslationContext::SubqueryDepthGuard depthGuard(ctx);
			tcSql = renderSplitClosure(tc, ctx, nullptr, outCol, &nOut);
		}
		if (tcSql.empty()) {
			return false;
		}
		if (memo != nullptr) {
			const std::string cte = ctx.nextCteName();
			ctx.addCte(cte, tcSql);
			(*memo)[memoKey] = std::make_pair(cte, nOut);
			tcSql = "SELECT * FROM " + cte;
		}
	}
	const SqlDialect &dialect = ctx.dialect();
	ExtraProjections partnerExtra;
	rewritten.assign(keys.size(), false);
	if (nOut > 0) {
		const std::string &pAlias = tcRight ? leftAlias : rightAlias;
		const std::string &tAlias = tcRight ? rightAlias : leftAlias;
		for (std::size_t i = 0; i < nOut; ++i) {
			const std::string name = dialect.quoteIdentifier("ok_" + std::to_string(i));
			partnerExtra.emplace_back(name, outCol->templateColumnRefs[i]);
			nativeConds.push_back(pAlias + "." + name + " = " + tAlias + "." + name);
		}
		rewritten[keyIndex] = true;
		// Take the term from the closure side, which built it for the joined rows
		// only; the scan's own term column is then unused and never computed.
		if (tcRight) {
			fromRight.insert(var);
		}
	}
	std::string partnerSql;
	{
		TranslationContext::SubqueryDepthGuard depthGuard(ctx);
		partnerSql = renderChild(partner, ctx, partnerExtra);
	}
	leftSql = tcRight ? partnerSql : tcSql;
	rightSql = tcRight ? tcSql : partnerSql;
	return true;
}

std::string renderJoinParts(const RelNode &left, const RelNode &right, const std::vector<EquiKey> &keys, JoinKind kind,
                            TranslationContext &ctx, ClosureMemo *memo = nullptr) {
	const SqlDialect &dialect = ctx.dialect();
	std::string leftAlias = ctx.nextAlias();
	std::string rightAlias = ctx.nextAlias();

	ExtraProjections leftExtra;
	ExtraProjections rightExtra;
	std::vector<std::string> nativeConds;
	std::vector<bool> rewritten;
	std::string leftSql;
	std::string rightSql;
	bool closureOnRight = false;
	std::string partnerSql;
	std::string closureSql;
	std::set<std::string> fromRight; // shared variables projected from the right side
	std::size_t startKeys = 0;
	std::string seedVar;
	{
		TranslationContext::SubqueryDepthGuard depthGuard(ctx);
		closureSql = seededClosure(left, right, keys, kind, ctx, closureOnRight, partnerSql, startKeys, seedVar);
	}
	if (!closureSql.empty()) {
		// Seeded: the closure is already narrowed to the partner's values. It
		// meets the partner on the start's raw keys when it carried them (and the
		// start's term then comes from the partner), else on term text.
		rewritten.assign(keys.size(), false);
		for (std::size_t i = 0; i < keys.size() && startKeys > 0; ++i) {
			if (keys[i].var == seedVar) {
				rewritten[i] = true;
				for (std::size_t k = 0; k < startKeys; ++k) {
					const std::string col = dialect.quoteIdentifier("sk_" + std::to_string(k));
					nativeConds.push_back(leftAlias + "." + col + " = " + rightAlias + "." + col);
				}
				if (!closureOnRight) {
					fromRight.insert(seedVar);
				}
			}
		}
		leftSql = closureOnRight ? partnerSql : closureSql;
		rightSql = closureOnRight ? closureSql : partnerSql;
	} else if (!closureKeyJoin(left, right, keys, kind, ctx, leftAlias, rightAlias, leftSql, rightSql, nativeConds,
	                           rewritten, fromRight, memo)) {
		planNativeKeys(keys, left, right, ctx, leftAlias, rightAlias, leftExtra, rightExtra, nativeConds, rewritten);
		TranslationContext::SubqueryDepthGuard depthGuard(ctx);
		leftSql = renderChild(left, ctx, leftExtra);
		rightSql = renderChild(right, ctx, rightExtra);
	}

	std::set<std::string> shared;
	for (const auto &k : keys) {
		shared.insert(k.var);
	}

	std::vector<std::string> onConditions;
	std::vector<std::string> projectExprs;
	projectExprs.reserve(left.schema().size() + right.schema().size() + keys.size() * 2);
	for (std::size_t i = 0; i < keys.size(); ++i) {
		const EquiKey &k = keys[i];
		std::string lcol = leftAlias + "." + mangleVar(k.var, dialect);
		std::string rcol = rightAlias + "." + mangleVar(k.var, dialect);
		if (!rewritten[i]) {
			onConditions.push_back(keyComparison(k, lcol, rcol));
		}
		// Not folded into keyComparison: a native-key rewrite replaces the
		// lexical comparison but says nothing about the dimension, so the tag
		// check applies to every form of the key equally.
		const std::string tagCond = keyTagComparison(k, ctx, leftAlias, rightAlias, lcol, rcol);
		if (!tagCond.empty()) {
			onConditions.push_back(tagCond);
		}
		if (k.nullSafe) {
			projectExprs.push_back("COALESCE(" + lcol + ", " + rcol + ") AS " + mangleVar(k.var, dialect));
		} else {
			projectExprs.push_back((fromRight.count(k.var) != 0 ? rcol : lcol) + " AS " + mangleVar(k.var, dialect));
		}
		if (ctx.needsTag(k.var)) {
			const std::string ltag = leftAlias + "." + mangleVarTag(k.var, dialect);
			const std::string rtag = rightAlias + "." + mangleVarTag(k.var, dialect);
			// A plain COALESCE of the two *columns* is exactly right here, unlike
			// the constant-tag case in mergeInner: a child's tag column is NULL
			// precisely when its value column is, so COALESCE picks the tag from
			// the same side the value came from.
			projectExprs.push_back(
			    (k.nullSafe ? ("COALESCE(" + ltag + ", " + rtag + ")") : (fromRight.count(k.var) != 0 ? rtag : ltag)) +
			    " AS " + mangleVarTag(k.var, dialect));
		}
	}
	onConditions.insert(onConditions.end(), nativeConds.begin(), nativeConds.end());
	for (const auto &v : left.allVars()) {
		if (shared.count(v)) {
			continue;
		}
		projectExprs.push_back(leftAlias + "." + mangleVar(v, dialect) + " AS " + mangleVar(v, dialect));
		if (ctx.needsTag(v)) {
			projectExprs.push_back(leftAlias + "." + mangleVarTag(v, dialect) + " AS " + mangleVarTag(v, dialect));
		}
	}
	for (const auto &v : right.allVars()) {
		if (shared.count(v)) {
			continue;
		}
		projectExprs.push_back(rightAlias + "." + mangleVar(v, dialect) + " AS " + mangleVar(v, dialect));
		if (ctx.needsTag(v)) {
			projectExprs.push_back(rightAlias + "." + mangleVarTag(v, dialect) + " AS " + mangleVarTag(v, dialect));
		}
	}

	// A native-aggregate block below this join (see Translator.cpp): pass its
	// n_<var> companions up, so the aggregate above reads table values.
	for (const auto &child : {std::make_pair(&left, &leftAlias), std::make_pair(&right, &rightAlias)}) {
		if (ctx.nativeRoot() == child.first) {
			for (const auto &n : ctx.nativeRootExprs()) {
				const std::string col = mangleVarNative(n.first, dialect);
				projectExprs.push_back(*child.second + "." + col + " AS " + col);
			}
		}
	}

	std::string sql;
	sql.reserve(256);
	sql = "SELECT";
	if (projectExprs.empty()) {
		sql += joinColumnList({"1 AS " + dialect.quoteIdentifier("_dummy")}, ctx);
	} else {
		sql += joinColumnList(projectExprs, ctx);
	}
	const char *keyword = kind == JoinKind::LeftOuter ? "LEFT OUTER JOIN" : "INNER JOIN";
	sql += ctx.clauseSep() + "FROM (" + leftSql + ") AS " + leftAlias;
	sql += ctx.clauseSep() + keyword + " (" + rightSql + ") AS " + rightAlias;
	sql += ctx.onSep() + "ON ";
	if (onConditions.empty()) {
		sql += dialect.booleanLiteral(true);
	} else {
		sql += joinConditions(onConditions, ctx);
	}
	return sql;
}

// A closure joined to a union of scans: join each arm separately, so the arms
// are narrowed by the closure (and joined on keys where they can be) before
// their union removes duplicates, instead of after.
// (A u B) JOIN T = (A JOIN T) u (B JOIN T), for bag and set unions alike.
std::string renderJoin(const JoinNode &join, TranslationContext &ctx) {
	if (join.joinKind == JoinKind::Inner) {
		const bool tcRight = join.right->kind() == RelKind::TransitiveClosure;
		const bool tcLeft = join.left->kind() == RelKind::TransitiveClosure;
		const RelNode *other = tcRight ? join.left.get() : (tcLeft ? join.right.get() : nullptr);
		// Only a one-end-anchored closure whose step mixes templates: that is
		// what closureKeyJoin narrows per arm (sharing one rendering). Any other
		// closure would just be rendered again for every arm.
		const RelNode *tcSide = tcRight ? join.right.get() : join.left.get();
		bool splittable = false;
		if (other != nullptr) {
			const auto &tc = static_cast<const TransitiveClosureNode &>(*tcSide);
			splittable = (tc.mode == TransitiveClosureNode::Mode::ForwardFromSubject ||
			              tc.mode == TransitiveClosureNode::Mode::BackwardFromObject) &&
			             closureArmCount(tc) >= 2;
		}
		if (other != nullptr && splittable && other->kind() == RelKind::UnionByName) {
			const auto &un = static_cast<const UnionByNameNode &>(*other);
			bool armsOk = !un.arms.empty();
			for (const auto &arm : un.arms) {
				armsOk = armsOk && arm->kind() == RelKind::Spj;
				for (const auto &k : join.keys) {
					armsOk = armsOk && arm->column(k.var) != nullptr && !k.nullSafe;
				}
			}
			if (armsOk) {
				std::vector<std::string> parts;
				parts.reserve(un.arms.size());
				ClosureMemo memo;
				for (const auto &arm : un.arms) {
					parts.push_back(tcRight ? renderJoinParts(*arm, *join.right, join.keys, join.joinKind, ctx, &memo)
					                        : renderJoinParts(*join.left, *arm, join.keys, join.joinKind, ctx, &memo));
				}
				return ctx.dialect().combineByName(un.all, parts);
			}
		}
	}
	return renderJoinParts(*join.left, *join.right, join.keys, join.joinKind, ctx);
}

std::string renderAntiJoin(const AntiJoinNode &anti, TranslationContext &ctx) {
	const SqlDialect &dialect = ctx.dialect();
	std::string leftAlias = ctx.nextAlias();
	std::string rightAlias = ctx.nextAlias();
	ExtraProjections leftExtra;
	ExtraProjections rightExtra;
	std::vector<std::string> nativeConds;
	std::vector<bool> rewritten;
	planNativeKeys(anti.keys, *anti.left, *anti.right, ctx, leftAlias, rightAlias, leftExtra, rightExtra, nativeConds,
	               rewritten);

	std::string leftSql;
	std::string rightSql;
	{
		TranslationContext::SubqueryDepthGuard depthGuard(ctx);
		leftSql = renderChild(*anti.left, ctx, leftExtra);
		rightSql = renderChild(*anti.right, ctx, rightExtra);
	}

	std::vector<std::string> conds;
	conds.reserve(anti.keys.size() * 2 + nativeConds.size());
	for (std::size_t i = 0; i < anti.keys.size(); ++i) {
		const EquiKey &k = anti.keys[i];
		std::string lcol = leftAlias + "." + mangleVar(k.var, dialect);
		std::string rcol = rightAlias + "." + mangleVar(k.var, dialect);
		if (!rewritten[i]) {
			conds.push_back(keyComparison(k, lcol, rcol));
		}
		// MINUS's compatibility test is RDF term equality too: a right-hand row
		// whose term merely spells the same text must not eliminate a left row.
		const std::string tagCond = keyTagComparison(k, ctx, leftAlias, rightAlias, lcol, rcol);
		if (!tagCond.empty()) {
			conds.push_back(tagCond);
		}
	}
	conds.insert(conds.end(), nativeConds.begin(), nativeConds.end());
	std::string cond = joinConditions(conds, ctx);

	// Project MINUS's schema (which is the left operand's) explicitly rather
	// than SELECT *: the left side may carry hidden native-key columns that must
	// not escape into an enclosing UNION BY NAME.
	std::vector<std::string> projectionCols;
	projectionCols.reserve(anti.schema().size() * 2);
	for (const auto &c : anti.schema()) {
		projectionCols.push_back(leftAlias + "." + mangleVar(c.var, dialect) + " AS " + mangleVar(c.var, dialect));
		if (ctx.needsTag(c.var)) {
			projectionCols.push_back(leftAlias + "." + mangleVarTag(c.var, dialect) + " AS " +
			                         mangleVarTag(c.var, dialect));
		}
	}
	std::string sql;
	sql.reserve(256);
	sql = "SELECT";
	sql += projectionCols.empty() ? joinColumnList({"1 AS " + dialect.quoteIdentifier("_dummy")}, ctx)
	                              : joinColumnList(projectionCols, ctx);
	sql += ctx.clauseSep() + "FROM (" + leftSql + ") AS " + leftAlias + " WHERE NOT EXISTS (SELECT 1 FROM (" +
	       rightSql + ") AS " + rightAlias + " WHERE " + cond + ")";
	return sql;
}

std::string renderUnion(const UnionByNameNode &un, TranslationContext &ctx) {
	std::vector<std::string> armSqls;
	armSqls.reserve(un.arms.size());
	for (const auto &arm : un.arms) {
		armSqls.push_back(renderNode(*arm, ctx));
	}
	return ctx.dialect().combineByName(un.all, armSqls);
}

std::string renderFilter(const FilterNode &f, TranslationContext &ctx) {
	std::string alias = ctx.nextAlias();
	std::string childSql;
	{
		TranslationContext::SubqueryDepthGuard depthGuard(ctx);
		childSql = renderNode(*f.child, ctx);
	}
	TranslatedPattern scope = scopeOf(*f.child);
	// Reinstate the graph this FILTER was written under before translating it:
	// an EXISTS in the predicate folds its own graph pattern, and must do so
	// against that graph rather than whatever is active at render time.
	TranslationContext::ActiveGraphGuard graphGuard(ctx, f.activeGraph);
	std::string cond = translateExpression(*f.predicate, scope, alias, ctx);
	return "SELECT *" + ctx.clauseSep() + "FROM (" + childSql + ") AS " + alias + ctx.clauseSep() + "WHERE " + cond;
}

std::string renderBind(const BindNode &b, TranslationContext &ctx) {
	std::string alias = ctx.nextAlias();
	std::string childSql;
	{
		TranslationContext::SubqueryDepthGuard depthGuard(ctx);
		childSql = renderNode(*b.child, ctx);
	}
	TranslatedPattern scope = scopeOf(*b.child);
	TranslationContext::ActiveGraphGuard graphGuard(ctx, b.activeGraph); // see renderFilter
	TermSql bound = translateTerm(*b.expr, scope, alias, ctx);
	std::string extra;
	if (ctx.needsTag(b.outVar)) {
		if (bound.tag.empty()) {
			throw TranslationError("unsupported: the RDF term dimension of the BIND-ed variable ?" + b.outVar +
			                       " is needed at run time, but neither the mapping nor this translator can derive it "
			                       "from the defining expression.");
		}
		extra = ", (" + bound.tag + ") AS " + mangleVarTag(b.outVar, ctx.dialect());
	}
	return "SELECT *, (" + bound.value + ") AS " + mangleVar(b.outVar, ctx.dialect()) + extra + ctx.clauseSep() +
	       "FROM (" + childSql + ") AS " + alias;
}

// ---------------------------------------------------------------------------
// Closures whose step mixes templates: recurse only where a hop can follow.
//
// A transitive property often links two kinds of thing: addresses to their
// neighbourhood and regions to their parent region, under one nl:liesIn. The
// step relation is then a union of arms with different templates, so the
// closure cannot recurse on keys, and the recursion drags every address link
// through every iteration, building IRI text for all of them.
//
// But an address IRI is never the object of a liesIn link, so an address link
// can only ever be the first hop of a path: liesIn+ = regions+ u addressLink u
// addressLink/regions+. In general, judged per arm from its two templates
// (templatesCanEverMatch):
//  - a *leaf* arm lands on a node no arm walks on: it can only be the last hop;
//  - a *start* arm walks from a node no arm lands on: it can only be the first;
//  - every other arm is a *core* arm, and only core arms recurse.
// Leaf and start arms are then joined once, outside the recursion, and the
// core usually has one template at both ends, so it recurses on raw keys.
// A constant anchor is compared on the raw columns it implies
// (invertTemplate), so no arm builds IRI text for rows it does not return.
// ---------------------------------------------------------------------------

struct ClosureArm {
	const SpjRelation *arm = nullptr;
	const ColumnInfo *from = nullptr;
	const ColumnInfo *to = nullptr;
};

bool armTemplated(const ColumnInfo *c) {
	return c != nullptr && c->prov == Provenance::TemplateExpr && !c->templateString.empty();
}

// The step's arms, or empty when any arm is not a templated SPJ block (then
// the split proves nothing and the closure renders as before).
std::vector<ClosureArm> closureArms(const TransitiveClosureNode &tc) {
	std::vector<ClosureArm> arms;
	auto add = [&](const RelNode &n) {
		if (n.kind() != RelKind::Spj) {
			return false;
		}
		ClosureArm a;
		a.arm = &static_cast<const SpjRelation &>(n);
		a.from = n.column(tc.fromVar);
		a.to = n.column(tc.toVar);
		if (!armTemplated(a.from) || !armTemplated(a.to)) {
			return false;
		}
		arms.push_back(a);
		return true;
	};
	if (tc.step == nullptr) {
		return arms;
	}
	if (tc.step->kind() == RelKind::UnionByName) {
		for (const auto &arm : static_cast<const UnionByNameNode &>(*tc.step).arms) {
			if (!add(*arm)) {
				return {};
			}
		}
	} else if (!add(*tc.step)) {
		return {};
	}
	return arms;
}

// How many templated SPJ arms the closure's step has (0 when any arm is not one).
std::size_t closureArmCount(const TransitiveClosureNode &tc) {
	return closureArms(tc).size();
}

// "SELECT <cols> FROM <arm sources>[, <extraFrom>] WHERE <arm conds> AND <extraConds>",
// with every expression in the arm's own scope. The arm's DISTINCT is dropped:
// every caller feeds a deduplicating UNION.
std::string armSelect(const SpjRelation &arm, const std::vector<std::string> &cols, const std::string &extraFrom,
                      const std::vector<std::string> &extraConds) {
	std::string sql = "SELECT ";
	for (std::size_t i = 0; i < cols.size(); ++i) {
		sql += (i > 0 ? ", " : "") + cols[i];
	}
	sql += " FROM ";
	for (std::size_t i = 0; i < arm.sources.size(); ++i) {
		sql += (i > 0 ? ", " : "") + arm.sources[i].sql;
	}
	if (!extraFrom.empty()) {
		sql += ", " + extraFrom;
	}
	std::vector<std::string> conds;
	conds.reserve(arm.whereConds.size() + extraConds.size());
	for (const auto &c : arm.whereConds) {
		conds.push_back("(" + c + ")");
	}
	for (const auto &c : extraConds) {
		conds.push_back("(" + c + ")");
	}
	if (!conds.empty()) {
		sql += " WHERE ";
		for (std::size_t i = 0; i < conds.size(); ++i) {
			sql += (i > 0 ? " AND " : "") + conds[i];
		}
	}
	return sql;
}

// The text of a SQL string literal ('it''s' -> it's).
std::string unquoteLiteral(const std::string &literal) {
	if (literal.size() < 2 || literal.front() != '\'' || literal.back() != '\'') {
		return literal;
	}
	std::string out;
	for (std::size_t i = 1; i + 1 < literal.size(); ++i) {
		out += literal[i];
		if (literal[i] == '\'' && i + 2 < literal.size() && literal[i + 1] == '\'') {
			++i;
		}
	}
	return out;
}

// The condition that an arm's end column equals a constant IRI: equalities on
// the raw placeholder columns when the template splits it, FALSE when it cannot
// produce it, the built term otherwise.
std::string anchorCondition(const ColumnInfo &col, const std::string &anchorLiteral, const SqlDialect &dialect) {
	if (col.templateInvertible && !col.templateColumnRefs.empty() &&
	    col.templateColumnRefs.size() == col.templateColumnNames.size()) {
		const bool iri = col.term.kind == RdfTermKind::Iri;
		InversionOutcome inv = invertTemplate(parseTemplate(col.templateString), unquoteLiteral(anchorLiteral),
		                                      /*percentDecodeValues=*/iri);
		if (inv.kind == InversionKind::NeverMatches) {
			return dialect.booleanLiteral(false);
		}
		if (inv.kind == InversionKind::PerColumnMatch && inv.columnValues.size() == col.templateColumnRefs.size()) {
			std::string cond;
			for (std::size_t i = 0; i < inv.columnValues.size(); ++i) {
				// The template rendered CAST(col AS VARCHAR), so compare that text:
				// a typed comparison could fail to cast a non-numeric value.
				cond += (i > 0 ? " AND " : "") + std::string("CAST(") + col.templateColumnRefs[i] +
				        " AS VARCHAR) = " + dialect.stringLiteral(inv.columnValues[i].second);
			}
			return cond;
		}
	}
	return col.renderedExpr + " = " + anchorLiteral;
}

// Render a closure whose step mixes templates (see the section comment), or
// return "" when the split does not apply and the plain closure should be used.
// With `seed`, a pairs closure walks only from the seed's values. With
// `outCol` (a unary closure's join partner column for the reached node), arms
// whose landing template the partner can never match are left out of the
// output, and when every remaining part lands in the partner's template shape
// the output also carries the raw placeholder columns as ok_0.. (*outKeys says
// how many; 0 when not exposed).
std::string renderSplitClosure(const TransitiveClosureNode &tc, TranslationContext &ctx, const ClosureSeed *seed,
                               const ColumnInfo *outCol, std::size_t *outKeys) {
	if (outKeys != nullptr) {
		*outKeys = 0;
	}
	if (!tc.invariantVars.empty() || tc.sameEndpointVar) {
		return std::string();
	}
	const std::vector<ClosureArm> arms = closureArms(tc);
	if (arms.size() < (seed != nullptr ? 1U : 2U)) {
		return std::string();
	}
	const SqlDialect &dialect = ctx.dialect();
	const TypeCatalog *catalog = ctx.catalog();

	// fromSide: the arm's `from` end (else its `to` end).
	auto end = [](const ClosureArm &a, bool fromSide) {
		return fromSide ? a.from : a.to;
	};
	// Can some arm's `otherSide` end ever equal this end of `a`?
	auto meets = [&](const ClosureArm &a, bool fromSide) {
		for (const auto &b : arms) {
			if (templatesCanEverMatch(end(a, fromSide)->templateString, end(b, !fromSide)->templateString)) {
				return true;
			}
		}
		return false;
	};

	const bool bothVars = tc.mode == TransitiveClosureNode::Mode::BothVars && seed == nullptr;
	// Walk direction: forward walks from -> to. A pairs closure is split along
	// whichever direction has single-hop arms (entry arms first: their `from`
	// meets no `to`, as addresses below a region hierarchy).
	bool forward = seed != nullptr ? seed->onFrom : tc.mode != TransitiveClosureNode::Mode::BackwardFromObject;
	if (bothVars) {
		bool anyEntry = false;
		bool anyExit = false;
		for (const auto &a : arms) {
			anyEntry = anyEntry || !meets(a, /*fromSide=*/true);
			anyExit = anyExit || !meets(a, /*fromSide=*/false);
		}
		if (!anyEntry && !anyExit) {
			return std::string();
		}
		forward = !anyEntry; // entry arms are leaves when walking backward
	}
	// Walking end / landing end of an arm in this direction.
	auto walk = [&](const ClosureArm &a) {
		return forward ? a.from : a.to;
	};
	auto land = [&](const ClosureArm &a) {
		return forward ? a.to : a.from;
	};

	std::vector<ClosureArm> core;
	std::vector<ClosureArm> leaf;  // lands where no arm walks: last hop only
	std::vector<ClosureArm> start; // walks where no arm lands: first hop only (and not a leaf)
	for (const auto &a : arms) {
		const bool isLeaf = !meets(a, /*fromSide=*/!forward);
		const bool isStart = !meets(a, /*fromSide=*/forward);
		if (isLeaf) {
			leaf.push_back(a);
		} else if (isStart) {
			start.push_back(a);
		} else {
			core.push_back(a);
		}
	}
	if (leaf.empty() && start.empty() && seed == nullptr) {
		return std::string();
	}
	if (bothVars && !start.empty()) {
		return std::string(); // a pairs closure is split on leaf arms only
	}

	// Core node keys: the template placeholders, when every core arm's two ends
	// share core[0]'s landing shape over comparable columns.
	const ColumnInfo *ref = core.empty() ? nullptr : land(core[0]);
	std::size_t nKeys = 0;
	if (ref != nullptr) {
		nKeys = nativeKeyPairs(*ref, *ref, catalog).size();
		for (const auto &a : core) {
			if (nativeKeyPairs(*a.from, *ref, catalog).size() != nKeys ||
			    nativeKeyPairs(*a.to, *ref, catalog).size() != nKeys) {
				nKeys = 0;
				break;
			}
		}
	}
	// Seeds landing from start arms must land in the core's key space too.
	if (nKeys > 0) {
		for (const auto &a : start) {
			if (nativeKeyPairs(*land(a), *ref, catalog).size() != nKeys) {
				nKeys = 0;
			}
		}
	}
	auto keyName = [&](const std::string &prefix, std::size_t i) {
		return dialect.quoteIdentifier(prefix + std::to_string(i));
	};
	// "<ref0> AS k0, ..." for one end of an arm, in its own scope.
	auto keyCols = [&](const ColumnInfo &c, const std::string &prefix) {
		std::vector<std::string> cols;
		if (nKeys == 0) {
			return cols;
		}
		for (const auto &p : nativeKeyPairs(c, *ref, catalog)) {
			cols.push_back(p.leftRef + " AS " + keyName(prefix, cols.size()));
		}
		return cols;
	};
	// Join one arm end (own scope) to a closure node row `alias` with key prefix
	// `prefix` (or its IRI column `iriCol`).
	auto nodeJoin = [&](const ColumnInfo &c, const std::string &alias, const std::string &prefix,
	                    const std::string &iriCol) {
		std::vector<NativeKeyPair> pairs = nKeys > 0 ? nativeKeyPairs(c, *ref, catalog) : std::vector<NativeKeyPair>();
		if (pairs.size() != nKeys || nKeys == 0) {
			return c.renderedExpr + " = " + alias + "." + iriCol;
		}
		std::string cond;
		for (std::size_t i = 0; i < pairs.size(); ++i) {
			cond += (i > 0 ? " AND " : "") + pairs[i].leftRef + " = " + alias + "." + keyName(prefix, i);
		}
		return cond;
	};
	auto unionOf = [](const std::vector<std::string> &parts) {
		std::string sql;
		for (std::size_t i = 0; i < parts.size(); ++i) {
			sql += (i > 0 ? " UNION " : "") + std::string("(") + parts[i] + ")";
		}
		return sql;
	};

	// Whether arm `a`'s first hop can start from a seed value at all.
	auto seedCanMeet = [&](const ClosureArm &a) {
		return seed == nullptr || seed->col == nullptr || seed->col->templateString.empty() ||
		       templatesCanEverMatch(walk(a)->templateString, seed->col->templateString);
	};
	const std::string node = dialect.quoteIdentifier("cte_node");
	const std::string sFrom = dialect.quoteIdentifier("s_from");
	const std::string sTo = dialect.quoteIdentifier("s_to");

	// The core step: both ends' IRIs, and their keys (kf/kt) when keyed.
	std::string coreCte;
	if (!core.empty()) {
		std::vector<std::string> parts;
		for (const auto &a : core) {
			std::vector<std::string> cols = {a.from->renderedExpr + " AS " + sFrom, a.to->renderedExpr + " AS " + sTo};
			for (auto &k : keyCols(*a.from, "kf")) {
				cols.push_back(k);
			}
			for (auto &k : keyCols(*a.to, "kt")) {
				cols.push_back(k);
			}
			parts.push_back(armSelect(*a.arm, cols, "", {}));
		}
		coreCte = ctx.nextCteName();
		std::string sql;
		for (std::size_t i = 0; i < parts.size(); ++i) {
			sql += (i > 0 ? " UNION ALL " : "") + std::string("(") + parts[i] + ")";
		}
		ctx.addCte(coreCte, sql);
	}
	const std::string walkCol = forward ? sFrom : sTo;
	const std::string landCol = forward ? sTo : sFrom;
	const std::string walkKey = forward ? "kf" : "kt";
	const std::string landKey = forward ? "kt" : "kf";
	auto carried = [&](const std::string &alias, const std::string &prefix, bool rename) {
		std::string out;
		for (std::size_t i = 0; i < nKeys; ++i) {
			out += ", " + alias + "." + keyName(prefix, i) + (rename ? " AS " + keyName("k", i) : "");
		}
		return out;
	};
	auto coreHop = [&](const std::string &acc, const std::string &step) {
		if (nKeys == 0) {
			return acc + "." + node + " = " + step + "." + walkCol;
		}
		std::string cond;
		for (std::size_t i = 0; i < nKeys; ++i) {
			cond += (i > 0 ? " AND " : "") + acc + "." + keyName("k", i) + " = " + step + "." + keyName(walkKey, i);
		}
		return cond;
	};

	if (!bothVars && seed != nullptr && !seed->keyCols.empty() && nKeys > 0) {
		// A seeded closure over keys: carry the start's raw columns (s0..) and the
		// node's (k0..) through the recursion instead of their IRI text, build the
		// reached node's IRI once at the end, and hand the start keys to the join
		// (as sk0.., the partner CTE's names), which takes the start term from the
		// partner. Applies when every first hop meets the seed on raw columns and
		// every leaf arm walks from the core's key space.
		const std::size_t nSeed = seed->keyCols.size();
		bool keyed = true;
		for (const auto *group : {&core, &start, &leaf}) {
			for (const auto &a : *group) {
				keyed = keyed && (!seedCanMeet(a) || nativeKeyPairs(*walk(a), *seed->col, catalog).size() == nSeed);
			}
		}
		for (const auto &a : leaf) {
			keyed = keyed && nativeKeyPairs(*walk(a), *ref, catalog).size() == nKeys;
		}
		if (keyed) {
			auto sCol = [&](std::size_t i) {
				return keyName("s", i);
			};
			auto skCol = [&](std::size_t i) {
				return dialect.quoteIdentifier("sk_" + std::to_string(i));
			};
			std::string seedSrc = "(SELECT DISTINCT ";
			for (std::size_t i = 0; i < nSeed; ++i) {
				seedSrc += (i > 0 ? ", " : "") + seed->keyCols[i];
			}
			seedSrc += " FROM " + seed->cte + ")";
			// One first hop of arm `a`: the seed's columns, `landCols`, the raw join.
			auto firstHop = [&](const ClosureArm &a, const std::vector<std::string> &landCols) {
				const std::string sd = ctx.nextAlias();
				std::vector<NativeKeyPair> pairs = nativeKeyPairs(*walk(a), *seed->col, catalog);
				std::vector<std::string> cols;
				std::string cond;
				for (std::size_t i = 0; i < nSeed; ++i) {
					cols.push_back(sd + "." + seed->keyCols[i] + " AS " + sCol(i));
					cond += (i > 0 ? " AND " : "") + pairs[i].leftRef + " = " + sd + "." + seed->keyCols[i];
				}
				cols.insert(cols.end(), landCols.begin(), landCols.end());
				return armSelect(*a.arm, cols, seedSrc + " AS " + sd, {cond});
			};
			std::vector<std::string> seeds;
			for (const auto *group : {&core, &start}) {
				for (const auto &a : *group) {
					if (seedCanMeet(a)) {
						seeds.push_back(firstHop(a, keyCols(*land(a), "k")));
					}
				}
			}
			std::string sCarry;
			for (std::size_t i = 0; i < nSeed; ++i) {
				sCarry += "%A%." + sCol(i) + ", ";
			}
			auto carryS = [&](const std::string &alias) {
				std::string out = sCarry;
				for (std::size_t pos = out.find("%A%"); pos != std::string::npos; pos = out.find("%A%", pos)) {
					out.replace(pos, 3, alias);
				}
				return out;
			};
			std::vector<std::string> nodes;
			std::string closureCte;
			if (!seeds.empty()) {
				closureCte = ctx.nextCteName();
				std::string r = ctx.nextAlias();
				std::string st = ctx.nextAlias();
				std::string recursive;
				if (!core.empty()) {
					std::string landKeys;
					for (std::size_t i = 0; i < nKeys; ++i) {
						landKeys += (i > 0 ? ", " : "") + st + "." + keyName(landKey, i);
					}
					recursive = " UNION SELECT " + carryS(r) + landKeys + " FROM " + closureCte + " AS " + r +
					            " JOIN " + coreCte + " AS " + st + " ON " + coreHop(r, st);
				}
				ctx.addCte(closureCte, "SELECT * FROM (" + unionOf(seeds) + ")" + recursive);
				// The reached node's IRI, built from its keys.
				const std::string c = ctx.nextAlias();
				std::string iri = ref->renderedExpr;
				for (std::size_t i = 0; i < nKeys; ++i) {
					iri = replaceRef(iri, ref->templateColumnRefs[i], c + "." + keyName("k", i));
				}
				nodes.push_back("SELECT " + carryS(c) + iri + " AS " + node + " FROM " + closureCte + " AS " + c);
			}
			for (const auto &a : leaf) {
				const std::vector<std::string> cols = {land(a)->renderedExpr + " AS " + node};
				if (seedCanMeet(a)) {
					nodes.push_back(firstHop(a, cols));
				}
				if (!closureCte.empty()) {
					const std::string c = ctx.nextAlias();
					std::vector<std::string> leafCols;
					for (std::size_t i = 0; i < nSeed; ++i) {
						leafCols.push_back(c + "." + sCol(i));
					}
					leafCols.push_back(cols[0]);
					nodes.push_back(
					    armSelect(*a.arm, leafCols, closureCte + " AS " + c, {nodeJoin(*walk(a), c, "k", node)}));
				}
			}
			if (nodes.empty()) {
				// No arm can start from a seed value: no pairs.
				std::string none = "SELECT ";
				for (std::size_t i = 0; i < nSeed; ++i) {
					none += "NULL AS " + sCol(i) + ", ";
				}
				nodes.push_back(none + "CAST(NULL AS VARCHAR) AS " + node + " WHERE FALSE");
			}
			if (outKeys != nullptr) {
				*outKeys = nSeed;
			}
			// The start end's term comes from the partner; its column here is a
			// placeholder (the join never reads it).
			const std::string c = ctx.nextAlias();
			const ColumnInfo &fromInfo = tc.schema()[0];
			const ColumnInfo &toInfo = tc.schema()[1];
			const ColumnInfo &startInfo = seed->onFrom ? fromInfo : toInfo;
			const ColumnInfo &nodeInfo = seed->onFrom ? toInfo : fromInfo;
			std::string sql = "SELECT CAST(NULL AS VARCHAR) AS " + mangleVar(startInfo.var, dialect) +
			                  closureTagProjection(startInfo, ctx) + ", " + c + "." + node + " AS " +
			                  mangleVar(nodeInfo.var, dialect) + closureTagProjection(nodeInfo, ctx);
			for (std::size_t i = 0; i < nSeed; ++i) {
				sql += ", " + c + "." + sCol(i) + " AS " + skCol(i);
			}
			return sql + " FROM (" + unionOf(nodes) + ") AS " + c;
		}
	}
	if (!bothVars) {
		// A seeded closure carries its start node through every hop.
		const std::string startCol = dialect.quoteIdentifier("cte_start");
		std::string seedSrc;
		if (seed != nullptr) {
			seedSrc = "(SELECT DISTINCT " + seed->iriCol;
			for (const auto &k : seed->keyCols) {
				seedSrc += ", " + k;
			}
			seedSrc += " FROM " + seed->cte + ")";
		}
		// The first hop of arm `a`: its extra FROM item, its condition and the
		// start column, from the anchor (raw columns) or from the seed set.
		struct FirstHop {
			std::string from;
			std::string cond;
			std::string startExpr;
		};
		auto firstHop = [&](const ClosureArm &a) {
			FirstHop h;
			if (seed == nullptr) {
				h.cond = anchorCondition(*walk(a), tc.anchorLiteral, dialect);
				return h;
			}
			const std::string sd = ctx.nextAlias();
			h.from = seedSrc + " AS " + sd;
			h.startExpr = sd + "." + seed->iriCol + " AS " + startCol;
			std::vector<NativeKeyPair> pairs = seed->col != nullptr && !seed->keyCols.empty()
			                                       ? nativeKeyPairs(*walk(a), *seed->col, catalog)
			                                       : std::vector<NativeKeyPair>();
			if (!pairs.empty() && pairs.size() == seed->keyCols.size()) {
				for (std::size_t i = 0; i < pairs.size(); ++i) {
					h.cond += (i > 0 ? " AND " : "") + pairs[i].leftRef + " = " + sd + "." + seed->keyCols[i];
				}
			} else {
				h.cond = walk(a)->renderedExpr + " = " + sd + "." + seed->iriCol;
			}
			return h;
		};
		auto withStart = [&](const FirstHop &h, std::vector<std::string> cols) {
			if (!h.startExpr.empty()) {
				cols.insert(cols.begin(), h.startExpr);
			}
			return cols;
		};
		const std::string startCarry = seed != nullptr ? "%A%." + startCol + ", " : "";
		auto carryStart = [&](const std::string &alias) {
			std::string out = startCarry;
			std::size_t pos = out.find("%A%");
			if (pos != std::string::npos) {
				out.replace(pos, 3, alias);
			}
			return out;
		};

		// Seeds: one hop from the anchor over core and start arms, on raw columns.
		std::vector<std::string> seeds;
		for (const auto *group : {&core, &start}) {
			for (const auto &a : *group) {
				if (!seedCanMeet(a)) {
					continue;
				}
				std::vector<std::string> cols = {land(a)->renderedExpr + " AS " + node};
				for (auto &k : keyCols(*land(a), "k")) {
					cols.push_back(k);
				}
				FirstHop h = firstHop(a);
				seeds.push_back(armSelect(*a.arm, withStart(h, cols), h.from, {h.cond}));
			}
		}
		std::vector<std::string> nodes;
		std::string closureCte;
		if (!seeds.empty()) {
			closureCte = ctx.nextCteName();
			std::string r = ctx.nextAlias();
			std::string s = ctx.nextAlias();
			std::string recursive;
			if (!core.empty()) {
				recursive = " UNION SELECT " + carryStart(r) + s + "." + landCol + carried(s, landKey, false) +
				            " FROM " + closureCte + " AS " + r + " JOIN " + coreCte + " AS " + s + " ON " +
				            coreHop(r, s);
			}
			ctx.addCte(closureCte, "SELECT * FROM (" + unionOf(seeds) + ")" + recursive);
		}

		// Output restriction (see the function comment): which parts can meet
		// the partner, and whether they all carry its raw key columns.
		auto canMeet = [&](const ColumnInfo *c) {
			return outCol == nullptr || outCol->templateString.empty() ||
			       templatesCanEverMatch(c->templateString, outCol->templateString);
		};
		bool closureNodesOut = closureCte.empty() ? false : outCol == nullptr;
		for (const auto *group : {&core, &start}) {
			for (const auto &a : *group) {
				closureNodesOut = closureNodesOut || (!closureCte.empty() && canMeet(land(a)));
			}
		}
		std::size_t nOut = 0;
		if (outCol != nullptr && outKeys != nullptr && seed == nullptr && outCol->prov == Provenance::TemplateExpr &&
		    !outCol->templateColumnRefs.empty()) {
			nOut = outCol->templateColumnRefs.size();
			if (closureNodesOut && (nKeys == 0 || nativeKeyPairs(*ref, *outCol, catalog).size() != nOut)) {
				nOut = 0;
			}
			for (const auto &a : leaf) {
				if (canMeet(land(a)) && nativeKeyPairs(*land(a), *outCol, catalog).size() != nOut) {
					nOut = 0;
				}
			}
		}
		auto outKeyName = [&](std::size_t i) {
			return dialect.quoteIdentifier("ok_" + std::to_string(i));
		};
		if (closureNodesOut) {
			std::string cols = carryStart(closureCte) + node;
			for (std::size_t i = 0; i < nOut; ++i) {
				cols += ", " + closureCte + "." + keyName("k", i) + " AS " + outKeyName(i);
			}
			nodes.push_back("SELECT " + cols + " FROM " + closureCte);
		}
		// Leaf arms: from the anchor directly, and from every node reached.
		for (const auto &a : leaf) {
			if (!canMeet(land(a))) {
				continue;
			}
			std::vector<std::string> cols = {land(a)->renderedExpr + " AS " + node};
			if (nOut > 0) {
				std::vector<NativeKeyPair> pairs = nativeKeyPairs(*land(a), *outCol, catalog);
				for (std::size_t i = 0; i < nOut; ++i) {
					cols.push_back(pairs[i].leftRef + " AS " + outKeyName(i));
				}
			}
			if (seedCanMeet(a)) {
				FirstHop h = firstHop(a);
				nodes.push_back(armSelect(*a.arm, withStart(h, cols), h.from, {h.cond}));
			}
			if (!closureCte.empty() && seed == nullptr) {
				// A semi-join: the closure is the small side, and IN makes it the
				// hash side whatever the engine estimates for a recursive CTE.
				std::vector<NativeKeyPair> pairs =
				    nKeys > 0 ? nativeKeyPairs(*walk(a), *ref, catalog) : std::vector<NativeKeyPair>();
				std::string lhs;
				std::string rhs;
				if (nKeys > 0 && pairs.size() == nKeys) {
					for (std::size_t i = 0; i < nKeys; ++i) {
						lhs += (i > 0 ? ", " : "") + pairs[i].leftRef;
						rhs += (i > 0 ? ", " : "") + keyName("k", i);
					}
				} else {
					lhs = walk(a)->renderedExpr;
					rhs = node;
				}
				if (nKeys > 1 && pairs.size() == nKeys) {
					lhs = "(" + lhs + ")";
				}
				nodes.push_back(
				    armSelect(*a.arm, cols, "", {lhs + " IN (SELECT " + rhs + " FROM " + closureCte + ")"}));
			} else if (!closureCte.empty()) {
				std::string c = ctx.nextAlias();
				std::vector<std::string> leafCols = cols;
				leafCols.insert(leafCols.begin(), c + "." + startCol);
				nodes.push_back(
				    armSelect(*a.arm, leafCols, closureCte + " AS " + c, {nodeJoin(*walk(a), c, "k", node)}));
			}
		}
		if (nodes.empty()) {
			// Nothing the partner can meet (or no arm starts from a seed value): an
			// empty relation of the right shape.
			nodes.push_back("SELECT " +
			                std::string(seed != nullptr ? "CAST(NULL AS VARCHAR) AS " + startCol + ", " : "") +
			                "CAST(NULL AS VARCHAR) AS " + node + " WHERE FALSE");
			nOut = 0;
		}
		if (outKeys != nullptr) {
			*outKeys = nOut;
		}
		const std::string all = unionOf(nodes);
		if (seed != nullptr) {
			std::string c = ctx.nextAlias();
			const ColumnInfo &fromInfo = tc.schema()[0];
			const ColumnInfo &toInfo = tc.schema()[1];
			const std::string fromExpr = c + "." + (seed->onFrom ? startCol : node);
			const std::string toExpr = c + "." + (seed->onFrom ? node : startCol);
			return "SELECT " + fromExpr + " AS " + mangleVar(fromInfo.var, dialect) +
			       closureTagProjection(fromInfo, ctx) + ", " + toExpr + " AS " + mangleVar(toInfo.var, dialect) +
			       closureTagProjection(toInfo, ctx) + " FROM (" + all + ") AS " + c;
		}
		if (tc.mode == TransitiveClosureNode::Mode::BothBound) {
			return "SELECT 1 AS " + dialect.quoteIdentifier("_dummy") + " WHERE " +
			       dialect.existsClause(false, "SELECT 1 FROM (" + all + ") AS " + ctx.nextAlias() + " WHERE " + node +
			                                       " = " + tc.targetLiteral);
		}
		std::string c = ctx.nextAlias();
		std::string outKeyCols;
		for (std::size_t i = 0; i < nOut; ++i) {
			outKeyCols += ", " + c + "." + outKeyName(i);
		}
		return "SELECT " + c + "." + node + " AS " + mangleVar(tc.schema()[0].var, dialect) +
		       closureTagProjection(tc.schema()[0], ctx) + outKeyCols + " FROM (" + all + ") AS " + c;
	}

	// Pairs closure, split on leaf arms (entry arms when walking backward, exit
	// arms when walking forward): core+ u leaf u (core+ joined to leaf).
	const std::string cFrom = dialect.quoteIdentifier("cte_from");
	const std::string cTo = dialect.quoteIdentifier("cte_to");
	std::vector<std::string> pairs;
	if (!core.empty()) {
		// Core pairs closure, carrying both ends' keys when keyed.
		std::string pairsCte = ctx.nextCteName();
		std::string s1 = ctx.nextAlias();
		std::string s2 = ctx.nextAlias();
		std::string r = ctx.nextAlias();
		std::string seed = "SELECT " + s1 + "." + sFrom + " AS " + cFrom + ", " + s1 + "." + sTo + " AS " + cTo;
		std::string rec = "SELECT " + r + "." + cFrom + ", " + s2 + "." + sTo;
		for (std::size_t i = 0; i < nKeys; ++i) {
			seed += ", " + s1 + "." + keyName("kf", i) + " AS " + keyName("pf", i) + ", " + s1 + "." +
			        keyName("kt", i) + " AS " + keyName("pt", i);
			rec += ", " + r + "." + keyName("pf", i) + ", " + s2 + "." + keyName("kt", i);
		}
		std::string hop;
		for (std::size_t i = 0; i < nKeys; ++i) {
			hop += (i > 0 ? " AND " : "") + r + "." + keyName("pt", i) + " = " + s2 + "." + keyName("kf", i);
		}
		if (nKeys == 0) {
			hop = r + "." + cTo + " = " + s2 + "." + sFrom;
		}
		ctx.addCte(pairsCte, seed + " FROM " + coreCte + " AS " + s1 + " UNION " + rec + " FROM " + pairsCte + " AS " +
		                         r + " JOIN " + coreCte + " AS " + s2 + " ON " + hop);
		pairs.push_back("SELECT " + cFrom + ", " + cTo + " FROM " + pairsCte);
		// Leaf arm then core path (entry arms, backward) or core path then leaf
		// arm (exit arms, forward).
		for (const auto &a : leaf) {
			std::string c = ctx.nextAlias();
			if (!forward) {
				pairs.push_back(armSelect(*a.arm, {a.from->renderedExpr + " AS " + cFrom, c + "." + cTo},
				                          pairsCte + " AS " + c, {nodeJoin(*a.to, c, "pf", cFrom)}));
			} else {
				pairs.push_back(armSelect(*a.arm, {c + "." + cFrom, a.to->renderedExpr + " AS " + cTo},
				                          pairsCte + " AS " + c, {nodeJoin(*a.from, c, "pt", cTo)}));
			}
		}
	}
	for (const auto &a : leaf) {
		pairs.push_back(
		    armSelect(*a.arm, {a.from->renderedExpr + " AS " + cFrom, a.to->renderedExpr + " AS " + cTo}, "", {}));
	}
	std::string c = ctx.nextAlias();
	return "SELECT " + c + "." + cFrom + " AS " + mangleVar(tc.schema()[0].var, dialect) +
	       closureTagProjection(tc.schema()[0], ctx) + ", " + c + "." + cTo + " AS " +
	       mangleVar(tc.schema()[1].var, dialect) + closureTagProjection(tc.schema()[1], ctx) + " FROM (" +
	       unionOf(pairs) + ") AS " + c;
}

// E+ closure rendering. Registers two CTEs on `ctx` (the one-hop step
// relation, then the recursive closure over it - never inlining step's SQL
// twice, since both the seed and the recursive term reference it) and
// returns a bare "SELECT ... FROM <closureCte> ..." reference, analogous to
// how RawRelation returns its pre-rendered sql verbatim.
//
// Two shapes, chosen by tc.mode:
//  - BothVars: a full (from, to) pairs closure - the seed is every one-hop
//    edge, the recursive term extends a known pair by one more hop. This is
//    the only shape that needs both endpoint columns; the other three anchor
//    at a bound literal and only need a unary "reachable node" column, which
//    is far cheaper.
//  - ForwardFromSubject/BackwardFromObject/BothBound: seed from the bound
//    endpoint's literal and walk the step relation forward or backward one
//    hop at a time. BothBound projects nothing and tests membership via
//    EXISTS instead, mirroring zeroLengthPath's both-bound-unequal Empty
//    shape (0 columns, existence only).
//
// Every recursive term is combined with its seed via a deduplicating UNION
// (never UNION ALL): this is what makes the closure terminate on cyclic edge
// data, which real graphs frequently have.
std::string renderTransitiveClosure(const TransitiveClosureNode &tc, TranslationContext &ctx,
                                    const ExtraProjections *extra) {
	if (extra == nullptr) {
		std::string split = renderSplitClosure(tc, ctx, nullptr);
		if (!split.empty()) {
			return split;
		}
	}
	const SqlDialect &dialect = ctx.dialect();
	std::string fromCol = mangleVar(tc.fromVar, dialect);
	std::string toCol = mangleVar(tc.toVar, dialect);

	// Raw-key recursion (see closureKeyPairs): the step projects each
	// endpoint's placeholder columns as k_f<i>/k_t<i> beside the IRIs, the
	// closure carries the reached node's keys beside its IRI, and every hop
	// joins on keys. The IRI still rides along, so the anchor and target
	// comparisons and the output column are unchanged; it is a function of
	// the keys, so the deduplicating UNION keeps exactly the rows it did.
	const std::vector<NativeKeyPair> keyPairs = closureKeyPairs(tc, ctx.catalog());
	const std::size_t nKeys = keyPairs.size();
	auto stepKey = [&](bool fromSide, std::size_t i) {
		return closureKeyName(fromSide ? "k_f" : "k_t", i, dialect);
	};

	std::string stepCte = ctx.nextCteName();
	if (nKeys == 0) {
		ctx.addCte(stepCte, renderNode(*tc.step, ctx));
	} else {
		ExtraProjections stepExtra;
		for (std::size_t i = 0; i < nKeys; ++i) {
			stepExtra.emplace_back(stepKey(true, i), keyPairs[i].leftRef);
			stepExtra.emplace_back(stepKey(false, i), keyPairs[i].rightRef);
		}
		ctx.addCte(stepCte, renderSpj(static_cast<const SpjRelation &>(*tc.step), ctx, &stepExtra));
	}
	std::string closureCte = ctx.nextCteName();

	// Hidden projections a parent join asked for (planNativeKeys): bare key
	// column names of this closure's CTE, the only source of the final SELECT.
	std::string extraProject;
	if (extra != nullptr) {
		for (const auto &e : *extra) {
			extraProject += ", " + e.second + " AS " + e.first;
		}
	}

	// Invariant columns (see TransitiveClosureNode::invariantVars) keep their
	// own mangled names all the way through - unlike the endpoints, which are
	// renamed to cte_from/cte_to/cte_node because the step relation names them
	// after internal path variables. Held constant per hop by an added ON
	// equality rather than walked.
	std::string invSeed;      // ", <alias>.v_g AS v_g" for the seed term
	std::string invRecursive; // ", <accumulator>.v_g" for the recursive term
	std::string invProject;   // ", <c>.v_g AS v_g" for the final projection
	for (const auto &var : tc.invariantVars) {
		const std::string col = mangleVar(var, dialect);
		invSeed += ", %SEED%." + col + " AS " + col;
		invRecursive += ", %ACC%." + col;
		const ColumnInfo *info = tc.column(var);
		invProject += ", %C%." + col + " AS " + col + (info != nullptr ? closureTagProjection(*info, ctx) : "");
	}
	auto invOn = [&](const std::string &acc, const std::string &step) -> std::string {
		std::string on;
		for (const auto &var : tc.invariantVars) {
			const std::string col = mangleVar(var, dialect);
			on += " AND " + acc + "." + col + " = " + step + "." + col;
		}
		return on;
	};
	auto subst = [](std::string text, const std::string &token, const std::string &value) -> std::string {
		std::size_t pos = 0;
		while ((pos = text.find(token, pos)) != std::string::npos) {
			text.replace(pos, token.size(), value);
			pos += value.size();
		}
		return text;
	};
	// ", a.<k_t0> AS <cte_k0>, ..." / ", a.<k_t0>, ..." / "a.<cte_k0> = b.<k_f0> AND ...".
	auto keyList = [&](const std::string &alias, bool fromSide, const std::string &asPrefix) {
		std::string out;
		for (std::size_t i = 0; i < nKeys; ++i) {
			out += ", " + alias + "." + stepKey(fromSide, i);
			if (!asPrefix.empty()) {
				out += " AS " + closureKeyName(asPrefix, i, dialect);
			}
		}
		return out;
	};
	auto keyOn = [&](const std::string &acc, const std::string &accPrefix, const std::string &step, bool fromSide) {
		std::string on;
		for (std::size_t i = 0; i < nKeys; ++i) {
			on += (i > 0 ? " AND " : "") + acc + "." + closureKeyName(accPrefix, i, dialect) + " = " + step + "." +
			      stepKey(fromSide, i);
		}
		return on;
	};

	if (tc.mode == TransitiveClosureNode::Mode::BothVars) {
		std::string cteFrom = dialect.quoteIdentifier("cte_from");
		std::string cteTo = dialect.quoteIdentifier("cte_to");
		std::string s1 = ctx.nextAlias();
		std::string s2 = ctx.nextAlias();
		std::string r = ctx.nextAlias();
		std::string seed = "SELECT " + s1 + "." + fromCol + " AS " + cteFrom + ", " + s1 + "." + toCol + " AS " +
		                   cteTo + keyList(s1, true, "cte_fk") + keyList(s1, false, "cte_tk") +
		                   subst(invSeed, "%SEED%", s1) + " FROM " + stepCte + " AS " + s1;
		std::string carriedFromKeys;
		for (std::size_t i = 0; i < nKeys; ++i) {
			carriedFromKeys += ", " + r + "." + closureKeyName("cte_fk", i, dialect);
		}
		std::string hop = nKeys == 0 ? r + "." + cteTo + " = " + s2 + "." + fromCol : keyOn(r, "cte_tk", s2, true);
		std::string recursive = "SELECT " + r + "." + cteFrom + ", " + s2 + "." + toCol + carriedFromKeys +
		                        keyList(s2, false, "") + subst(invRecursive, "%ACC%", r) + " FROM " + closureCte +
		                        " AS " + r + " JOIN " + stepCte + " AS " + s2 + " ON " + hop + invOn(r, s2);
		ctx.addCte(closureCte, seed + " UNION " + recursive);

		std::string c = ctx.nextAlias();
		if (tc.sameEndpointVar) {
			// Subject and object share one variable (`?x p+ ?x`): only the
			// diagonal of the pairs closure satisfies the pattern.
			return "SELECT " + c + "." + cteFrom + " AS " + mangleVar(tc.schema()[0].var, dialect) +
			       closureTagProjection(tc.schema()[0], ctx) + subst(invProject, "%C%", c) + extraProject + " FROM " +
			       closureCte + " AS " + c + " WHERE " + c + "." + cteFrom + " = " + c + "." + cteTo;
		}
		return "SELECT " + c + "." + cteFrom + " AS " + mangleVar(tc.schema()[0].var, dialect) +
		       closureTagProjection(tc.schema()[0], ctx) + ", " + c + "." + cteTo + " AS " +
		       mangleVar(tc.schema()[1].var, dialect) + closureTagProjection(tc.schema()[1], ctx) +
		       subst(invProject, "%C%", c) + extraProject + " FROM " + closureCte + " AS " + c;
	}

	// Unary reachable-set: ForwardFromSubject/BackwardFromObject walk the
	// step relation in the direction that starts at the bound endpoint;
	// BothBound reuses the forward walk (seeded from the subject) and only
	// tests membership.
	std::string cteNode = dialect.quoteIdentifier("cte_node");
	bool forward = tc.mode != TransitiveClosureNode::Mode::BackwardFromObject;
	const std::string &walkCol = forward ? fromCol : toCol;
	const std::string &landCol = forward ? toCol : fromCol;

	std::string seedAlias = ctx.nextAlias();
	std::string s = ctx.nextAlias();
	std::string r = ctx.nextAlias();
	// One hop from the anchor, not the anchor itself: this node's minimum
	// cardinality is always 1 (see class comment), so seeding with the anchor
	// verbatim would wrongly include it as a zero-hop "reachable" result.
	std::string seed = "SELECT " + seedAlias + "." + landCol + " AS " + cteNode +
	                   keyList(seedAlias, !forward, "cte_k") + subst(invSeed, "%SEED%", seedAlias) + " FROM " +
	                   stepCte + " AS " + seedAlias + " WHERE " + seedAlias + "." + walkCol + " = " + tc.anchorLiteral;
	std::string hop = nKeys == 0 ? r + "." + cteNode + " = " + s + "." + walkCol : keyOn(r, "cte_k", s, forward);
	std::string recursive = "SELECT " + s + "." + landCol + keyList(s, !forward, "") + subst(invRecursive, "%ACC%", r) +
	                        " FROM " + closureCte + " AS " + r + " JOIN " + stepCte + " AS " + s + " ON " + hop +
	                        invOn(r, s);
	ctx.addCte(closureCte, seed + " UNION " + recursive);

	if (tc.mode == TransitiveClosureNode::Mode::BothBound) {
		if (tc.invariantVars.empty()) {
			return "SELECT 1 AS " + dialect.quoteIdentifier("_dummy") + " WHERE " +
			       dialect.existsClause(false,
			                            "SELECT 1 FROM " + closureCte + " WHERE " + cteNode + " = " + tc.targetLiteral);
		}
		// With an invariant to bind (`GRAPH ?g { <a> :p+ <b> }`), this stops being
		// a pure existence check: the answer is *which* graphs connect the two
		// endpoints, so the graph must be projected rather than tested away.
		// DISTINCT because several paths through one graph are still one solution.
		std::string c = ctx.nextAlias();
		std::string projection = subst(invProject, "%C%", c);
		return "SELECT DISTINCT " + projection.substr(2) + " FROM " + closureCte + " AS " + c + " WHERE " + c + "." +
		       cteNode + " = " + tc.targetLiteral;
	}

	std::string c = ctx.nextAlias();
	return "SELECT " + c + "." + cteNode + " AS " + mangleVar(tc.schema()[0].var, dialect) +
	       closureTagProjection(tc.schema()[0], ctx) + subst(invProject, "%C%", c) + extraProject + " FROM " +
	       closureCte + " AS " + c;
}

// A Raw leaf's SQL was built during folding, before any tag was demanded, so it
// only carries the tag columns its producer could not have reconstructed later
// (providedTagVars). Every other demanded tag is a constant, so it is added here
// by wrapping - which costs nothing when nothing is demanded, the overwhelmingly
// common case, where this returns the pre-rendered SQL verbatim as it always
// did.
std::string renderRaw(const RawRelation &raw, TranslationContext &ctx) {
	const SqlDialect &dialect = ctx.dialect();
	std::string added;
	for (const auto &c : raw.schema()) {
		if (!ctx.needsTag(c.var) || raw.providedTagVars.count(c.var) != 0) {
			continue;
		}
		added += ", " + producedTag(c, "this inline-data or subquery relation") + " AS " + mangleVarTag(c.var, dialect);
	}
	if (added.empty()) {
		return raw.sql;
	}
	return "SELECT *" + added + ctx.clauseSep() + "FROM (" + raw.sql + ") AS " + ctx.nextAlias();
}

std::string renderEmpty(const EmptyNode &e, TranslationContext &ctx) {
	const SqlDialect &dialect = ctx.dialect();
	if (e.schema().empty()) {
		return "SELECT" + joinColumnList({"1 AS " + dialect.quoteIdentifier("_dummy")}, ctx) + ctx.clauseSep() +
		       "WHERE FALSE";
	}
	std::vector<std::string> cols;
	cols.reserve(e.schema().size() * 2);
	for (const auto &c : e.schema()) {
		cols.push_back("CAST(NULL AS VARCHAR) AS " + mangleVar(c.var, dialect));
		if (ctx.needsTag(c.var)) {
			// No rows, so no term: a NULL tag beside the NULL value is both the
			// only honest answer and the one the invariant requires.
			cols.push_back("CAST(NULL AS VARCHAR) AS " + mangleVarTag(c.var, dialect));
		}
	}
	return "SELECT" + joinColumnList(cols, ctx) + ctx.clauseSep() + "WHERE FALSE";
}

std::string renderNode(const RelNode &node, TranslationContext &ctx) {
	switch (node.kind()) {
	case RelKind::Spj:
		return renderSpj(static_cast<const SpjRelation &>(node), ctx, nullptr);
	case RelKind::Join:
		return renderJoin(static_cast<const JoinNode &>(node), ctx);
	case RelKind::AntiJoin:
		return renderAntiJoin(static_cast<const AntiJoinNode &>(node), ctx);
	case RelKind::UnionByName:
		return renderUnion(static_cast<const UnionByNameNode &>(node), ctx);
	case RelKind::Filter:
		return renderFilter(static_cast<const FilterNode &>(node), ctx);
	case RelKind::Bind:
		return renderBind(static_cast<const BindNode &>(node), ctx);
	case RelKind::Raw:
		return renderRaw(static_cast<const RawRelation &>(node), ctx);
	case RelKind::SingleRow:
		return "SELECT 1 AS " + ctx.dialect().quoteIdentifier("_dummy");
	case RelKind::Empty:
		return renderEmpty(static_cast<const EmptyNode &>(node), ctx);
	case RelKind::TransitiveClosure:
		return renderTransitiveClosure(static_cast<const TransitiveClosureNode &>(node), ctx, nullptr);
	}
	return std::string();
}

} // namespace

void fillScopeFromSchema(TranslatedPattern &out, const std::vector<ColumnInfo> &schema) {
	for (const auto &c : schema) {
		if (c.nonNull) {
			out.boundVars.insert(c.var);
		} else {
			out.optionalVars.insert(c.var);
		}
		if (c.term.kindKnown()) {
			// Only record what is actually known: an absent entry already reads
			// back as Unknown, so storing one saves nothing and invites a
			// consumer to distinguish "absent" from "present but Unknown".
			out.termInfo[c.var] = c.term;
		}
	}
}

TranslatedPattern renderRelation(const RelNode &node, TranslationContext &ctx) {
	TranslatedPattern tp;
	tp.sql = renderNode(node, ctx);
	fillScopeFromSchema(tp, node.schema());
	tp.isIdentity = (node.kind() == RelKind::SingleRow);
	return tp;
}

} // namespace sparql2sql

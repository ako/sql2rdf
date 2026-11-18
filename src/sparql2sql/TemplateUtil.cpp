#include "sparql2sql/TemplateUtil.h"

#include <algorithm>
#include <utility>
#include <vector>

#include "sparql2sql/SqlDialect.h"

namespace sparql2sql {

namespace {

bool startsWithAt(const std::string &haystack, std::size_t pos, const std::string &needle) {
	if (pos > haystack.size()) {
		return false;
	}
	return haystack.compare(pos, needle.size(), needle) == 0;
}
// TODO Merge with other implementation
bool isHexDigit(char c) {
	return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}

int hexVal(char c) {
	if (c >= '0' && c <= '9') {
		return c - '0';
	}
	if (c >= 'a' && c <= 'f') {
		return 10 + (c - 'a');
	}
	return 10 + (c - 'A');
}

} // namespace

std::vector<TemplateSegment> parseTemplate(const std::string &templateString) {
	std::vector<TemplateSegment> segments;
	segments.reserve(8); // rough guess to avoid too many reallocs
	std::string literalBuf;
	std::size_t i = 0;
	const std::size_t n = templateString.size();

	while (i < n) {
		if (templateString[i] == '{') {
			std::size_t end = templateString.find('}', i + 1);
			if (end == std::string::npos) {
				// Matches TemplateTermMap.cpp: an unmatched '{' truncates
				// the rest of the template rather than being treated as
				// literal text.
				break;
			}
			if (!literalBuf.empty()) {
				TemplateSegment seg;
				seg.isPlaceholder = false;
				seg.text = literalBuf;
				segments.push_back(seg);
				literalBuf.clear();
			}
			TemplateSegment seg;
			seg.isPlaceholder = true;
			seg.text = templateString.substr(i + 1, end - i - 1);
			segments.push_back(seg);
			i = end + 1;
		} else {
			literalBuf += templateString[i];
			++i;
		}
	}
	if (!literalBuf.empty()) {
		TemplateSegment seg;
		seg.isPlaceholder = false;
		seg.text = literalBuf;
		segments.push_back(seg);
	}
	return segments;
}

std::vector<std::string> referencedColumns(const std::vector<TemplateSegment> &segments) {
	std::vector<std::string> out;
	out.reserve(segments.size()); // rough guess to avoid too many reallocs
	for (const auto &seg : segments) {
		if (!seg.isPlaceholder) {
			continue;
		}
		bool seen = false;
		for (const auto &c : out) {
			if (c == seg.text) {
				seen = true;
				break;
			}
		}
		if (!seen) {
			out.push_back(seg.text);
		}
	}
	return out;
}

std::string buildProjectionSql(const std::vector<TemplateSegment> &segments, const std::string &sourceAlias,
                               const SqlDialect &dialect, bool percentEncodeValues) {
	if (segments.empty()) {
		return dialect.stringLiteral("");
	}
	std::vector<std::string> parts;
	parts.reserve(segments.size());
	for (const auto &seg : segments) {
		if (seg.isPlaceholder) {
			std::string columnExpr = "CAST(" + sourceAlias + "." + dialect.quoteIdentifier(seg.text) + " AS VARCHAR)";
			parts.push_back(percentEncodeValues ? dialect.percentEncode(columnExpr) : columnExpr);
		} else {
			parts.push_back(dialect.stringLiteral(seg.text));
		}
	}
	return dialect.concat(parts);
}

InversionOutcome invertTemplate(const std::vector<TemplateSegment> &segments, const std::string &boundValue,
                                bool percentDecodeValues) {
	InversionOutcome outcome;

	if (segments.empty()) {
		// An empty template only "matches" an empty bound value.
		if (boundValue.empty()) {
			outcome.kind = InversionKind::WholeTemplateMatch;
		} else {
			outcome.kind = InversionKind::NeverMatches;
		}
		return outcome;
	}

	bool canSplit = true;
	for (std::size_t i = 0; i + 1 < segments.size(); ++i) {
		if (segments[i].isPlaceholder && segments[i + 1].isPlaceholder) {
			canSplit = false;
			break;
		}
	}

	if (!canSplit) {
		// Still prune using the leading/trailing literal anchors, if any.
		if (!segments.front().isPlaceholder && !startsWithAt(boundValue, 0, segments.front().text)) {
			outcome.kind = InversionKind::NeverMatches;
			return outcome;
		}
		if (!segments.back().isPlaceholder) {
			const std::string &suffix = segments.back().text;
			if (boundValue.size() < suffix.size() ||
			    boundValue.compare(boundValue.size() - suffix.size(), suffix.size(), suffix) != 0) {
				outcome.kind = InversionKind::NeverMatches;
				return outcome;
			}
		}
		outcome.kind = InversionKind::WholeTemplateMatch;
		return outcome;
	}

	std::size_t pos = 0;
	for (std::size_t i = 0; i < segments.size(); ++i) {
		const TemplateSegment &seg = segments[i];
		if (!seg.isPlaceholder) {
			if (!startsWithAt(boundValue, pos, seg.text)) {
				outcome.kind = InversionKind::NeverMatches;
				return outcome;
			}
			pos += seg.text.size();
			continue;
		}

		// Placeholder: canSplit guarantees the next segment (if any) is
		// literal, so it's safe to search for it as this placeholder's
		// ending delimiter.
		std::string span;
		if (i + 1 < segments.size()) {
			const std::string &delimiter = segments[i + 1].text;
			std::size_t found = boundValue.find(delimiter, pos);
			if (found == std::string::npos) {
				outcome.kind = InversionKind::NeverMatches;
				return outcome;
			}
			span = boundValue.substr(pos, found - pos);
			pos = found;
		} else {
			span = boundValue.substr(pos);
			pos = boundValue.size();
		}
		outcome.columnValues.emplace_back(seg.text, percentDecodeValues ? percentDecode(span) : span);
	}

	if (pos != boundValue.size()) {
		// Trailing characters left over that the template never accounted
		// for.
		outcome.kind = InversionKind::NeverMatches;
		outcome.columnValues.clear();
		return outcome;
	}

	outcome.kind = InversionKind::PerColumnMatch;
	return outcome;
}

namespace {

bool literalPrefixesCompatible(const std::string &a, const std::string &b) {
	std::size_t n = std::min(a.size(), b.size());
	return a.compare(0, n, b, 0, n) == 0;
}

bool literalSuffixesCompatible(const std::string &a, const std::string &b) {
	std::size_t n = std::min(a.size(), b.size());
	return a.compare(a.size() - n, n, b, b.size() - n, n) == 0;
}

} // namespace

bool templatesCanEverMatch(const std::string &templateA, const std::string &templateB) {
	if (templateA == templateB) {
		return true;
	}

	std::vector<TemplateSegment> a = parseTemplate(templateA);
	std::vector<TemplateSegment> b = parseTemplate(templateB);
	if (a.empty() || b.empty()) {
		// One side is the literal empty string. The only conclusive case (both
		// fully literal and equal) was already handled above; anything else is
		// left unproven rather than risking a wrong prune.
		return true;
	}

	bool aLiteralOnly = true;
	for (const auto &seg : a) {
		if (seg.isPlaceholder) {
			aLiteralOnly = false;
			break;
		}
	}
	bool bLiteralOnly = true;
	for (const auto &seg : b) {
		if (seg.isPlaceholder) {
			bLiteralOnly = false;
			break;
		}
	}
	if (aLiteralOnly && bLiteralOnly) {
		return false; // both fully literal and, per the check above, not equal.
	}

	if (!a.front().isPlaceholder && !b.front().isPlaceholder &&
	    !literalPrefixesCompatible(a.front().text, b.front().text)) {
		return false;
	}
	if (!a.back().isPlaceholder && !b.back().isPlaceholder &&
	    !literalSuffixesCompatible(a.back().text, b.back().text)) {
		return false;
	}
	return true;
}

namespace {

// A template as a sequence of positions: a literal character, or a placeholder
// that matches any run (possibly empty) of characters from its alphabet.
struct TemplateItem {
	bool placeholder = false;
	unsigned char ch = 0;
};

std::vector<TemplateItem> templateItems(const std::string &tmpl) {
	std::vector<TemplateItem> items;
	for (const auto &seg : parseTemplate(tmpl)) {
		if (seg.isPlaceholder) {
			TemplateItem item;
			item.placeholder = true;
			items.push_back(item);
			continue;
		}
		for (char c : seg.text) {
			TemplateItem item;
			item.ch = static_cast<unsigned char>(c);
			items.push_back(item);
		}
	}
	return items;
}

// What a percent-encoded (IRI-safe) placeholder value can contain: the RFC 3986
// unreserved characters, '%' (from the escapes themselves), and - for R2RML
// 7.3, which leaves ucschar unencoded, unlike DuckDB's url_encode - any
// non-ASCII byte. A superset of what any conforming dialect emits, so a
// template pair proven disjoint over it is disjoint for real values too.
bool inEncodedAlphabet(unsigned char c) {
	return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '.' ||
	       c == '_' || c == '~' || c == '%' || c >= 0x80;
}

} // namespace

bool templatesCanEverMatch(const std::string &templateA, const std::string &templateB, bool aPercentEncoded,
                           bool bPercentEncoded) {
	if (templateA == templateB) {
		return true;
	}
	// Each template is a small automaton: state i sits before item i, a literal
	// item moves on its own character, a placeholder loops on any character of
	// its alphabet and may be left without consuming one. The two can produce a
	// common string exactly when the product of the two automata reaches both
	// end states - a decision, not an estimate, for the alphabets above.
	const std::vector<TemplateItem> a = templateItems(templateA);
	const std::vector<TemplateItem> b = templateItems(templateB);
	const std::size_t na = a.size();
	const std::size_t nb = b.size();
	auto accepts = [](const TemplateItem &item, bool encoded, unsigned char c) {
		return item.placeholder ? (!encoded || inEncodedAlphabet(c)) : item.ch == c;
	};

	// Characters worth trying: every literal character of either template, plus
	// one stand-in for all the characters that appear in neither - those differ
	// only in whether an encoded placeholder accepts them, so one from inside
	// and one from outside the encoded alphabet cover them all.
	std::vector<bool> inLiterals(256, false);
	for (const auto *items : {&a, &b}) {
		for (const auto &item : *items) {
			if (!item.placeholder) {
				inLiterals[item.ch] = true;
			}
		}
	}
	std::vector<unsigned char> alphabet;
	bool haveEncoded = false;
	bool haveOther = false;
	for (int c = 1; c < 256; ++c) {
		const auto uc = static_cast<unsigned char>(c);
		if (inLiterals[uc]) {
			alphabet.push_back(uc);
		} else if (inEncodedAlphabet(uc) ? !haveEncoded : !haveOther) {
			(inEncodedAlphabet(uc) ? haveEncoded : haveOther) = true;
			alphabet.push_back(uc);
		}
	}

	std::vector<bool> seen((na + 1) * (nb + 1), false);
	std::vector<std::pair<std::size_t, std::size_t>> work;
	auto visit = [&](std::size_t i, std::size_t j) {
		if (!seen[i * (nb + 1) + j]) {
			seen[i * (nb + 1) + j] = true;
			work.emplace_back(i, j);
		}
	};
	visit(0, 0);
	while (!work.empty()) {
		const std::size_t i = work.back().first;
		const std::size_t j = work.back().second;
		work.pop_back();
		if (i == na && j == nb) {
			return true;
		}
		// A placeholder may end without consuming anything.
		if (i < na && a[i].placeholder) {
			visit(i + 1, j);
		}
		if (j < nb && b[j].placeholder) {
			visit(i, j + 1);
		}
		if (i == na || j == nb) {
			continue; // one side is finished: no character can advance both.
		}
		for (unsigned char c : alphabet) {
			if (accepts(a[i], aPercentEncoded, c) && accepts(b[j], bPercentEncoded, c)) {
				// A placeholder stays put after consuming (it may consume more); a
				// literal moves on.
				visit(a[i].placeholder ? i : i + 1, b[j].placeholder ? j : j + 1);
			}
		}
	}
	return false;
}

bool sameTemplateShape(const std::string &templateA, const std::string &templateB) {
	if (templateA == templateB) {
		return true;
	}
	std::vector<TemplateSegment> a = parseTemplate(templateA);
	std::vector<TemplateSegment> b = parseTemplate(templateB);
	if (a.size() != b.size()) {
		return false;
	}
	// Canonicalize each side's placeholder names to their first-occurrence
	// index so a repeated placeholder ("{x}/{x}") only matches a template
	// that repeats a placeholder at the same positions ("{y}/{y}").
	std::vector<int> canonA, canonB;
	canonA.reserve(a.size());
	canonB.reserve(b.size());
	std::vector<std::string> seenA, seenB;
	for (const auto &seg : a) {
		if (!seg.isPlaceholder) {
			canonA.push_back(-1);
			continue;
		}
		auto it = std::find(seenA.begin(), seenA.end(), seg.text);
		if (it == seenA.end()) {
			canonA.push_back(static_cast<int>(seenA.size()));
			seenA.push_back(seg.text);
		} else {
			canonA.push_back(static_cast<int>(it - seenA.begin()));
		}
	}
	for (const auto &seg : b) {
		if (!seg.isPlaceholder) {
			canonB.push_back(-1);
			continue;
		}
		auto it = std::find(seenB.begin(), seenB.end(), seg.text);
		if (it == seenB.end()) {
			canonB.push_back(static_cast<int>(seenB.size()));
			seenB.push_back(seg.text);
		} else {
			canonB.push_back(static_cast<int>(it - seenB.begin()));
		}
	}
	for (std::size_t i = 0; i < a.size(); ++i) {
		if (a[i].isPlaceholder != b[i].isPlaceholder) {
			return false;
		}
		if (!a[i].isPlaceholder) {
			if (a[i].text != b[i].text) {
				return false;
			}
		} else if (canonA[i] != canonB[i]) {
			return false;
		}
	}
	return true;
}

std::string percentDecode(const std::string &value) {
	std::string out;
	out.reserve(value.size());
	for (std::size_t i = 0; i < value.size(); ++i) {
		if (value[i] == '%' && i + 2 < value.size() && isHexDigit(value[i + 1]) && isHexDigit(value[i + 2])) {
			out += static_cast<char>(hexVal(value[i + 1]) * 16 + hexVal(value[i + 2]));
			i += 2;
		} else {
			out += value[i];
		}
	}
	return out;
}

} // namespace sparql2sql

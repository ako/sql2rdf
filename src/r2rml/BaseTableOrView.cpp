#include "r2rml/BaseTableOrView.h"
#include "r2rml/SQLConnection.h"
#include "r2rml/SQLResultSet.h"

#include <ostream>

namespace r2rml {

BaseTableOrView::BaseTableOrView(const std::string &table) : tableName(table) {
}

BaseTableOrView::~BaseTableOrView() = default;

std::unique_ptr<SQLResultSet> BaseTableOrView::getRows(SQLConnection &dbConnection) {
	// Construct the effective SQL query for a base table or view.
	std::string query = "SELECT * FROM " + sqlName();
	effectiveSqlQuery = query;
	return dbConnection.execute(query);
}

std::vector<std::string> BaseTableOrView::getColumnNames() {
	return {};
}

std::vector<std::string> BaseTableOrView::splitQualifiedName(const std::string &name) {
	std::vector<std::string> parts;
	std::string part;
	bool delimited = false; // the current part was written "quoted"
	std::size_t i = 0;
	while (i <= name.size()) {
		if (i == name.size() || name[i] == '.') {
			if (part.empty() && !delimited) {
				return {name}; // an empty part: "a..b", ".a", "a."
			}
			parts.push_back(part);
			part.clear();
			delimited = false;
			++i;
			continue;
		}
		if (name[i] == '"' && part.empty() && !delimited) {
			// A delimited identifier: up to the closing quote, "" standing for ".
			std::size_t j = i + 1;
			bool closed = false;
			while (j < name.size()) {
				if (name[j] == '"') {
					if (j + 1 < name.size() && name[j + 1] == '"') {
						part += '"';
						j += 2;
						continue;
					}
					closed = true;
					break;
				}
				part += name[j++];
			}
			// It must close, and be followed by a '.' or the end.
			if (!closed || (j + 1 < name.size() && name[j + 1] != '.')) {
				return {name};
			}
			delimited = true;
			i = j + 1;
			continue;
		}
		if (delimited || name[i] == '"') {
			return {name}; // text after a closing quote, or a quote inside a regular identifier
		}
		part += name[i++];
	}
	return parts;
}

std::vector<std::string> BaseTableOrView::nameParts() const {
	return splitQualifiedName(tableName);
}

std::string BaseTableOrView::sqlName() const {
	std::string out;
	for (const auto &part : nameParts()) {
		out += out.empty() ? "\"" : ".\"";
		for (char c : part) {
			out += c;
			if (c == '"') {
				out += '"';
			}
		}
		out += '"';
	}
	return out;
}

std::ostream &BaseTableOrView::print(std::ostream &os) const {
	return os << "BaseTableOrView { tableName=\"" << tableName << "\" }";
}

} // namespace r2rml

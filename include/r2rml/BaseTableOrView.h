#pragma once

#include "LogicalTable.h"
#include <memory>
#include <string>
#include <vector>

namespace r2rml {

/**
 * Logical table representing a direct reference to a base table or view
 * (rr:tableName).
 */
class BaseTableOrView : public LogicalTable {
public:
	BaseTableOrView() = default;
	explicit BaseTableOrView(const std::string &table);
	~BaseTableOrView() override;

	std::unique_ptr<SQLResultSet> getRows(SQLConnection &dbConnection) override;

	std::vector<std::string> getColumnNames() override;

	[[nodiscard]] bool isValid() const override {
		return !tableName.empty();
	}

	std::ostream &print(std::ostream &os) const override;

	/// The identifiers rr:tableName names, outermost first. R2RML 5.1 makes
	/// rr:tableName a schema-qualified name in SQL identifier syntax, so it is
	/// split at each '.' outside a delimited ("double-quoted") identifier, and a
	/// delimited part loses its quotes (with "" read as "):
	///   EMP -> {EMP};  hr.EMP -> {hr, EMP};  "my.table" -> {my.table};
	///   db.hr."Emp" -> {db, hr, Emp}.
	/// A name that does not parse (an unterminated quote, an empty part such as
	/// "a..b") is returned whole, as the single identifier it was always taken to be.
	std::vector<std::string> nameParts() const;

	/// The name as a SQL table reference: each part as an ANSI delimited
	/// identifier, joined with '.' ("hr.EMP" -> "hr"."EMP").
	std::string sqlName() const;

	/// nameParts() on any rr:tableName value.
	static std::vector<std::string> splitQualifiedName(const std::string &name);

	std::string tableName;
};

} // namespace r2rml

/*
 * Copyright (C) 2015 Cybernetica
 *
 * Research/Commercial License Usage
 * Licensees holding a valid Research License or Commercial License
 * for the Software may use this file according to the written
 * agreement between you and Cybernetica.
 *
 * GNU Lesser General Public License Usage
 * Alternatively, this file may be used under the terms of the GNU Lesser
 * General Public License version 3 as published by the Free Software
 * Foundation and appearing in the file LICENSE.LGPLv3 included in the
 * packaging of this file.  Please review the following information to
 * ensure the GNU Lesser General Public License version 3 requirements
 * will be met: http://www.gnu.org/licenses/lgpl-3.0.html.
 *
 * For further information, please contact us at sharemind@cyber.ee.
 */

/** \cond */
module table_database;

import stdlib;
/** \endcond */

/**
 * @file
 * \defgroup table_database table_database.sc
 * \defgroup SharemindTdbError Error codes
 * \defgroup tdb_vmap_new tdbVmapNew
 * \defgroup tdb_vmap_delete tdbVmapDelete
 * \defgroup tdb_vmap_count tdbVmapCount
 * \defgroup tdb_vmap_erase tdbVmapErase
 * \defgroup tdb_vmap_add_string tdbVmapAddString
 * \defgroup tdb_vmap_clear tdbVmapClear
 * \defgroup tdb_vmap_reset tdbVmapReset
 * \defgroup tdb_vmap_add_batch tdbVmapAddBatch
 * \defgroup tdb_vmap_set_batch tdbVmapSetBatch
 * \defgroup tdb_vmap_get_batch_count tdbVmapGetBatchCount
 * \defgroup tdb_open_connection tdbOpenConnection
 * \defgroup tdb_close_connection tdbCloseConnection
 * \defgroup tdb_table_create tdbTableCreate
 * \defgroup tdb_table_delete tdbTableDelete
 * \defgroup tdb_table_exists tdbTableExists
 * \defgroup tdb_insert_row tdbInsertRow
 * \defgroup tdb_get_row_count tdbGetRowCount
 * \defgroup tdb_vmap_string_vector_size tdbVmapStringVectorSize
 * \defgroup tdb_vmap_value_vector_size tdbVmapValueVectorSize
 * \defgroup tdb_read_column_index_vmap tdbReadColumn(index, vector map)
 * \defgroup tdb_read_column_string_vmap tdbReadColumn(string, vector map)
 * \defgroup tdb_read_column_index_vec tdbReadColumn(index, value vector)
 * \defgroup tdb_read_column_string_vec tdbReadColumn(string, value vector)
 * \defgroup tdb_get_value_string tdbVmapGetValue(string)
 * \defgroup tdb_get_column_count tdbGetColumnCount
 * \defgroup tdb_get_column_names tdbGetColumnNames
 * \defgroup tdb_vmap_get_string tdbVmapGetString
 * \defgroup tdb_get_column_types tdbGetColumnTypes
 * \defgroup tdb_vmap_get_type_name tdbVmapGetTypeName
 * \defgroup tdb_vmap_add_type tdbVmapAddType
 * \defgroup tdb_vmap_add_vlen_type tdbVmapAddVlenType
 * \defgroup tdb_vmap_add_value_scalar tdbVmapAddValue(scalar)
 * \defgroup tdb_vmap_add_value_vector tdbVmapAddValue(vector)
 * \defgroup tdb_vmap_add_vlen_value tdbVmapAddVlenValue
 * \defgroup tdb_vmap_get_value tdbVmapGetValue
 */

/** \addtogroup table_database
 *  @{
 *  @brief Module for working with table databases.
 */

/** \addtogroup SharemindTdbError
 *  @{
 *  @brief Table database error codes.
 */
int64 SHAREMIND_TDB_OK = 0;
int64 SHAREMIND_TDB_UNKNOWN_ERROR = 1;
int64 SHAREMIND_TDB_GENERAL_ERROR = 2;
int64 SHAREMIND_TDB_CONSENSUS_ERROR = 3;
int64 SHAREMIND_TDB_IO_ERROR = 4;
int64 SHAREMIND_TDB_INVALID_ARGUMENT = 5;
int64 SHAREMIND_TDB_TABLE_NOT_FOUND = 6;
int64 SHAREMIND_TDB_TABLE_ALREADY_EXISTS = 7;
/** @} */

/** \addtogroup tdb_vmap_new
 *  @{
 *  @brief Create a vector map
 *  @return returns an identifier that can be used for working with
 *  the vector map
 */
uint64 tdbVmapNew () {
    uint64 rv = 0;
    __syscall ("tdb_vmap_new", __return rv);
    return rv;
}
/** @} */

/** \addtogroup tdb_vmap_delete
 *  @{
 *  @brief Delete a vector map
 *  @param id - vector map id
 */
void tdbVmapDelete (uint64 id) {
    __syscall ("tdb_vmap_delete", id);
}
/** @} */

/** \addtogroup tdb_vmap_count
 *  @{
 *  @brief Get the number of vectors in a vector map
 *  @param id - vector map id
 *  @param paramname - name of the vector to count
 *  @return returns the number of vectors with the name paramname in the vector map (one or zero)
 */
uint64 tdbVmapCount (uint64 id, string paramname) {
    uint64 rv = 0;
    __syscall ("tdb_vmap_count", id, __cref paramname, __return rv);
    return rv;
}
/** @} */

/** \addtogroup tdb_vmap_string_vector_size
 *  @{
 *  @brief Get the size of a vector in a vector map
 *  @param id - vector map id
 *  @param paramname - name of the vector in the vector map
 *  @return returns the number of values in the vector
 */
uint64 tdbVmapStringVectorSize(uint64 id, string paramname) {
    uint64 rsize = 0;
    __syscall("tdb_vmap_size_string", id, __cref paramname, __return rsize);
    return rsize;
}
/** @} */

/** \addtogroup tdb_vmap_value_vector_size
 *  @{
 *  @brief Get the size of a vector in a vector map
 *  @param id - vector map id
 *  @param paramname - name of the vector in the vector map
 *  @return returns the number of values in the vector
 */
uint64 tdbVmapValueVectorSize(uint64 id, string paramname) {
    uint64 rsize = 0;
    __syscall("tdb_vmap_size_value", id, __cref paramname, __return rsize);
    return rsize;
}
/** @} */

/** \addtogroup tdb_vmap_erase
 *  @{
 *  @brief Remove a vector from a vector map
 *  @param id - vector map id
 *  @param paramname - name of the removed vector
 *  @return returns true if a vector was removed, false otherwise
 */
bool tdbVmapErase (uint64 id, string paramname) {
    uint64 rv = 0;
    __syscall ("tdb_vmap_erase", id, __cref paramname, __return rv);
    return rv != 0;
}
/** @} */

/** \addtogroup tdb_vmap_add_string
 *  @{
 *  @brief Add a string to a vector in a vector map
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the string is added
 *  @param str - string to be added
 */
void tdbVmapAddString (uint64 id, string paramname, string str) {
    __syscall ("tdb_vmap_push_back_string", id, __cref paramname, __cref str);
}
/** @} */

/** \addtogroup tdb_vmap_clear
 *  @{
 *  @brief Clears the current batch in a vector map
 *  @param id - vector map id
 */
void tdbVmapClear (uint64 id) {
    __syscall ("tdb_vmap_clear", id);
}
/** @} */

/** \addtogroup tdb_vmap_reset
 *  @{
 *  @brief Resets the vector map to the initial state
 *  @param id - vector map id
 */
void tdbVmapReset (uint64 id) {
    __syscall ("tdb_vmap_reset", id);
}
/** @} */

/** \addtogroup tdb_vmap_add_batch
 *  @{
 *  @brief Add a batch to a vector map.
 *  @note A vector map always contains at least one batch. Batches are
 *  used for combining multiple database operations. For instance, to
 *  insert two rows at once, add values of the first row to a vector
 *  map, call this function, add values of the second row and call
 *  tdbInsertRow.
 *  @param id - vector map id
 */
void tdbVmapAddBatch (uint64 id) {
    __syscall ("tdb_vmap_add_batch", id);
}
/** @} */

/** \addtogroup tdb_vmap_set_batch
 *  @{
 *  @brief Sets the current active batch
 *  @note Useful for iterating through the batches of the result returned by a
 *  database operation.
 *  @param id - vector map id
 *  @param index - index of the batch in the vector map
 */
void tdbVmapSetBatch (uint64 id, uint64 index) {
    __syscall ("tdb_vmap_set_batch", id, index);
}
/** @} */

/** \addtogroup tdb_vmap_get_batch_count
 *  @{
 *  @brief Get number of batches in a vector map
 *  @param id - vector map id
 *  @return returns the number of batches in the vector map
 */
uint64 tdbVmapGetBatchCount (uint64 id) {
    uint64 out;
    __syscall ("tdb_vmap_batch_count", id, __return out);
    return out;
}
/** @} */

/** \addtogroup tdb_open_connection
 *  @{
 *  @brief Open connection to a data source
 *  @param datasource - data source name
 */
void tdbOpenConnection (string datasource) {
    __syscall ("tdb_open", __cref datasource);
}
/** @} */

/** \addtogroup tdb_close_connection
 *  @{
 *  @brief Close connection to a data source
 *  @param datasource - data source name
 */
void tdbCloseConnection (string datasource) {
    __syscall ("tdb_close", __cref datasource);
}
/** @} */

/** \addtogroup tdb_table_create
 *  @{
 *  @brief Create a table
 *  @param datasource - name of the data source that will contain the table
 *  @param table - table name
 *  @param parameters - id of the vector map containing parameters for
 *  creating the table. The vectors "types" and "names" should contain
 *  the types and names of the columns.
 */
void tdbTableCreate (string datasource, string table, uint64 parameters) {
    __syscall ("tdb_stmt_exec", __cref datasource, __cref table, __cref "tbl_create", parameters);
}
/** @} */

/** \addtogroup tdb_table_delete
 *  @{
 *  @brief Delete a table
 *  @param datasource - name of the data source containing the table
 *  @param table - table name
 */
void tdbTableDelete (string datasource, string table) {
    __syscall ("tdb_tbl_delete", __cref datasource, __cref table);
}
/** @} */

/** \addtogroup tdb_table_exists
 *  @{
 *  @brief Check if a table exists
 *  @param datasource - name of the data source that is expected to contain the table
 *  @param table - table name
 *  @return returns true if the table exists
 */
bool tdbTableExists (string datasource, string table) {
    uint64 rv = 0;
    __syscall ("tdb_tbl_exists", __cref datasource, __cref table, __return rv);
    return rv != 0;
}
/** @} */

/** \addtogroup tdb_insert_row
 *  @{
 *  @brief Insert a row into a table
 *  @param datasource - name of the data source containing the table
 *  @param table - table name
 *  @param parameters - id of the vector map containing values to be
 *  inserted. The vector "values" should contain a value for each
 *  column.
 */
void tdbInsertRow (string datasource, string table, uint64 parameters) {
    __syscall ("tdb_stmt_exec", __cref datasource, __cref table, __cref "insert_row", parameters);
}
/** @} */

/** \addtogroup tdb_get_row_count
 *  @{
 *  @brief Get the number of rows in a table
 *  @param datasource - data source name
 *  @param table - table name
 *  @return returns the number of rows in the table
 */
uint64 tdbGetRowCount (string datasource, string table) {
    uint64 count = 0;
    __syscall ("tdb_tbl_row_count", __cref datasource, __cref table, __return count);
    return count;
}
/** @} */

/** \addtogroup tdb_read_column_index_vmap
 *  @{
 *  @brief Read a column from a table
 *  @param datasource - data source name
 *  @param table - table name
 *  @param index - index of the column in the table
 *  @return Returns a vector map id. The first value of the "values"
 *  value vector in the vector map contains the values in the column.
 */
uint64 tdbReadColumn(string datasource, string table, uint64 index) {
    uint64 rv = 0;
    __syscall("tdb_read_col", __cref datasource, __cref table, index, __return rv);
    return rv;
}
/** @} */

/** \addtogroup tdb_read_column_string_vmap
 *  @{
 *  @brief Read a column from a table
 *  @param datasource - data source name
 *  @param table - table name
 *  @param column - column name
 *  @return Returns a vector map id. The first value of the "values"
 *  value vector in the vector map contains the values in the column.
 */
uint tdbReadColumn(string datasource, string table, string column) {
    uint rv = 0;
    __syscall("tdb_read_col", __cref datasource, __cref table, __cref column, __return rv);
    return rv;
}
/** @} */

/** \addtogroup tdb_read_column_index_vec
 *  @{
 *  @brief Read a column from a table
 *  @param datasource - data source name
 *  @param table - table name
 *  @param index - index of the column in the table
 *  @return returns a vector with the values in the column
 */
/** \cond Doxygen_Suppress */
template<type T>
T[[1]] tdbReadColumn(string datasource, string table, uint64 index) {
    uint64 rv = 0;
    __syscall("tdb_read_col", __cref datasource, __cref table, index, __return rv);
    T[[1]] out = tdbVmapGetValue(rv, "values", 0 :: uint);
    tdbVmapDelete(rv);
    return out;
}
/** \endcond */
/** @} */

/** \addtogroup tdb_read_column_string_vec
 *  @{
 *  @brief Read a column from a table
 *  @param datasource - data source name
 *  @param table - table name
 *  @param column - column name
 *  @return returns a vector with the values in the column
 */
/** \cond Doxygen_Suppress */
template<type T>
T[[1]] tdbReadColumn(string datasource, string table, string column) {
    uint rv = 0;
    __syscall("tdb_read_col", __cref datasource, __cref table, __cref column, __return rv);
    T[[1]] out = tdbVmapGetValue(rv, "values", 0 :: uint);
    tdbVmapDelete(rv);
    return out;
}
/** \endcond */
/** @} */

/** \addtogroup tdb_get_value_string
 *  @{
 *  @brief Get a string from a value vector in a vector map
 *  @param id - id of the vector map
 *  @param paramname - name of the value vector
 *  @param index - index of the element in the value vector
 *  @return returns the string in the value vector at the specified index
 */
string tdbVmapGetValue(uint64 id, string paramname, uint64 index) {
    uint64 isvec = 0;
    __syscall("tdb_vmap_is_value_vector", id, __cref paramname, __return isvec);
    assert(isvec != 0);

    uint64 vsize = 0;
    __syscall("tdb_vmap_size_value", id, __cref paramname, __return vsize);
    assert(index < vsize);

    string rt_name;
    __syscall("tdb_vmap_at_value_type_name", id, __cref paramname, index, __return rt_name);
    assert(rt_name == "string");

    string rt_dom;
    __syscall("tdb_vmap_at_value_type_domain", id, __cref paramname, index, __return rt_dom);
    assert(rt_dom == "public");

    uint64 rt_num_bytes = 0;
    __syscall("tdb_vmap_at_value", id, __cref paramname, index, __return rt_num_bytes);

    uint8[[1]] rt_bytes(rt_num_bytes);
    __syscall("tdb_vmap_at_value", id, __cref paramname, index, __ref rt_bytes);

    return __string_from_bytes(rt_bytes[:rt_num_bytes]); // exclude null-terminator byte
}
/** @} */

/** \addtogroup tdb_get_column_count
 *  @{
 *  @brief Get the number of columns in a table
 *  @param datasource - data source name
 *  @param table - table name
 *  @return returns the number of columns in the table
 */
uint64 tdbGetColumnCount(string datasource, string table) {
    uint64 rv = 0;
    __syscall("tdb_tbl_col_count", __cref datasource, __cref table, __return rv);
    return rv;
}
/** @} */

/** \addtogroup tdb_get_column_names
 *  @{
 *  @brief Get the column names of a table
 *  @param datasource - data source name
 *  @param table - table name
 *  @return returns the id of a vector map where the string vector "names"
 *  contains the names of the columns in the table
 */
uint64 tdbGetColumnNames(string datasource, string table) {
    uint64 rv = 0;
    __syscall("tdb_tbl_col_names", __cref datasource, __cref table, __return rv);
    return rv;
}
/** @} */

/** \addtogroup tdb_vmap_get_string
 *  @{
 *  @brief Get a string from a string vector in a vector map
 *  @param id - vector map id
 *  @param paramname - string vector name
 *  @param index - index of the string in the string vector
 *  @return returns the string in the string vector at the specified index
 */
string tdbVmapGetString(uint64 id, string paramname, uint64 index) {
    uint64 isvec = 0;
    __syscall("tdb_vmap_is_string_vector", id, __cref paramname, __return isvec);
    assert(isvec != 0);

    uint64 vsize = 0;
    __syscall("tdb_vmap_size_string", id, __cref paramname, __return vsize);
    assert(index < vsize);

    string ret;
    __syscall("tdb_vmap_at_string", id, index, __cref paramname, __return ret);

    return ret;
}
/** @} */

/** \addtogroup tdb_get_column_types
 *  @{
 *  @brief Get the column types of a table
 *  @param datasource - data source name
 *  @param table - table name
 *  @return returns the id of a vector map where the type vector
 *  "types" contains the types of the columns in the table
 */
uint64 tdbGetColumnTypes(string datasource, string table) {
    uint64 rv = 0;
    __syscall("tdb_tbl_col_types", __cref datasource, __cref table, __return rv);
    return rv;
}
/** @} */

/** \addtogroup tdb_vmap_get_type_name
 *  @{
 *  @brief Get the name of a type in a type vector in a vector map
 *  @param id - vector map id
 *  @param paramname - type vector name
 *  @param index - index of the type in the type vector
 *  @return returns the name of the type in the type vector at the specified index
 */
string tdbVmapGetTypeName(uint id, string paramname, uint index) {
    uint isvec = 0;
    __syscall("tdb_vmap_is_type_vector", id, __cref paramname, __return isvec);
    assert(isvec != 0);

    uint vsize = 0;
    __syscall("tdb_vmap_size_type", id, __cref paramname, __return vsize);
    assert(index < vsize);

    string ret;
    __syscall("tdb_vmap_at_type_name", id, index, __cref paramname, __return ret);
    return ret;
}
/** @} */

/** \addtogroup tdb_vmap_add_type
 *  @{
 *  @brief Add a type to a vector in a vector map
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the type is added
 *  @param t - a value of the type that's added to the vector
 */
template<type T>
void tdbVmapAddType(uint id, string paramname, T t) {
    string t_dom = "public";
    uint t_size = sizeof(t);
    __syscall("tdb_vmap_push_back_type", id, __cref paramname, __cref t_dom, __cref "$T", t_size);
}
/** @} */

/** \addtogroup tdb_vmap_add_vlen_type
 *  @{
 *  @brief Add a variable length type to a vector in a vector map
 *  @note This is used to create a table with a column that contains
 *  vectors with arbitrary length.
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64" / \ref string "string"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the type is added
 *  @param t - a value of the type that's added to the vector
 */
template<type T>
void tdbVmapAddVlenType(uint64 id, string paramname, T t) {
    string t_dom = "public";
    __syscall("tdb_vmap_push_back_type", id, __cref paramname, __cref t_dom, __cref "$T", 0::uint64);
}
/** @} */

/** \addtogroup tdb_vmap_add_value_scalar
 *  @{
 *  @brief Add a scalar value to a vector in a vector map
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the value is added
 *  @param value - value to be added
 */
template<type T>
void tdbVmapAddValue(uint64 id, string paramname, T value) {
    string t_dom = "public";
    uint64 t_size = sizeof(value);
    __syscall("tdb_vmap_push_back_value", id, __cref paramname, __cref t_dom, __cref "$T", t_size, __cref value);
}
/** @} */

/** \addtogroup tdb_vmap_add_vlen_value
 *  @{
 *  @brief Add a string to a vector in a vector map
 *  @note Supported types - \ref string "string"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the value is added
 *  @param values - vector to be added
 */
void tdbVmapAddVlenValue (uint64 id, string paramname, string value) {
    string t_dom = "public";
    uint8 [[1]] bytes = __bytes_from_string (value);
    __syscall("tdb_vmap_push_back_value", id, __cref paramname, __cref t_dom, __cref "string", 0::uint64, __cref bytes);
}
/** @} */

/** \addtogroup tdb_vmap_add_value_vector
 *  @{
 *  @brief Add a vector to a vector in a vector map
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the argument vector is added
 *  @param values - vector to be added
 */
template<type T>
void tdbVmapAddValue (uint64 id, string paramname, T[[1]] values) {
    T dummy;
    string t_dom = "public";
    uint64 t_size = sizeof(dummy);
    __syscall("tdb_vmap_push_back_value", id, __cref paramname, __cref t_dom, __cref "$T", t_size, __cref values);
}
/** @} */

/** \addtogroup tdb_vmap_get_value
 *  @{
 *  @brief Get a value from a vector in a vector map
 *  @param id - vector map id
 *  @param paramname - name of the vector from which to retrieve the value
 *  @param index - index of the value in the vector
 *  @return returns the value in the vector at the specified index
 */
template<type T>
T[[1]] tdbVmapGetValue (uint id, string paramname, uint index) {
    T dummy;
    string t_dom = "public";
    uint t_size = sizeof(dummy);

    uint isvalue = 0;
    __syscall("tdb_vmap_is_value_vector", id, __cref paramname, __return isvalue);
    assert(isvalue != 0);

    uint64 pvsize = 0;
    __syscall("tdb_vmap_size_value", id, __cref paramname, __return pvsize);
    assert(index < pvsize);

    string rt_dom;
    __syscall("tdb_vmap_at_value_type_domain", id, __cref paramname, index, __return rt_dom);
    assert(rt_dom == t_dom);

    string rt_name;
    __syscall("tdb_vmap_at_value_type_name", id, __cref paramname, index, __return rt_name);
    assert(rt_name == "$T");

    uint64 rt_size = 0;
    __syscall("tdb_vmap_at_value_type_size", id, __cref paramname, index, __return rt_size);
    assert(rt_size == t_size);

    uint64 num_bytes = 0;
    __syscall ("tdb_vmap_at_value", id, __cref paramname, index, __return num_bytes);
    T[[1]] out(num_bytes / t_size);
    __syscall("tdb_vmap_at_value", id, __cref paramname, index, __ref out);

    return out;
}
/** @} */

/** @} */

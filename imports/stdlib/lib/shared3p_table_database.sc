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
module shared3p_table_database;

import shared3p;
import table_database;
/** \endcond */

/**
 * @file
 * \defgroup shared3p_table_database shared3p_table_database.sc
 * \defgroup shared3p_tdb_vmap_add_type tdbVmapAddType
 * \defgroup shared3p_tdb_vmap_add_vlen_type tdbVmapAddVlenType
 * \defgroup shared3p_tdb_vmap_add_value_scalar tdbVmapAddValue(scalar)
 * \defgroup shared3p_tdb_vmap_add_value_vector tdbVmapAddValue(vector)
 * \defgroup shared3p_tdb_vmap_add_vlen_value tdbVmapAddVlenValue
 * \defgroup shared3p_tdb_vmap_get_value tdbVmapGetValue
 * \defgroup shared3p_tdb_vmap_get_vlen_value tdbVmapGetVlenValue
 * \defgroup shared3p_tdb_table_create tdbTableCreate
 * \defgroup shared3p_tdb_insert_row tdbInsertRow
 * \defgroup shared3p_tdb_read_column_index tdbReadColumn(index)
 * \defgroup shared3p_tdb_read_column_string tdbReadColumn(string)
 */

/** \addtogroup shared3p_table_database
 * @{
 * @brief Module for working with table databases that contain shared3p shares.
 */

/** \addtogroup shared3p_tdb_vmap_add_type
 *  @{
 *  @brief Add a type to a vector in a vector map
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the type is added
 *  @param t - a value of the type that's added to the vector
 */
template <domain D : shared3p, type T>
void tdbVmapAddType (uint64 id, string paramname, D T t) {
    string t_dom;
    __syscall("shared3p::get_domain_name", __domainid(D), __return t_dom);
    uint64 t_size;
    __syscall("shared3p::get_type_size_$T", __domainid(D), __return t_size);
    __syscall("tdb_vmap_push_back_type", id, __cref paramname, __cref t_dom, __cref "$T", t_size);
}
/** @} */

/** \addtogroup shared3p_tdb_vmap_add_vlen_type
 *  @{
 *  @brief Add a variable length type to a vector in a vector map
 *  @note This is used to create a table with a column that contains
 *  vectors with arbitrary length.
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the type is added
 *  @param t - a value of the type that's added to the vector
 */
template <domain D : shared3p, type T>
void tdbVmapAddVlenType (uint64 id, string paramname, D T t) {
    string t_dom;
    __syscall("shared3p::get_domain_name", __domainid(D), __return t_dom);
    __syscall("tdb_vmap_push_back_type", id, __cref paramname, __cref t_dom, __cref "$T", 0::uint64);
}
/** @} */

/** \addtogroup shared3p_tdb_vmap_add_value_scalar
 *  @{
 *  @brief Add a scalar value to a vector in a vector map
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the value is added
 *  @param value - value to be added
 */
template <domain D : shared3p, type T>
void tdbVmapAddValue (uint64 id, string paramname, D T value) {
    string t_dom;
    __syscall("shared3p::get_domain_name", __domainid(D), __return t_dom);
    uint64 t_size;
    __syscall("shared3p::get_type_size_$T", __domainid(D), __return t_size);
    uint64 num_bytes;
    __syscall("shared3p::get_shares_$T\_vec", __domainid(D), value, __return num_bytes);
    uint8 [[1]] bytes(num_bytes);
    __syscall("shared3p::get_shares_$T\_vec", __domainid(D), value, __ref bytes);
    __syscall("tdb_vmap_push_back_value", id, __cref paramname, __cref t_dom, __cref "$T", t_size, __cref bytes);
}
/** @} */

/** \addtogroup shared3p_tdb_vmap_add_value_vector
 *  @{
 *  @brief Add a vector to a vector in a vector map
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the argument vector is added
 *  @param values - vector to be added
 */
template <domain D : shared3p, type T>
void tdbVmapAddValue (uint64 id, string paramname, D T [[1]] values) {
    string t_dom;
    __syscall("shared3p::get_domain_name", __domainid(D), __return t_dom);
    uint64 t_size;
    __syscall("shared3p::get_type_size_$T", __domainid(D), __return t_size);
    uint64 num_bytes;
    __syscall("shared3p::get_shares_$T\_vec", __domainid(D), values, __return num_bytes);
    uint8 [[1]] bytes(num_bytes);
    __syscall("shared3p::get_shares_$T\_vec", __domainid(D), values, __ref bytes);
    __syscall("tdb_vmap_push_back_value", id, __cref paramname, __cref t_dom, __cref "$T", t_size, __cref bytes);
}
/** @} */

/** \addtogroup shared3p_tdb_vmap_add_vlen_value
 *  @{
 *  @brief Add a variable length vector to a vector in a vector map
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector to which the value is added
 *  @param values - vector to be added
 */
template <domain D : shared3p, type T>
void tdbVmapAddVlenValue (uint64 id, string paramname, D T [[1]] values) {
    string t_dom;
    __syscall("shared3p::get_domain_name", __domainid(D), __return t_dom);
    uint64 num_bytes;
    __syscall("shared3p::get_shares_$T\_vec", __domainid(D), values, __return num_bytes);
    uint8 [[1]] bytes(num_bytes);
    __syscall("shared3p::get_shares_$T\_vec", __domainid(D), values, __ref bytes);
    __syscall("tdb_vmap_push_back_value", id, __cref paramname, __cref t_dom, __cref "$T", 0::uint64, __cref bytes);
}
/** @} */

/** \addtogroup shared3p_tdb_vmap_get_value
 *  @{
 *  @brief Get a value from a vector in a vector map
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector from which to retrieve the value
 *  @param index - index of the value in the vector
 *  @return returns the value in the vector at the specified index
 */
template <domain D : shared3p, type T>
D T[[1]] tdbVmapGetValue (uint64 id, string paramname, uint64 index) {
    // Get type information
    string t_dom;
    __syscall ("shared3p::get_domain_name", __domainid(D), __return t_dom);
    uint64 t_size = 0;
    __syscall ("shared3p::get_type_size_$T", __domainid(D), __return t_size);

    // Check if the given vector map is valid
    uint64 isvalue = 0;
    __syscall ("tdb_vmap_is_value_vector", id, __cref paramname, __return isvalue);
    assert (isvalue != 0);

    // Get the number of values in 'values'
    uint64 pvsize = 0;
    __syscall ("tdb_vmap_size_value", id, __cref paramname, __return pvsize);
    assert (index < pvsize);

    // Check if the returned value type matches
    string rt_dom;
    __syscall ("tdb_vmap_at_value_type_domain", id, __cref paramname, index, __return rt_dom);
    assert (rt_dom == t_dom);

    string rt_name;
    __syscall ("tdb_vmap_at_value_type_name", id, __cref paramname, index, __return rt_name);
    assert (rt_name == "$T");

    uint64 rt_size = 0;
    __syscall ("tdb_vmap_at_value_type_size", id, __cref paramname, index, __return rt_size);
    assert (rt_size == t_size);

    // Read the value bytes
    uint64 num_bytes = 0;
    __syscall ("tdb_vmap_at_value", id, __cref paramname, index, __return num_bytes);
    uint8[[1]] bytes(num_bytes);
    __syscall ("tdb_vmap_at_value", id, __cref paramname, index, __ref bytes);

    // Deserialize the value
    uint64 vsize = 0;
    __syscall ("shared3p::set_shares_$T\_vec", __domainid(D), __cref bytes, __return vsize);
    D T[[1]] out(vsize);
    __syscall ("shared3p::set_shares_$T\_vec", __domainid(D), out, __cref bytes);

    return out;
}
/** @} */

/** \addtogroup shared3p_tdb_vmap_get_vlen_value
 *  @{
 *  @brief Get a variable length value from a vector in a vector map
 *  @note This function is used when the table column contains variable length vectors
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param id - vector map id
 *  @param paramname - name of the vector from which to retrieve the value
 *  @param index - index of the value in the vector
 */
template <domain D : shared3p, type T>
D T[[1]] tdbVmapGetVlenValue (uint64 id, string paramname, uint64 index) {
    // Get type information
    string t_dom;
    __syscall ("shared3p::get_domain_name", __domainid(D), __return t_dom);

    // Check if the given vector map is valid
    uint64 isvalue = 0;
    __syscall ("tdb_vmap_is_value_vector", id, __cref paramname, __return isvalue);
    assert (isvalue != 0);

    // Get the number of values in 'values'
    uint64 pvsize = 0;
    __syscall ("tdb_vmap_size_value", id, __cref paramname, __return pvsize);
    assert (index < pvsize);

    // Check if the returned value type matches
    string rt_dom;
    __syscall ("tdb_vmap_at_value_type_domain", id, __cref paramname, index, __return rt_dom);
    assert (rt_dom == t_dom);

    string rt_name;
    __syscall ("tdb_vmap_at_value_type_name", id, __cref paramname, index, __return rt_name);
    assert (rt_name == "$T");

    uint64 rt_size = 0;
    __syscall ("tdb_vmap_at_value_type_size", id, __cref paramname, index, __return rt_size);
    assert (rt_size == 0);

    // Read the value bytes
    uint64 num_bytes = 0;
    __syscall ("tdb_vmap_at_value", id, __cref paramname, index, __return num_bytes);
    uint8[[1]] bytes(num_bytes);
    __syscall ("tdb_vmap_at_value", id, __cref paramname, index, __ref bytes);

    // Deserialize the value
    uint64 vsize = 0;
    __syscall ("shared3p::set_shares_$T\_vec", __domainid(D), __cref bytes, __return vsize);
    D T[[1]] out(vsize);
    __syscall ("shared3p::set_shares_$T\_vec", __domainid(D), out, __cref bytes);

    return out;
}
/** @} */

/** \addtogroup shared3p_tdb_table_create
 *  @{
 *  @brief Create a table where all columns have the same type
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param datasource - name of the data source
 *  @param table - name of the table
 *  @param vtype - the type of this value will be the type of the columns
 *  @param ncols - number of columns in the created table
 */
template <domain D : shared3p, type T, dim N>
void tdbTableCreate (string datasource, string table, D T[[N]] vtype, uint64 ncols) {
    string t_dom;
    __syscall ("shared3p::get_domain_name", __domainid(D), __return t_dom);
    uint64 t_size = 0;
    __syscall ("shared3p::get_type_size_$T", __domainid(D), __return t_size);
    __syscall ("tdb_tbl_create", __cref datasource, __cref table, __cref t_dom, __cref "$T", t_size, ncols);
}
/** @} */

/** \addtogroup shared3p_tdb_insert_row
 *  @{
 *  @brief Insert a row into a table
 *  @note This function can be used if all columns have the same type.
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param datasource - name of the data source
 *  @param table - name of the table
 *  @param values - row to be inserted
 */
template <domain D : shared3p, type T>
void tdbInsertRow (string datasource, string table, D T[[1]] values) {
    string t_dom;
    __syscall ("shared3p::get_domain_name", __domainid(D), __return t_dom);
    uint64 t_size = 0;
    __syscall ("shared3p::get_type_size_$T", __domainid(D), __return t_size);
    uint64 num_bytes = 0;
    __syscall ("shared3p::get_shares_$T\_vec", __domainid(D), values, __return num_bytes);
    uint8[[1]] bytes(num_bytes);
    __syscall ("shared3p::get_shares_$T\_vec", __domainid(D), values, __ref bytes);
    __syscall ("tdb_insert_row", __cref datasource, __cref table, __cref t_dom, __cref "$T", t_size, __cref bytes);
}
/** @} */

/** \addtogroup shared3p_tdb_read_column_index
 *  @{
 *  @brief Read a column from a table
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param datasource - name of the data source
 *  @param table - name of the table
 *  @param index - index of the column in the table
 *  @return returns a vector with the values in the column
 */
template <domain D : shared3p, type T>
D T[[1]] tdbReadColumn (string datasource, string table, uint64 index) {
    uint64 rv = 0;
    __syscall ("tdb_read_col", __cref datasource, __cref table, index, __return rv);
    D T[[1]] out = tdbVmapGetValue(rv, "values", 0::uint64);
    tdbVmapDelete(rv);
    return out;
}
/** @} */

/** \addtogroup shared3p_tdb_read_column_string
 *  @{
 *  @brief Read a column from a table
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64" \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param datasource - name of the data source
 *  @param table - name of the table
 *  @param column - name of the column
 *  @return returns a vector with the values in the column
 */
template <domain D : shared3p, type T>
D T[[1]] tdbReadColumn (string datasource, string table, string column) {
    uint64 rv = 0;
    __syscall ("tdb_read_col", __cref datasource, __cref table, __cref column, __return rv);
    D T[[1]] out = tdbVmapGetValue(rv, "values", 0::uint64);
    tdbVmapDelete(rv);
    return out;
}
/** @} */

/** @} */

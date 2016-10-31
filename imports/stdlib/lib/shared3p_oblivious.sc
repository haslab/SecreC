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

/**
* \cond
*/
module shared3p_oblivious;

import shared3p;
import oblivious;
import stdlib;
/**
* \endcond
*/

/**
* @file
* \defgroup shared3p_oblivious shared3p_oblivious.sc
* \defgroup shared3p_choose choose
* \defgroup shared3p_vectorupdate vectorUpdate
* \defgroup shared3p_matrixupdate matrixUpdate
* \defgroup shared3p_matrixupdaterow matrixUpdateRow
* \defgroup shared3p_matrixupdatecolumn matrixUpdateColumn
*/

/** \addtogroup shared3p_oblivious
*@{
* @brief Module with functions for oblivious tasks (shared3p protection domain)
*/

/** \addtogroup shared3p_choose
 *  @{
 *  @brief Function for obliviously choosing one of the inputs
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 *  @param cond - a boolean array.
 *  @return returns one of the input arrays that was obliviously chosen with the condition. if **true**, array **first** is returned else **second** is returned
 */

template <domain D : shared3p, dim N>
D float32[[N]] choose(D bool[[N]] cond, D float32[[N]] first, D float32[[N]] second) {
    D float32[[N]] out = first;
    __syscall ("shared3p::choose_float32_vec", __domainid (D), cond, first, second, out);
    return out;
}

template <domain D : shared3p, dim N>
D float64[[N]] choose(D bool[[N]] cond, D float64[[N]] first, D float64[[N]] second) {
    D float64[[N]] out = first;
    __syscall ("shared3p::choose_float64_vec", __domainid (D), cond, first, second, out);
    return out;
}

/** @}*/


/** \addtogroup shared3p_vectorupdate
 *  @{
 *  @brief Function for obliviously updating an element in the input vector
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref float64 "float64" / \ref float32 "float32"
 *  @param vec - a 1-dimensional vector of supported type
 *  @param index - an \ref uint64 "uint" type scalar for specifying the element to replace
 *  @param newValue - a scalar value of the same type as the input vector
 *  @return returns a vector with the value at position **index** replaced by **newValue**
 */

/** \cond */

template <domain D : shared3p, type T>
D T[[1]] _vectorUpdate(D T[[1]] vec, D uint index, D T newValue) {
    D T[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}

/** \endcond */

template <domain D : shared3p>
D float32[[1]] vectorUpdate(D float32[[1]] vec, D uint index, D float32 newValue) {
    return _vectorUpdate (vec, index, newValue);
}

template <domain D : shared3p>
D float64[[1]] vectorUpdate(D float64[[1]] vec, D uint index, D float64 newValue) {
    return _vectorUpdate (vec, index, newValue);
}
/** @}*/


/** \addtogroup shared3p_matrixupdaterow
 *  @{
 *  @brief Function for obliviously updating a row in the input matrix
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 *  @param mat - a matrix of supported type
 *  @param rowIndex - an \ref uint64 "uint" type scalar for specifying the row to replace
 *  @param newRow - a vector with new values
 *  @return returns a matrix where the row at **rowIndex** has been replaced with **newRow**
 */

/** \cond */

template <domain D : shared3p, type T>
D T[[2]] _matrixUpdateRow(D T[[2]] mat, D uint rowIndex, D T[[1]] newRow) {
    uint[[1]] s = shape(mat);
    uint rows = s[0];
    uint cols = s[1];
    assert(cols == size(newRow));
    // assert(declassify(rows > rowIndex));

    D bool[[2]] mask = matrixLookupRowBitmask(rows, cols, rowIndex);

    D T[[2]] newRows(rows, cols);
    for (uint i = 0; i < rows; ++i)
        newRows[i,:] = newRow;

    return choose(mask, newRows, mat);
}

/** \endcond */

template <domain D : shared3p>
D float32[[2]] matrixUpdateRow(D float32[[2]] mat, D uint rowIndex, D float32[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}

template <domain D : shared3p>
D float64[[2]] matrixUpdateRow(D float64[[2]] mat, D uint rowIndex, D float64[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}
/** @}*/


/** \addtogroup shared3p_matrixupdatecolumn
 *  @{
 *  @brief Function for obliviously updating a column in the input matrix
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 *  @param mat - a matrix of supported type
 *  @param colIndex - an \ref uint64 "uint" type scalar for specifying the column to replace
 *  @param newCol - a vector with new values
 *  @return returns a matrix where the column at **colIndex** has been replaced with **newCol**
 */

/** \cond */

template <domain D : shared3p, type T>
D T[[2]] _matrixUpdateColumn(D T[[2]] mat, D uint colIndex, D T[[1]] newCol) {
    uint[[1]] s = shape(mat);
    uint rows = s[0];
    uint cols = s[1];
    assert(rows == size(newCol));
    // assert(declassify(cols > colIndex));

    D bool[[2]] mask = matrixLookupColumnBitmask(rows, cols, colIndex);

    D T[[2]] newCols(rows, cols);
    for (uint i = 0; i < cols; ++i)
        newCols[:,i] = newCol;

    return choose(mask, newCols, mat);
}

/** \endcond */

template <domain D : shared3p>
D float32[[2]] matrixUpdateColumn(D float32[[2]] mat, D uint colIndex, D float32[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

template <domain D : shared3p>
D float64[[2]] matrixUpdateColumn(D float64[[2]] mat, D uint colIndex, D float64[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}
/** @}*/


/** \addtogroup shared3p_matrixupdate
 *  @{
 *  @brief Function for obliviously updating a value in the input matrix
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 *  @param mat - a matrix of supported type
 *  @param rowIndex - an \ref uint64 "uint" type scalar for specifying the row in the input matrix
 *  @param colIndex - an \ref uint64 "uint" type scalar for specifying the column in the input matrix
 *  @param newValue - a new scalar value
 *  @return returns a matrix where the element at row **rowIndex** and column **colIndex** has been replaced with **newValue**
 */

/** \cond */

template <domain D : shared3p, type T>
D T[[2]] _matrixUpdate(D T[[2]] mat, D uint rowIndex, D uint columnIndex, D T newValue) {
    uint[[1]] s = shape(mat);
    uint rows = s[0];
    uint cols = s[1];
    // assert(declassify(rows > rowIndex));
    // assert(declassify(cols > columnIndex));

    D T[[2]] n(rows, cols) = newValue;
    return choose(matrixLookupBitmask(rows, cols, rowIndex, columnIndex), n, mat);
}

/** \endcond */

template <domain D : shared3p>
D float32[[2]] matrixUpdate(D float32[[2]] mat, D uint rowIndex, D uint columnIndex, D float32 newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

template <domain D : shared3p>
D float64[[2]] matrixUpdate(D float64[[2]] mat, D uint rowIndex, D uint columnIndex, D float64 newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

/** @}*/

/** @}*/

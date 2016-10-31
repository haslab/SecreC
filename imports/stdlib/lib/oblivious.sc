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
module oblivious;

import stdlib;
import matrix;
/**
* \endcond
*/

/**
* @file
* \defgroup oblivious oblivious.sc
* \defgroup choose choose
* \defgroup choose1 choose(single condition)
* \defgroup choose2 choose(multiple conditions)
* \defgroup vectorlookup vectorLookup
* \defgroup matrixlookuprow matrixLookupRow
* \defgroup matrixlookupcolumn matrixLookupColumn
* \defgroup matrixlookup matrixLookup
* \defgroup vectorupdate vectorUpdate
* \defgroup matrixupdaterow matrixUpdateRow
* \defgroup matrixupdatecolumn matrixUpdateColumn
* \defgroup matrixupdate matrixUpdate
*/

/** \addtogroup oblivious
*@{
* @brief Module with functions for oblivious tasks
*/


/**
 * \todo
 *    NB!!
 * Functions for float32 and float64 do not guarantee precise results!!!
 * Need syscalls for floats that compare all 3 components of float. *
 *
 */


/*******************************************************************************
********************************************************************************
**                                                                            **
**  Oblivious choice (choose)                                                 **
**                                                                            **
********************************************************************************
*******************************************************************************/

/** \addtogroup choose
 *  @{
 *  @brief Function for obliviously choosing one of the inputs
 *  @note **D** - all protection domains
 *  @return returns one of the input arrays that was obliviously chosen with the condition
 */

/** \addtogroup choose1
 *  @{
 *  @brief Function for obliviously choosing one of the inputs
 *  @note **D** - all protection domains
 *  @note **T** - any \ref data_types "data" type
 *  @param cond - a boolean scalar.
 *  @return returns one of the input arrays that was obliviously chosen with the condition. if **true**, array **first** is returned else **second** is returned
 */

template <domain D, type T, dim N>
D T[[N]] choose(bool cond, D T[[N]] first, D T[[N]] second) {
    return cond ? first : second;
}

template <domain D, dim N>
D bool[[N]] choose(D bool cond, D bool[[N]] first, D bool[[N]] second) {
    assert(shapesAreEqual(first,second));
    return first && cond || second && !cond;
}

/** \cond */

template <domain D, dim N, type T>
D T[[N]] _chooseInt (D bool cond, D T[[N]] first, D T[[N]] second) {
    assert (shapesAreEqual (first, second));
    D T cond2 = (T)cond;
    // Using this form because multiplication is more expensive than addition
    return cond2 * (first - second) + second;
}

template <domain D, dim N, type T>
D T[[N]] _chooseFloat (D bool cond, D T[[N]] first, D T[[N]] second) {
    assert(shapesAreEqual(first,second));
    D T cond2 = (T)cond;
    D T cond3 = (T)!cond;
    // Using different form here because multiplication is cheap and addition is expensive
    return first * cond2 + second * cond3;
}

/** \endcond */

template <domain D, dim N>
D uint8[[N]] choose(D bool cond, D uint8[[N]] first, D uint8[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D uint16[[N]] choose(D bool cond, D uint16[[N]] first, D uint16[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D uint32[[N]] choose(D bool cond, D uint32[[N]] first, D uint32[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D uint[[N]] choose(D bool cond, D uint[[N]] first, D uint[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D int8[[N]] choose(D bool cond, D int8[[N]] first, D int8[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D int16[[N]] choose(D bool cond, D int16[[N]] first, D int16[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D int32[[N]] choose(D bool cond, D int32[[N]] first, D int32[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D int[[N]] choose(D bool cond, D int[[N]] first, D int[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D float32[[N]] choose(D bool cond, D float32[[N]] first, D float32[[N]] second) {
    return _chooseFloat (cond, first, second);
}
template <domain D, dim N>
D float64[[N]] choose(D bool cond, D float64[[N]] first, D float64[[N]] second) {
    return _chooseFloat (cond, first, second);
}

/** @}*/

/** \addtogroup choose2
 *  @{
 *  @brief Function for obliviously choosing pointwise from the inputs
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param cond - a boolean array
 *  @return pointwise check if **cond** at a certain position is **true** or **false**. if **true** the element of **first** at that position is returned else the element of **second** at that position is returned
 */

template <domain D, dim N>
D bool[[N]] choose(D bool[[N]] cond, D bool[[N]] first, D bool[[N]] second) {
    assert (shapesAreEqual (cond, first, second));
    return first && cond || second && !cond;
}

/** \cond */

template <domain D, dim N, type T>
D T[[N]] _chooseInt (D bool[[N]] cond, D T[[N]] first, D T[[N]] second) {
    assert (shapesAreEqual (cond, first, second));
    D T[[N]] cond2 = (T) cond;
    return cond2 * (first - second) + second;
}

/** \endcond */

template <domain D, dim N>
D uint8[[N]] choose(D bool[[N]] cond, D uint8[[N]] first, D uint8[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D uint16[[N]] choose(D bool[[N]] cond, D uint16[[N]] first, D uint16[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D uint32[[N]] choose(D bool[[N]] cond, D uint32[[N]] first, D uint32[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D uint[[N]] choose(D bool[[N]] cond, D uint[[N]] first, D uint[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D int8[[N]] choose(D bool[[N]] cond, D int8[[N]] first, D int8[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D int16[[N]] choose(D bool[[N]] cond, D int16[[N]] first, D int16[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D int32[[N]] choose(D bool[[N]] cond, D int32[[N]] first, D int32[[N]] second) {
    return _chooseInt (cond, first, second);
}
template <domain D, dim N>
D int[[N]] choose(D bool[[N]] cond, D int[[N]] first, D int[[N]] second) {
    return _chooseInt (cond, first, second);
}


/** @}*/
/** @}*/


/*******************************************************************************
********************************************************************************
**                                                                            **
**  vectorLookup                                                             **
**                                                                            **
********************************************************************************
*******************************************************************************/
/**
* \cond
*/

uint[[1]] _indexVector (uint n) {
    uint[[1]] is (n);
    for (uint i = 0; i < n; ++ i) {
        is[i] = i;
    }

    return is;
}

template <domain D>
D bool[[1]] vectorLookupBitmask(uint elems, D uint index) {
    uint[[1]] is = _indexVector (elems);
    return index == is;
}

/**
* \endcond
*/

/** \addtogroup vectorlookup
 *  @{
 *  @brief Function for obliviously looking up an element in a vector
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param vec - a 1-dimensional vector of supported type
 *  @param index - an \ref uint64 "uint" type scalar for specifying the position in the vector to look up
 *  @return returns the element in the vector specified by **index**
 */

template <domain D>
D bool vectorLookup(D bool[[1]] vec, D uint index) {
    uint elems = size(vec);
    D bool[[1]] mask = vectorLookupBitmask(elems, index);
    mask &= vec;
    D bool sum;
    for (uint i = 0; i < elems; ++i) {
        sum ^= mask[i];
    }
    return sum;
}

/** \cond */

template <domain D, type T>
D T _vectorLookup(D T[[1]] vec, D uint index) {
    D T[[1]] mask = (T) vectorLookupBitmask(size(vec), index);
    return sum (mask * vec);
}

/** \endcond */

template <domain D>
D uint8 vectorLookup(D uint8[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

template <domain D>
D uint16 vectorLookup(D uint16[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

template <domain D>
D uint32 vectorLookup(D uint32[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

template <domain D>
D uint vectorLookup(D uint[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

template <domain D>
D int8 vectorLookup(D int8[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

template <domain D>
D int16 vectorLookup(D int16[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

template <domain D>
D int32 vectorLookup(D int32[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

template <domain D>
D int vectorLookup(D int[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

template <domain D>
D float32 vectorLookup(D float32[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

template <domain D>
D float64 vectorLookup(D float64[[1]] vec, D uint index) {
    return _vectorLookup (vec, index);
}

/** @}*/


/*******************************************************************************
********************************************************************************
**                                                                            **
**  matrixLookupRow                                                         **
**                                                                            **
********************************************************************************
*******************************************************************************/

/**
* \cond
*/

template <domain D>
D bool[[2]] matrixLookupRowBitmask(uint rows, uint cols, D uint rowIndex) {
    uint[[1]] is (rows);
    for (uint i = 0; i < rows; ++ i) {
        is[i] = i;
    }

    D bool[[1]] rowMask = (is == rowIndex);
    D bool[[2]] mask (rows, cols);

    // Stretch mask:
    for (uint i = 0; i < cols; ++ i) {
        mask[:, i] = rowMask;
    }

    return mask;
}

/**
* \endcond
*/

/** \addtogroup matrixlookuprow
 *  @{
 *  @brief Function for obliviously looking up a row in a matrix
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param mat - a 2-dimensional matrix of supported type
 *  @param rowIndex - an \ref uint64 "uint" type scalar for specifying the row of the input matrix to look up
 *  @return returns the row from the input matrix specified by **rowIndex**
 */


template <domain D>
D bool[[1]] matrixLookupRow(D bool[[2]] mat, D uint rowIndex) {
    uint[[1]] s = shape(mat);
    uint rows = s[0];
    uint cols = s[1];

    D bool[[2]] mask = matrixLookupRowBitmask(rows, cols, rowIndex);

    mat &= mask;

    D bool[[1]] sum(cols);
    for (uint i = 0; i < rows; ++i) {
        sum ^= mat[i, :];
    }

    return sum;
}

/** \cond */

template <domain D, type T>
D T[[1]] _matrixLookupRow(D T[[2]] mat, D uint rowIndex) {
    uint[[1]] s = shape(mat);
    uint rows = s[0];
    uint cols = s[1];
    D T[[2]] mask = (T) matrixLookupRowBitmask(rows, cols, rowIndex);
    return colSums (mat * mask);
}

/** \endcond */

template <domain D>
D uint8[[1]] matrixLookupRow(D uint8[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

template <domain D>
D uint16[[1]] matrixLookupRow(D uint16[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

template <domain D>
D uint32[[1]] matrixLookupRow(D uint32[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

template <domain D>
D uint[[1]] matrixLookupRow(D uint[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

template <domain D>
D int8[[1]] matrixLookupRow(D int8[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

template <domain D>
D int16[[1]] matrixLookupRow(D int16[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

template <domain D>
D int32[[1]] matrixLookupRow(D int32[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

template <domain D>
D int[[1]] matrixLookupRow(D int[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

template <domain D>
D float32[[1]] matrixLookupRow(D float32[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

template <domain D>
D float64[[1]] matrixLookupRow(D float64[[2]] mat, D uint rowIndex) {
    return _matrixLookupRow (mat, rowIndex);
}

/** @}*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  matrixLookupColumn                                                        **
**                                                                            **
********************************************************************************
*******************************************************************************/

/**
* \cond
*/

template <domain D>
D bool[[2]] matrixLookupColumnBitmask(uint rows, uint cols, D uint colIndex) {
    uint[[1]] is (cols);
    for (uint i = 0; i < cols; ++ i) {
        is[i] = i;
    }

    D bool[[1]] colMask = (is == colIndex);
    D bool[[2]] mask (rows, cols);

    // Stretch mask:
    for (uint i = 0; i < rows; ++ i) {
        mask[i, :] = colMask;
    }

    return mask;
}
/**
* \endcond
*/

/** \addtogroup matrixlookupcolumn
 *  @{
 *  @brief Function for obliviously looking up a column in a matrix
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param mat - a 2-dimensional matrix of supported type
 *  @param colIndex - an \ref uint64 "uint" type scalar for specifying the column of the input matrix to look up
 *  @return returns the column from the input matrix specified by **colIndex**
 */

template <domain D>
D bool[[1]] matrixLookupColumn (D bool[[2]] mat, D uint colIndex) {
    uint[[1]] s = shape(mat);
    uint rows = s[0];
    uint cols = s[1];
    D bool[[2]] mask = matrixLookupColumnBitmask(rows, cols, colIndex);

    mat &= mask;

    D bool[[1]] sum(rows);
    for (uint i = 0; i < rows; ++i)
        for (uint j = 0; j < cols; ++j)
            sum[i] ^= mat[i, j];

    return sum;
}

/** \cond */

template <domain D, type T>
D T[[1]] _matrixLookupColumn(D T[[2]] mat, D uint colIndex) {
    uint[[1]] s = shape(mat);
    uint rows = s[0];
    uint cols = s[1];
    D T[[2]] mask = (T) matrixLookupColumnBitmask(rows, cols, colIndex);
    return rowSums (mat * mask);
}

/** \endcond */

template <domain D>
D uint8[[1]] matrixLookupColumn(D uint8[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

template <domain D>
D uint16[[1]] matrixLookupColumn(D uint16[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

template <domain D>
D uint32[[1]] matrixLookupColumn(D uint32[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

template <domain D>
D uint[[1]] matrixLookupColumn(D uint[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

template <domain D>
D int8[[1]] matrixLookupColumn(D int8[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

template <domain D>
D int16[[1]] matrixLookupColumn(D int16[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

template <domain D>
D int32[[1]] matrixLookupColumn(D int32[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

template <domain D>
D int[[1]] matrixLookupColumn(D int[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

template <domain D>
D float32[[1]] matrixLookupColumn(D float32[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

template <domain D>
D float64[[1]] matrixLookupColumn(D float64[[2]] mat, D uint colIndex) {
    return _matrixLookupColumn (mat, colIndex);
}

/** @}*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  matrixLookup                                                             **
**                                                                            **
********************************************************************************
*******************************************************************************/

/**
* \cond
*/

template <domain D>
D bool[[2]] matrixLookupBitmask(uint rows, uint cols, D uint rowIndex, D uint columnIndex) {
    // check if rows * cols would overflow
    // it's infeasible to handle the overflow as 2^64 of *anything* would be
    // much much too large to handle.
    assert (UINT64_MAX / rows >= cols);
    uint[[1]] is = _indexVector (rows * cols);
    D uint pIndex = rowIndex * cols + columnIndex;
    return reshape (is, rows, cols) == pIndex;
}

/**
* \endcond
*/

/** \addtogroup matrixlookup
 *  @{
 *  @brief Function for obliviously looking up an element in the input matrix
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param mat - a 2-dimensional matrix of supported type
 *  @param rowIndex - an \ref uint64 "uint" type scalar for specifying the row in the input matrix
 *  @param colIndex - an \ref uint64 "uint" type scalar for specifying the column in the input matrix
 *  @return returns the element from the input matrix specified by **rowIndex** and **colIndex**
 */

template <domain D>
D bool matrixLookup(D bool[[2]] mat, D uint rowIndex, D uint columnIndex) {
    uint[[1]] s = shape(mat);
    uint rows = s[0];
    uint cols = s[1];

    D bool[[2]] mask = matrixLookupBitmask(rows, cols, rowIndex, columnIndex);

    mat &= mask;

    D bool sum;
    for (uint i = 0; i < rows; ++i)
        for (uint j = 0; j < cols; ++j)
            sum ^= mat[i,j];

    return sum;
}

/** \cond */

template <domain D, type T>
D T _matrixLookup(D T[[2]] mat, D uint rowIndex, D uint columnIndex) {
    uint[[1]] s = shape(mat);
    uint rows = s[0];
    uint cols = s[1];

    D T[[2]] mask = (T) matrixLookupBitmask(rows, cols, rowIndex, columnIndex);
    return sum (flatten (mat * mask));
}

/** \endcond */

template <domain D>
D uint8 matrixLookup(D uint8[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

template <domain D>
D uint16 matrixLookup(D uint16[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

template <domain D>
D uint32 matrixLookup(D uint32[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

template <domain D>
D uint matrixLookup(D uint[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

template <domain D>
D int8 matrixLookup(D int8[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

template <domain D>
D int16 matrixLookup(D int16[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

template <domain D>
D int32 matrixLookup(D int32[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

template <domain D>
D int matrixLookup(D int[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

template <domain D>
D float32 matrixLookup(D float32[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

template <domain D>
D float64 matrixLookup(D float64[[2]] mat, D uint rowIndex, D uint columnIndex) {
    return _matrixLookup (mat, rowIndex, columnIndex);
}

/** @}*/


/*******************************************************************************
********************************************************************************
**                                                                            **
**  vectorUpdate                                                             **
**                                                                            **
********************************************************************************
*******************************************************************************/

/** \addtogroup vectorupdate
 *  @{
 *  @brief Function for obliviously updating an element in the input vector
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int"
 *  @param vec - a 1-dimensional vector of supported type
 *  @param index - an \ref uint64 "uint" type scalar for specifying the element to replace
 *  @param newValue - a scalar value of the same type as the input vector
 *  @return returns a vector with the value at position **index** replaced by **newValue**
 */

template <domain D>
D bool[[1]] vectorUpdate(D bool[[1]] vec, D uint index, D bool newValue) {
    D bool[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}

template <domain D>
D int8[[1]] vectorUpdate(D int8[[1]] vec, D uint index, D int8 newValue) {
    D int8[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}

template <domain D>
D int16[[1]] vectorUpdate(D int16[[1]] vec, D uint index, D int16 newValue) {
    D int16[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}

template <domain D>
D int32[[1]] vectorUpdate(D int32[[1]] vec, D uint index, D int32 newValue) {
    D int32[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}

template <domain D>
D int64[[1]] vectorUpdate(D int64[[1]] vec, D uint index, D int64 newValue) {
    D int64[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}

template <domain D>
D uint8[[1]] vectorUpdate(D uint8[[1]] vec, D uint index, D uint8 newValue) {
    D uint8[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}

template <domain D>
D uint16[[1]] vectorUpdate(D uint16[[1]] vec, D uint index, D uint16 newValue) {
    D uint16[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}

template <domain D>
D uint32[[1]] vectorUpdate(D uint32[[1]] vec, D uint index, D uint32 newValue) {
    D uint32[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}

template <domain D>
D uint[[1]] vectorUpdate(D uint64[[1]] vec, D uint index, D uint64 newValue) {
    D uint[[1]] n(size(vec)) = newValue;
    return choose(vectorLookupBitmask(size(vec), index), n, vec);
}


/** @}*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  matrixUpdateRow                                                         **
**                                                                            **
********************************************************************************
*******************************************************************************/

/** \addtogroup matrixupdaterow
 *  @{
 *  @brief Function for obliviously updating a row in the input matrix
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int"
 *  @param mat - a matrix of supported type
 *  @param rowIndex - an \ref uint64 "uint" type scalar for specifying the row to replace
 *  @param newRow - a vector with new values
 *  @return returns a matrix where the row at **rowIndex** has been replaced with **newRow**
 */

/** \cond */

template <domain D, type T>
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

template <domain D>
D bool[[2]] matrixUpdateRow(D bool[[2]] mat, D uint rowIndex, D bool[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}

template <domain D>
D uint8[[2]] matrixUpdateRow(D uint8[[2]] mat, D uint rowIndex, D uint8[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}

template <domain D>
D uint16[[2]] matrixUpdateRow(D uint16[[2]] mat, D uint rowIndex, D uint16[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}

template <domain D>
D uint32[[2]] matrixUpdateRow(D uint32[[2]] mat, D uint rowIndex, D uint32[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}

template <domain D>
D uint[[2]] matrixUpdateRow(D uint[[2]] mat, D uint rowIndex, D uint[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}

template <domain D>
D int8[[2]] matrixUpdateRow(D int8[[2]] mat, D uint rowIndex, D int8[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}

template <domain D>
D int16[[2]] matrixUpdateRow(D int16[[2]] mat, D uint rowIndex, D int16[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}

template <domain D>
D int32[[2]] matrixUpdateRow(D int32[[2]] mat, D uint rowIndex, D int32[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}

template <domain D>
D int[[2]] matrixUpdateRow(D int[[2]] mat, D uint rowIndex, D int[[1]] newRow) {
    return _matrixUpdateRow (mat, rowIndex, newRow);
}



/** @}*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  matrixUpdateColumn                                                      **
**                                                                            **
********************************************************************************
*******************************************************************************/

/** \addtogroup matrixupdatecolumn
 *  @{
 *  @brief Function for obliviously updating a column in the input matrix
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int"
 *  @param mat - a matrix of supported type
 *  @param colIndex - an \ref uint64 "uint" type scalar for specifying the column to replace
 *  @param newCol - a vector with new values
 *  @return returns a matrix where the column at **colIndex** has been replaced with **newCol**
 */

/** \cond */

template <domain D, type T>
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

template <domain D>
D bool[[2]] matrixUpdateColumn(D bool[[2]] mat, D uint colIndex, D bool[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

template <domain D>
D uint8[[2]] matrixUpdateColumn(D uint8[[2]] mat, D uint colIndex, D uint8[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

template <domain D>
D uint16[[2]] matrixUpdateColumn(D uint16[[2]] mat, D uint colIndex, D uint16[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

template <domain D>
D uint32[[2]] matrixUpdateColumn(D uint32[[2]] mat, D uint colIndex, D uint32[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

template <domain D>
D uint[[2]] matrixUpdateColumn(D uint[[2]] mat, D uint colIndex, D uint[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

template <domain D>
D int8[[2]] matrixUpdateColumn(D int8[[2]] mat, D uint colIndex, D int8[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

template <domain D>
D int16[[2]] matrixUpdateColumn(D int16[[2]] mat, D uint colIndex, D int16[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

template <domain D>
D int32[[2]] matrixUpdateColumn(D int32[[2]] mat, D uint colIndex, D int32[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

template <domain D>
D int[[2]] matrixUpdateColumn(D int[[2]] mat, D uint colIndex, D int[[1]] newCol) {
    return _matrixUpdateColumn (mat, colIndex, newCol);
}

/** @}*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  matrixUpdate                                                             **
**                                                                            **
********************************************************************************
*******************************************************************************/

/** \addtogroup matrixupdate
 *  @{
 *  @brief Function for obliviously updating a value in the input matrix
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int"
 *  @param mat - a matrix of supported type
 *  @param rowIndex - an \ref uint64 "uint" type scalar for specifying the row in the input matrix
 *  @param colIndex - an \ref uint64 "uint" type scalar for specifying the column in the input matrix
 *  @param newValue - a new scalar value
 *  @return returns a matrix where the element at row **rowIndex** and column **colIndex** has been replaced with **newValue**
 */

/** \cond */

template <domain D, type T>
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

template <domain D>
D bool[[2]] matrixUpdate(D bool[[2]] mat, D uint rowIndex, D uint columnIndex, D bool newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

template <domain D>
D uint8[[2]] matrixUpdate(D uint8[[2]] mat, D uint rowIndex, D uint columnIndex, D uint8 newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

template <domain D>
D uint16[[2]] matrixUpdate(D uint16[[2]] mat, D uint rowIndex, D uint columnIndex, D uint16 newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

template <domain D>
D uint32[[2]] matrixUpdate(D uint32[[2]] mat, D uint rowIndex, D uint columnIndex, D uint32 newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

template <domain D>
D uint[[2]] matrixUpdate(D uint[[2]] mat, D uint rowIndex, D uint columnIndex, D uint newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

template <domain D>
D int8[[2]] matrixUpdate(D int8[[2]] mat, D uint rowIndex, D uint columnIndex, D int8 newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

template <domain D>
D int16[[2]] matrixUpdate(D int16[[2]] mat, D uint rowIndex, D uint columnIndex, D int16 newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

template <domain D>
D int32[[2]] matrixUpdate(D int32[[2]] mat, D uint rowIndex, D uint columnIndex, D int32 newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

template <domain D>
D int[[2]] matrixUpdate(D int[[2]] mat, D uint rowIndex, D uint columnIndex, D int newValue) {
    return _matrixUpdate (mat, rowIndex, columnIndex, newValue);
}

/** @}*/
/** @}*/

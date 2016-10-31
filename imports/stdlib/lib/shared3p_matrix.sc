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
module shared3p_matrix;

import stdlib;
import shared3p;
import matrix;

/**
* \endcond
*/
/**
* @file
* \defgroup shared3p_matrix shared3p_matrix.sc
* \defgroup shared3p_rowsums rowSums
* \defgroup shared3p_colsums colSums
* \defgroup shared3p_dotproduct dotProduct
* \defgroup shared3p_dotproduct_vec dotProduct[[1]]
* \defgroup shared3p_dotproduct_mat dotProduct[[2]]
* \defgroup shared3p_veclength vecLength
* \defgroup shared3p_unitvector unitVector
* \defgroup shared3p_crossproduct crossProduct
* \defgroup shared3p_crossproduct_vec crossProduct[[1]]
* \defgroup shared3p_crossproduct_mat crossProduct[[2]]
* \defgroup shared3p_matrixmultiplication matrixMultiplication
* \defgroup shared3p_matrixmultiplication_mat matrixMultiplication[[2]]
* \defgroup shared3p_matrixmultiplication_cube matrixMultiplication[[3]]
*/

/** \addtogroup shared3p_matrix
*@{
*
* @brief Module with functions for manipulating matrices and vectors (shared3p protection domain)
*/

/*******************************
    rowSums, colSums
********************************/

/** \cond */

template <domain D : shared3p, type T>
D T[[1]] _rowSums (D T[[2]] mat) {
    return sum (flatten(mat), shape(mat)[0]);
}

/** \endcond */

/** \addtogroup shared3p_rowsums
 *  @{
 *  @brief Function for summarizing the rows of a matrix
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @note When adding boolean values, the numerical value of boolean is used
 *  @param mat - a matrix of supported type
 *  @return returns a vector with the sums of each row in the input matrix
 */

template <domain D : shared3p>
D uint[[1]] rowSums (D bool[[2]] mat) {
    return sum(flatten(mat), shape(mat)[0]);
}

template <domain D : shared3p>
D uint8[[1]] rowSums (D uint8[[2]] mat) {
    return _rowSums (mat);
}

template <domain D : shared3p>
D uint16[[1]] rowSums (D uint16[[2]] mat) {
    return _rowSums (mat);
}

template <domain D : shared3p>
D uint32[[1]] rowSums (D uint32[[2]] mat) {
    return _rowSums (mat);
}

template <domain D : shared3p>
D uint[[1]] rowSums (D uint[[2]] mat) {
    return _rowSums (mat);
}

template <domain D : shared3p>
D int8[[1]] rowSums (D int8[[2]] mat) {
    return _rowSums (mat);
}

template <domain D : shared3p>
D int16[[1]] rowSums (D int16[[2]] mat) {
    return _rowSums (mat);
}

template <domain D : shared3p>
D int32[[1]] rowSums (D int32[[2]] mat) {
    return _rowSums (mat);
}

template <domain D : shared3p>
D int[[1]] rowSums (D int[[2]] mat) {
    return _rowSums (mat);
}

template <domain D : shared3p>
D float32[[1]] rowSums (D float32[[2]] mat) {
    return _rowSums (mat);
}

template <domain D : shared3p>
D float64[[1]] rowSums (D float64[[2]] mat) {
    return _rowSums (mat);
}

/** @}*/
/** \addtogroup shared3p_colsums
 *  @{
 *  @brief Function for summarizing the columns of a matrix
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @note When adding boolean values, the numerical value of boolean is used
 *  @param mat - a matrix of supported type
 *  @return returns a vector with the sums of each column in the input matrix
 */

template <domain D : shared3p>
D uint[[1]] colSums (D bool[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D uint8[[1]] colSums (D uint8[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D uint16[[1]] colSums (D uint16[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D uint32[[1]] colSums (D uint32[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D uint[[1]] colSums (D uint[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D int8[[1]] colSums (D int8[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D int16[[1]] colSums (D int16[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D int32[[1]] colSums (D int32[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D int[[1]] colSums (D int[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D float32[[1]] colSums (D float32[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D : shared3p>
D float64[[1]] colSums (D float64[[2]] mat) {
    return rowSums(transpose(mat));
}

/** @}*/

/*******************************
    dotProduct
********************************/

/** \cond */

template <domain D : shared3p, type T>
D T _dotProduct (D T[[1]] x, D T[[1]] y) {
    assert (size (x) == size (y));
    return sum (x * y);
}

template <domain D : shared3p, type T>
D T[[1]] _dotProduct (D T[[2]] x, D T[[2]] y) {
    assert (shapesAreEqual (x,y));
    return rowSums(x * y);
}

/** \endcond */

/** \addtogroup shared3p_dotproduct
 *  @{
 *  @brief Function for finding the dot product of two vectors/matrices
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 */

/** \addtogroup shared3p_dotproduct_vec
 *  @{
 *  @brief Function for finding the dot product of two vectors
 *  @note **D** - shared3p domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @return returns a scalar with the dot product of the two input vectors
 */

template <domain D : shared3p>
D uint8 dotProduct (D uint8[[1]] x, D uint8[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D uint16 dotProduct (D uint16[[1]] x, D uint16[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D uint32 dotProduct (D uint32[[1]] x, D uint32[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D uint dotProduct (D uint[[1]] x, D uint[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D int8 dotProduct (D int8[[1]] x, D int8[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D int16 dotProduct (D int16[[1]] x, D int16[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D int32 dotProduct (D int32[[1]] x, D int32[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D int dotProduct (D int[[1]] x, D int[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D float32 dotProduct (D float32[[1]] x, D float32[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D float64 dotProduct (D float64[[1]] x, D float64[[1]] y) {
    return _dotProduct (x, y);
}

/** @}*/
/** \addtogroup shared3p_dotproduct_mat
 *  @{
 *  @brief Function for finding the dot product of two matrices
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param x,y - matrices of supported type
 *  @return returns a vector with the dot product of each row of the two input matrices
 */

template <domain D : shared3p>
D uint8[[1]] dotProduct (D uint8[[2]] x, D uint8[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D uint16[[1]] dotProduct (D uint16[[2]] x, D uint16[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D uint32[[1]] dotProduct (D uint32[[2]] x, D uint32[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D uint[[1]] dotProduct (D uint[[2]] x, D uint[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D int8[[1]] dotProduct (D int8[[2]] x, D int8[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D int16[[1]] dotProduct (D int16[[2]] x, D int16[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D int32[[1]] dotProduct (D int32[[2]] x, D int32[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D int[[1]] dotProduct (D int[[2]] x, D int[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D float32[[1]] dotProduct (D float32[[2]] x, D float32[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D : shared3p>
D float64[[1]] dotProduct (D float64[[2]] x, D float64[[2]] y) {
    return _dotProduct (x, y);
}
/** @}*/
/** @}*/

/*******************************
    vecLength, unitVector
********************************/

/** \addtogroup shared3p_veclength
 *  @{
 *  @brief Function for finding the length of a vector
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 */

/**
*  @param x - vector of supported type
*  @return returns the length of the vector
*/
template <domain D : shared3p>
D float32 vecLength (D float32[[1]] x) {
    return sqrt (dotProduct (x, x));
}

/**
*  @param x - vector of supported type
*  @return returns the length of the vector
*/
template <domain D : shared3p>
D float64 vecLength (D float64[[1]] x) {
    return sqrt (dotProduct (x, x));
}

/**
*  @param x - matrix of supported type
*  @return returns a vector with length of each row in the matrix
*/
template <domain D : shared3p>
D float32[[1]] vecLength (D float32[[2]] x) {
    return sqrt (dotProduct (x, x));
}

/**
*  @param x - matrix of supported type
*  @return returns a vector with length of each row in the matrix
*/
template <domain D : shared3p>
D float64[[1]] vecLength (D float64[[2]] x) {
    return sqrt (dotProduct (x, x));
}

/** @}*/
/** \addtogroup shared3p_unitvector
 *  @{
 *  @brief Function for finding the unit vector of the input vector
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 */

/** \cond */

template <domain D : shared3p, type T>
D T[[1]] _unitVector (D T[[1]] x) {
    assert(size(x) > 0);
    D T invLen = 1.0 / vecLength(x);
    return x * invLen;
}

template <domain D : shared3p, type T>
D T [[2]] _unitVector (D T [[2]] x) {
    assert(shape(x)[1] > 0);
    D T [[1]] invLen = 1.0 / vecLength (x);
    // Expand invLen
    uint[[1]] xShape = shape (x);
    D T [[2]] invLenExpanded (xShape[0], xShape[1]);
    for (uint i = 0; i < xShape[0]; ++i) {
        invLenExpanded[i, :] = invLen[i];
    }

    return x * invLenExpanded;
}

/** \endcond */

/**
*  @param x - vector of supported type
*  @return returns the unit vector for the input vector
*/
template <domain D : shared3p>
D float32[[1]] unitVector (D float32[[1]] x) {
    return _unitVector (x);
}

/**
*  @param x - vector of supported type
*  @return returns the unit vector for the input vector
*/
template <domain D : shared3p>
D float64[[1]] unitVector (D float64[[1]] x) {
    return _unitVector (x);
}

/**
*  @param x - matrix of supported type
*  @return returns a matrix with the unit vector of each row in the input matrix
*/
template <domain D : shared3p>
D float32[[2]] unitVector (D float32[[2]] x) {
    return _unitVector (x);
}

/**
*  @param x - matrix of supported type
*  @return returns a matrix with the unit vector of each row in the input matrix
*/
template <domain D : shared3p>
D float64[[2]] unitVector (D float64[[2]] x) {
    return _unitVector (x);
}
/** @}*/



/*******************************
    crossProduct
********************************/

/** \cond */

template <domain D : shared3p, type T>
D T[[1]] _crossProduct (D T[[1]] x, D T[[1]] y) {
    assert (size (x) == 3 && size (y) == 3);
    D T[[1]] prod =
        {x[1], x[2], x[0], x[2], x[0], x[1]} *
        {y[2], y[0], y[1], y[1], y[2], y[0]};
    return prod[0 : 3] - prod[3 : 6];
}

template <domain D : shared3p, type T>
D T[[2]] _crossProduct (D T[[2]] x, D T[[2]] y) {
    uint[[1]] xShape = shape (x);
    uint[[1]] yShape = shape (y);
    assert (xShape[1] == 3 && yShape[1] == 3 && xShape[0] == yShape[0]);

    D T[[2]] result (xShape[0], xShape[1]);
    D T[[2]] parProdA (xShape[0], xShape[1] * 2),
             parProdB (xShape[0], xShape[1] * 2),
             parProdRes (xShape[0], xShape[1] * 2);

    parProdA[:, 0] = x[:, 1];
    parProdB[:, 0] = y[:, 2];
    parProdA[:, 3] = x[:, 2];
    parProdB[:, 3] = y[:, 1];
    parProdA[:, 1] = x[:, 2];
    parProdB[:, 1] = y[:, 0];
    parProdA[:, 4] = x[:, 0];
    parProdB[:, 4] = y[:, 2];
    parProdA[:, 2] = x[:, 0];
    parProdB[:, 2] = y[:, 1];
    parProdA[:, 5] = x[:, 1];
    parProdB[:, 5] = y[:, 0];

    parProdRes = parProdA * parProdB;
    result = parProdRes[:, 0 : 3] - parProdRes[:, 3 : 6];
    return result;
}

/** \endcond */

/** \addtogroup shared3p_crossproduct
 *  @{
 *  @brief Function for finding the cross product of two vectors/matrices
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 */


 /** \addtogroup shared3p_crossproduct_vec
 *  @{
 *  @brief Function for finding the cross product of two vectors
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param x,y - vectors of supported type
 *  @return returns a vector with the cross product of the two input vectors
 */


template <domain D : shared3p>
D int8[[1]] crossProduct (D int8[[1]] x, D int8[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D int16[[1]] crossProduct (D int16[[1]] x, D int16[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D int32[[1]] crossProduct (D int32[[1]] x, D int32[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D int[[1]] crossProduct (D int[[1]] x, D int[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D float32[[1]] crossProduct (D float32[[1]] x, D float32[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D float64[[1]] crossProduct (D float64[[1]] x, D float64[[1]] y) {
    return _crossProduct (x, y);
}

/** @}*/
/** \addtogroup shared3p_crossproduct_mat
 *  @{
 *  @brief Function for finding the cross product of two matrices
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param x,y - matrices of supported type
 *  @return returns a matrix with the cross product of each row of the two input matrices
 */

template <domain D : shared3p>
D int8[[2]] crossProduct (D int8[[2]] x, D int8[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D int16[[2]] crossProduct (D int16[[2]] x, D int16[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D int32[[2]] crossProduct (D int32[[2]] x, D int32[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D int[[2]] crossProduct (D int[[2]] x, D int[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D float32[[2]] crossProduct (D float32[[2]] x, D float32[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D : shared3p>
D float64[[2]] crossProduct (D float64[[2]] x, D float64[[2]] y) {
    return _crossProduct (x, y);
}


/** @}*/
/** @}*/


/*****************************************************
    matrixMultiplication
*****************************************************/

/** \cond */

template <domain D : shared3p, type T>
D T[[2]] _matrixMultiplication (D T[[2]] x, D T[[2]] y) {
    // For parallelisation
    uint [[1]] xShape = shape (x);
    uint [[1]] yShape = shape (y);

    // no. of columns of x must equal no. of rows of y
    assert (xShape[1] == yShape[0]);
    uint commonDim = xShape[1];

    D T[[1]] mulVec1 (xShape[0] * yShape[1] * commonDim),
                   mulVec2 (xShape[0] * yShape[1] * commonDim),
                   product (xShape[0] * yShape[1] * commonDim);

    // At the moment our matrices are kept in memory in row major order
    // We only take the column we need from memory once
    // This is also why our cycles run first over y and then over x
    D T[[1]] yColumn (commonDim);
    for(uint i = 0; i < yShape[1]; i++) {
        yColumn = y[:, i];
        for(uint j = 0; j < xShape[0]; j++) {
            mulVec1[(xShape[0] * i + j) * commonDim : (xShape[0] * i + j + 1) * commonDim] = x[j, :];
            mulVec2[(xShape[0] * i + j) * commonDim : (xShape[0] * i + j + 1) * commonDim] = yColumn;
        }
    }

    product = mulVec1 * mulVec2;

    D T[[2]] result (xShape[0], yShape[1]);
    D T[[1]] resultVec (xShape[0] * yShape[1]);

    resultVec = sum (product, xShape[0] * yShape[1]);

    for (uint i = 0; i < yShape[1]; i++){
        result[:, i] = resultVec[i * xShape[0] : (i + 1) * xShape[0]];
    }

    return result;
}

template <domain D : shared3p,  type T>
D T[[3]] _matrixMultiplication (D T[[3]] x, D T[[3]] y) {
    // We multiply across the last two dimensions
    // And return a vector of product matrices

    // For parallelisation
    uint [[1]] xShape = shape (x);
    uint [[1]] yShape = shape (y);

    // no. of columns of x must equal no. of rows of y
    // Also, there should be an equal no. of matrices in both structures
    assert (xShape[2] == yShape[1] && xShape[0] == yShape[0]);

    uint commonDim = xShape[2];
    uint count = xShape[0];
    uint matrixSize = xShape[1] * yShape[2];

    D T[[1]] mulVec1 (matrixSize * commonDim * count),
             mulVec2 (matrixSize * commonDim * count),
             product (matrixSize * commonDim * count);

    // At the moment our matrices are kept in memory in row major order
    // We only take the column we need from memory once
    // This is also why our cycles run first over y and then over x
    D T[[1]] yColumn (commonDim * count);


    // TODO: this is rather slow memory copy
    for(uint m = 0; m < count; ++m) {
        for(uint i = 0; i < yShape[2]; ++i) {
            yColumn = y[m, :, i];
            for(uint j = 0; j < xShape[1]; ++j) {
                mulVec1[(xShape[1] * i + j + m * matrixSize) * commonDim : (xShape[1] * i + m * matrixSize + j + 1) * commonDim] = x[m, j, :];
                mulVec2[(xShape[1] * i + j + m * matrixSize) * commonDim : (xShape[1] * i + m * matrixSize + j + 1) * commonDim] = yColumn;
            }
        }
    }

    product = mulVec1 * mulVec2;

    D T[[3]] result (count, xShape[1], yShape[2]);
    D T[[1]] resultVec (count * matrixSize);

    resultVec = sum (product, (matrixSize * count));

    for (uint m = 0; m < count; m++){
        for (uint i = 0; i < yShape[2]; i++){
            result[m, :, i] = resultVec [i * xShape[1] + m * matrixSize : (i + 1) * xShape[1] + m * matrixSize];
        }
    }

    return result;
}

template <domain D : shared3p, type T>
D T[[2]] _intMatrixMultiplication(D T[[2]] x, D T[[2]] y) {
    uint64[[1]] m (2) = shape(x);
    uint64[[1]] n (2) = shape(y);
    assert(m[1] == n[0]);
    D T[[2]] z (m[0], n[1]);
    __syscall("shared3p::mat_mult_$T\_vec", __domainid(D), x, y, z, __cref m[0], __cref m[1], __cref n[1]);
    return z;
}

/** \endcond */

/** \addtogroup shared3p_matrixmultiplication
 *  @{
 *  @brief Function for multiplying two matrices
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 */

/** \addtogroup shared3p_matrixmultiplication_mat
 *  @{
 *  @brief Function for multiplying two matrices
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @warning no. of columns of x must equal no. of rows of y
 *  @param x,y - 2-dimensional matrices of supported type and shape
 *  @return returns the matrix of x*y
 */

template <domain D : shared3p>
D uint8[[2]] matrixMultiplication (D uint8[[2]] x, D uint8[[2]] y) {
    return _intMatrixMultiplication (x, y);
}

template <domain D : shared3p>
D uint16[[2]] matrixMultiplication (D uint16[[2]] x, D uint16[[2]] y) {
    return _intMatrixMultiplication (x, y);
}

template <domain D : shared3p>
D uint32[[2]] matrixMultiplication (D uint32[[2]] x, D uint32[[2]] y) {
    return _intMatrixMultiplication (x, y);
}

template <domain D : shared3p>
D uint[[2]] matrixMultiplication (D uint[[2]] x, D uint[[2]] y) {
    return _intMatrixMultiplication (x, y);
}

template <domain D : shared3p>
D int8[[2]] matrixMultiplication (D int8[[2]] x, D int8[[2]] y) {
    return _intMatrixMultiplication (x, y);
}

template <domain D : shared3p>
D int16[[2]] matrixMultiplication (D int16[[2]] x, D int16[[2]] y) {
    return _intMatrixMultiplication (x, y);
}

template <domain D : shared3p>
D int32[[2]] matrixMultiplication (D int32[[2]] x, D int32[[2]] y) {
    return _intMatrixMultiplication (x, y);
}

template <domain D : shared3p>
D int[[2]] matrixMultiplication (D int[[2]] x, D int[[2]] y) {
    return _intMatrixMultiplication (x, y);
}

template <domain D : shared3p>
D float32[[2]] matrixMultiplication (D float32[[2]] x, D float32[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D : shared3p>
D float64[[2]] matrixMultiplication (D float64[[2]] x, D float64[[2]] y) {
    return _matrixMultiplication (x, y);
}

/** @}*/
/** \addtogroup shared3p_matrixmultiplication_cube
 *  @{
 *  @brief Function for multiplying two matrices
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @warning no. of columns of x must equal no. of rows of y. Also, there should be an equal no. of matrices in both structures
 *  @param x,y - 3-dimensional matrices of supported type and shape
 *  @return We multiply across the last two dimensions and return a vector of product matrices
 */

template <domain D : shared3p>
D uint8[[3]] matrixMultiplication (D uint8[[3]] x, D uint8[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D : shared3p>
D uint16[[3]] matrixMultiplication (D uint16[[3]] x, D uint16[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D : shared3p>
D uint32[[3]] matrixMultiplication (D uint32[[3]] x, D uint32[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D : shared3p>
D uint[[3]] matrixMultiplication (D uint[[3]] x, D uint[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D : shared3p>
D int8[[3]] matrixMultiplication (D int8[[3]] x, D int8[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D : shared3p>
D int16[[3]] matrixMultiplication (D int16[[3]] x, D int16[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D : shared3p>
D int32[[3]] matrixMultiplication (D int32[[3]] x, D int32[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D : shared3p>
D int[[3]] matrixMultiplication (D int[[3]] x, D int[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D : shared3p>
D float32[[3]] matrixMultiplication (D float32[[3]] x, D float32[[3]] y) {
    return _matrixMultiplication (x, y);
}
template <domain D : shared3p>
D float64[[3]] matrixMultiplication (D float64[[3]] x, D float64[[3]] y) {
    return _matrixMultiplication (x, y);
}

/** @}*/

/** @}*/

/** @}*/

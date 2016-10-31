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




/// \todo Need vecLength and unitVector, but waiting for public sqrt.
/// \todo ? inverse, det, eigenvectors?
/**
* \cond
*/
module matrix;

import stdlib;
/**
* \endcond
*/
/**
* @file
* \defgroup matrix matrix.sc
* \defgroup transpose transpose
* \defgroup rowsums rowSums
* \defgroup unitmatrix unitMatrix
* \defgroup colsums colSums
* \defgroup veclength vecLength
* \defgroup unitvector unitVector
* \defgroup crossproduct crossProduct
* \defgroup dotproduct dotProduct
* \defgroup dotproduct_vec dotProduct[[1]]
* \defgroup dotproduct_mat dotProduct[[2]]
* \defgroup crossproduct_vec crossProduct[[1]]
* \defgroup crossproduct_mat crossProduct[[2]]
* \defgroup matrixmultiplication matrixMultiplication
* \defgroup matrixmultiplication_mat matrixMultiplication[[2]]
* \defgroup matrixmultiplication_cube matrixMultiplication[[3]]
* \defgroup diag_matrixmultiplication diagMatrixMultiplication
* \defgroup diag_matrixmultiplication_mat diagMatrixMultiplication[[2]]
* \defgroup diag_matrixmultiplication_cube diagMatrixMultiplication[[3]]
* \defgroup determinant determinant
*/

/*******************************
    transpose
********************************/

/** \addtogroup matrix
*@{
*
* @brief Module with functions for manipulating matrices and vectors
*/

/** \addtogroup transpose
 *  @{
 *  @brief Function for transposing matrices
 *  @note **D** - all protection domains
 *  @note **T** - any \ref data_types "data" type
 */

/**
* @param mat - a 2-dimensional matrix
* @return returns the transposed version of the input matrix
*/
template <domain D, type T>
D T[[2]] transpose (D T[[2]] mat) {
    uint[[1]] matShape = shape (mat);
    D T[[2]] result (matShape[1], matShape[0]);

    for(uint i = 0; i < matShape[1]; ++i) {
        result[i, :] = mat[:, i];
    }
    return result;
}

/**
* @param arr - a 3-dimensional array
* @note Transposes across the last two dimensions
* @return returns a 2-dimensional array transposed across the last two dimension
*/
template <domain D, type T>
D T[[3]] transpose (D T[[3]] arr) {
    uint[[1]] matShape = shape (arr);
    D T[[3]] result (matShape[0], matShape[2], matShape[1]);

    for(uint j = 0; j < matShape[0]; ++j) {
        for(uint i = 0; i < matShape[1]; ++i) {
            result[j, :, i] = arr[j, i, :];
        }
    }
    return result;
}

/** @}*/

/*******************************
      Unit matrix
********************************/

/** \cond */

template <domain D, type T>
D T[[2]] _unitMatrix (uint n) {
    T[[2]] mat (n, n);
    for(uint i = 0; i < n; ++i){
        mat[i, i] = 1;
    }

    return mat;
}

/** \endcond */

/** \addtogroup unitmatrix
 *  @{
 *  @brief Function for creating a unit matrix
 *  @note **D** - all protection domains
 *  @return returns an unit matrix of size n
 */
template <domain D>
D bool[[2]] unitMatrix (uint n) {
    bool[[2]] mat (n, n);
    for(uint i = 0; i < n; ++i){
        mat[i, i] = true;
    }

    return mat;
}

template <domain D>
D uint8[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

template <domain D>
D uint16[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

template <domain D>
D uint32[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

template <domain D>
D uint64[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

template <domain D>
D int8[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

template <domain D>
D int16[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

template <domain D>
D int32[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

template <domain D>
D int64[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

template <domain D>
D float32[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

template <domain D>
D float64[[2]] unitMatrix (uint n) {
    return _unitMatrix (n);
}

/** @}*/

/*******************************
    rowSums, colSums
********************************/

/** \cond */

template <domain D, type T>
D T[[1]] _rowSums (D T[[2]] mat) {
    return sum(flatten(mat), shape(mat)[0]);
}

/** \endcond */

/** \addtogroup rowsums
 *  @{
 *  @brief Function for summarizing the rows of a matrix
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param mat - a matrix of supported type
 *  @return returns a vector with the sums of each row in the input matrix
*/

template <domain D>
D uint[[1]] rowSums (D bool[[2]] mat) {
    return sum(flatten(mat), shape(mat)[0]);
}

template <domain D>
D uint8[[1]] rowSums (D uint8[[2]] mat) {
    return _rowSums (mat);
}

template <domain D>
D uint16[[1]] rowSums (D uint16[[2]] mat) {
    return _rowSums (mat);
}

template <domain D>
D uint32[[1]] rowSums (D uint32[[2]] mat) {
    return _rowSums (mat);
}

template <domain D>
D uint[[1]] rowSums (D uint[[2]] mat) {
    return _rowSums (mat);
}

template <domain D>
D int8[[1]] rowSums (D int8[[2]] mat) {
    return _rowSums (mat);
}

template <domain D>
D int16[[1]] rowSums (D int16[[2]] mat) {
    return _rowSums (mat);
}

template <domain D>
D int32[[1]] rowSums (D int32[[2]] mat) {
    return _rowSums (mat);
}

template <domain D>
D int[[1]] rowSums (D int[[2]] mat) {
    return _rowSums (mat);
}

template <domain D>
D float32[[1]] rowSums (D float32[[2]] mat) {
    return _rowSums (mat);
}

template <domain D>
D float64[[1]] rowSums (D float64[[2]] mat) {
    return _rowSums (mat);
}

/** @}*/

/** \addtogroup colsums
 *  @{
 *  @brief Function for summarizing the columns of a matrix
 *  @note **D** - all protection domains
 *  @note Supported types - \ref bool "bool" / \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param mat - a matrix of supported type
 *  @return returns a vector with the sums of each column in the input matrix
 */

template <domain D>
D uint[[1]] colSums (D bool[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D uint8[[1]] colSums (D uint8[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D uint16[[1]] colSums (D uint16[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D uint32[[1]] colSums (D uint32[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D uint[[1]] colSums (D uint[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D int8[[1]] colSums (D int8[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D int16[[1]] colSums (D int16[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D int32[[1]] colSums (D int32[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D int[[1]] colSums (D int[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D float32[[1]] colSums (D float32[[2]] mat) {
    return rowSums(transpose(mat));
}

template <domain D>
D float64[[1]] colSums (D float64[[2]] mat) {
    return rowSums(transpose(mat));
}

/** @}*/

/*******************************
    dotProduct
********************************/

/** \cond */

template <domain D, type T>
D T _dotProduct (D T[[1]] x, D T[[1]] y) {
    assert (size (x) == size (y));
    return sum (x * y);
}

template <domain D, type T>
D T[[1]] _dotProduct (D T[[2]] x, D T[[2]] y) {
    assert (shapesAreEqual (x,y));
    return rowSums(x * y);
}

/** \endcond */

/** \addtogroup dotproduct
 *  @{
 *  @brief Function for finding the dot product of two vectors/matrices
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 */

/** \addtogroup dotproduct_vec
 *  @{
 *  @brief Function for finding the dot product of two vectors
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @return returns a scalar with the dot product of the two input vectors
 */

template <domain D>
D uint8 dotProduct (D uint8[[1]] x, D uint8[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D uint16 dotProduct (D uint16[[1]] x, D uint16[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D uint32 dotProduct (D uint32[[1]] x, D uint32[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D uint dotProduct (D uint[[1]] x, D uint[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D int8 dotProduct (D int8[[1]] x, D int8[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D int16 dotProduct (D int16[[1]] x, D int16[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D int32 dotProduct (D int32[[1]] x, D int32[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D int dotProduct (D int[[1]] x, D int[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D float32 dotProduct (D float32[[1]] x, D float32[[1]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D float64 dotProduct (D float64[[1]] x, D float64[[1]] y) {
    return _dotProduct (x, y);
}

/** @}*/
/** \addtogroup dotproduct_mat
 *  @{
 *  @brief Function for finding the dot product of two matrices
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param x,y - matrices of supported type
 *  @return returns a vector with the dot product of each row of the two input matrices
 */

template <domain D>
D uint8[[1]] dotProduct (D uint8[[2]] x, D uint8[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D uint16[[1]] dotProduct (D uint16[[2]] x, D uint16[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D uint32[[1]] dotProduct (D uint32[[2]] x, D uint32[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D uint[[1]] dotProduct (D uint[[2]] x, D uint[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D int8[[1]] dotProduct (D int8[[2]] x, D int8[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D int16[[1]] dotProduct (D int16[[2]] x, D int16[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D int32[[1]] dotProduct (D int32[[2]] x, D int32[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D int[[1]] dotProduct (D int[[2]] x, D int[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D float32[[1]] dotProduct (D float32[[2]] x, D float32[[2]] y) {
    return _dotProduct (x, y);
}

template <domain D>
D float64[[1]] dotProduct (D float64[[2]] x, D float64[[2]] y) {
    return _dotProduct (x, y);
}

/** @}*/
/** @}*/

/*******************************
    vecLength
********************************/

/** \addtogroup veclength
 *  @{
 *  @brief Function for finding the length of a vector
 *  @note Only for public domain (at this point only public sqrt is in scope).
 *  @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 */

/**
*  @param x - vector of supported type
*  @return returns the length of the vector
*/
float32 vecLength (float32[[1]] x) {
    return sqrt (dotProduct (x, x));
}

/**
*  @param x - vector of supported type
*  @return returns the length of the vector
*/
float64 vecLength (float64[[1]] x) {
    return sqrt (dotProduct (x, x));
}

/**
*  @param x - matrix of supported type
*  @return returns a vector with length of each row in the matrix
*/
float32[[1]] vecLength (float32[[2]] x) {
    return sqrt (dotProduct (x, x));
}

/**
*  @param x - matrix of supported type
*  @return returns a vector with length of each row in the matrix
*/
float64[[1]] vecLength (float64[[2]] x) {
    return sqrt (dotProduct (x, x));
}

/** @}*/

/*******************************
    unitVector
********************************/

/** \cond */

template <type T>
T[[1]] _unitVector (T[[1]] x) {
    assert(size(x) > 0);
    T invLen = 1.0 / vecLength(x);
    return x * invLen;
}

template <type T>
T [[2]] _unitVector (T [[2]] x) {
    assert(shape(x)[1] > 0);
    T [[1]] invLen = 1.0 / vecLength (x);
    // Expand invLen
    uint[[1]] xShape = shape (x);
    T [[2]] invLenExpanded (xShape[0], xShape[1]);
    for (uint i = 0; i < xShape[0]; ++i) {
        invLenExpanded[i, :] = invLen[i];
    }

    return x * invLenExpanded;
}

/** \endcond */

/** \addtogroup unitvector
 *  @{
 *  @brief Function for finding the unit vector of the input vector
 *  @note Only for public domain (at this point only public sqrt is in scope).
 *  @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 */

/**
*  @param x - vector of supported type
*  @return returns the unit vector for the input vector
*/
float32[[1]] unitVector (float32[[1]] x) {
    return _unitVector (x);
}

/**
*  @param x - vector of supported type
*  @return returns the unit vector for the input vector
*/
float64[[1]] unitVector (float64[[1]] x) {
    return _unitVector (x);
}

/**
*  @param x - matrix of supported type
*  @return returns a matrix with the unit vector of each row in the input matrix
*/
float32[[2]] unitVector (float32[[2]] x) {
    return _unitVector (x);
}

/**
*  @param x - matrix of supported type
*  @return returns a matrix with the unit vector of each row in the input matrix
*/
float64[[2]] unitVector (float64[[2]] x) {
    return _unitVector (x);
}
/** @}*/

/*******************************
    crossProduct
********************************/

/** \cond */

template <domain D, type T>
D T[[1]] _crossProduct (D T[[1]] x, D T[[1]] y) {
    assert (size (x) == 3 && size (y) == 3);
    D T[[1]] prod =
        {x[1], x[2], x[0], x[2], x[0], x[1]} *
        {y[2], y[0], y[1], y[1], y[2], y[0]};
    return prod[0 : 3] - prod[3 : 6];
}

template <domain D, type T>
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

/** \addtogroup crossproduct
 *  @{
 *  @brief Function for finding the cross product of two vectors/matrices
 *  @note **D** - all protection domains
 *  @note Supported types - \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 */


 /** \addtogroup crossproduct_vec
 *  @{
 *  @brief Function for finding the cross product of two vectors
 *  @note **D** - all protection domains
 *  @note Supported types - \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param x,y - vectors of supported type
 *  @return returns a vector with the cross product of the two input vectors
 */

template <domain D>
D int8[[1]] crossProduct (D int8[[1]] x, D int8[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D int16[[1]] crossProduct (D int16[[1]] x, D int16[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D int32[[1]] crossProduct (D int32[[1]] x, D int32[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D int[[1]] crossProduct (D int[[1]] x, D int[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D float32[[1]] crossProduct (D float32[[1]] x, D float32[[1]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D float64[[1]] crossProduct (D float64[[1]] x, D float64[[1]] y) {
    return _crossProduct (x, y);
}

/** @}*/
/** \addtogroup crossproduct_mat
 *  @{
 *  @brief Function for finding the cross product of two matrices
 *  @note **D** - all protection domains
 *  @note Supported types - \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @param x,y - matrices of supported type
 *  @return returns a matrix with the cross product of each row of the two input matrices
 */


template <domain D>
D int8[[2]] crossProduct (D int8[[2]] x, D int8[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D int16[[2]] crossProduct (D int16[[2]] x, D int16[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D int32[[2]] crossProduct (D int32[[2]] x, D int32[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D int[[2]] crossProduct (D int[[2]] x, D int[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D float32[[2]] crossProduct (D float32[[2]] x, D float32[[2]] y) {
    return _crossProduct (x, y);
}

template <domain D>
D float64[[2]] crossProduct (D float64[[2]] x, D float64[[2]] y) {
    return _crossProduct (x, y);
}

/** @}*/
/** @}*/


/*******************************
    matrixMultiplication
********************************/

/** \cond */

template <domain D, type T>
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

template <domain D,  type T>
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

/** \endcond */

/** \addtogroup matrixmultiplication
 *  @{
 *  @brief Function for multiplying two matrices
 *  @note **D** - any protection domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 */

/** \addtogroup matrixmultiplication_mat
 *  @{
 *  @brief Function for multiplying two matrices
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @warning no. of columns of x must equal no. of rows of y
 *  @param x,y - matrices of supported type and shape
 *  @return returns the matrix of x*y
 */
template <domain D>
D uint8[[2]] matrixMultiplication (D uint8[[2]] x, D uint8[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D uint16[[2]] matrixMultiplication (D uint16[[2]] x, D uint16[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D uint32[[2]] matrixMultiplication (D uint32[[2]] x, D uint32[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D uint[[2]] matrixMultiplication (D uint[[2]] x, D uint[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D int8[[2]] matrixMultiplication (D int8[[2]] x, D int8[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D int16[[2]] matrixMultiplication (D int16[[2]] x, D int16[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D int32[[2]] matrixMultiplication (D int32[[2]] x, D int32[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D int[[2]] matrixMultiplication (D int[[2]] x, D int[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D float32[[2]] matrixMultiplication (D float32[[2]] x, D float32[[2]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D float64[[2]] matrixMultiplication (D float64[[2]] x, D float64[[2]] y) {
    return _matrixMultiplication (x, y);
}

/** @} */

/** \addtogroup matrixmultiplication_cube
 *  @{
 *  @brief Function for multiplying two matrices
 *  @note **D** - any protection domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @warning no. of columns of x must equal no. of rows of y. Also, there should be an equal no. of matrices in both structures
 *  @param x,y - 3-dimensional matrices of supported type and shape
 *  @return We multiply across the last two dimensions and return a vector of product matrices
 */

template <domain D>
D uint8[[3]] matrixMultiplication (D uint8[[3]] x, D uint8[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D uint16[[3]] matrixMultiplication (D uint16[[3]] x, D uint16[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D uint32[[3]] matrixMultiplication (D uint32[[3]] x, D uint32[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D uint[[3]] matrixMultiplication (D uint[[3]] x, D uint[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D int8[[3]] matrixMultiplication (D int8[[3]] x, D int8[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D int16[[3]] matrixMultiplication (D int16[[3]] x, D int16[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D int32[[3]] matrixMultiplication (D int32[[3]] x, D int32[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D int[[3]] matrixMultiplication (D int[[3]] x, D int[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D float32[[3]] matrixMultiplication (D float32[[3]] x, D float32[[3]] y) {
    return _matrixMultiplication (x, y);
}

template <domain D>
D float64[[3]] matrixMultiplication (D float64[[3]] x, D float64[[3]] y) {
    return _matrixMultiplication (x, y);
}

/** @} */

/** @} */

/*****************************************************
    diagMatrixMultiplication
*****************************************************/

/** \cond */

template <domain D, type T>
D T[[2]] _diagMatrixMultiplication (D T[[2]] x, D T[[2]] y) {

    uint [[1]] xShape = shape (x);
    uint [[1]] yShape = shape (y);

    // We assume that matrix y is diagonal, therefore y must be square
    assert (yShape[0] == yShape[1]);

    // no. of columns of x must equal no. of rows of y
    assert (xShape[1] == yShape[0]);

    uint commonDim = xShape[1];

    D T[[1]] mulVec1 (xShape[0] * yShape[1]),
             mulVec2 (xShape[0] * yShape[1]),
             product (xShape[0] * yShape[1]);

    // We only use the elements on the diagonal
    // Also, note that yShape[1] == commonDim
    for(uint i = 0; i < yShape[1]; i++) {
        for(uint j = 0; j < xShape[0]; j++) {
            mulVec1[i + j * yShape[1]] = x[j, i];
            mulVec2[i + j * yShape[1]] = y[i, i];
        }
    }

    product = mulVec1 * mulVec2;

    D T[[2]] result = reshape (product, xShape[0], yShape[1]);

    return result;
}

template <domain D, type T>
D T[[3]] _diagMatrixMultiplication (D T[[3]] x, D T[[3]] y) {

    // We multiply across the first two dimensions
    // And return a vector of product matrices
    uint [[1]] xShape = shape (x);
    uint [[1]] yShape = shape (y);

    // We assume that matrix y is diagonal, therefore y must be square
    assert (yShape[1] == yShape[2]);

    // no. of columns of x must equal no. of rows of y
    // Also, there should be an equal no. of matrices in both structures
    assert (xShape[2] == yShape[1] && xShape[0] == yShape[0]);

    uint commonDim = xShape[2];
    uint count = xShape[0];
    uint matrixSize = xShape[1] * yShape[2];

    D T[[1]] mulVec1 (xShape[1] * yShape[2] * count),
             mulVec2 (xShape[1] * yShape[2] * count),
             product (xShape[1] * yShape[2] * count);

    // We only use the elements on the diagonal
    // Also, note that yShape[2] == commonDim
    for(uint m = 0; m < count; m++) {
        for(uint i = 0; i < yShape[2]; i++) {
            for(uint j = 0; j < xShape[1]; j++) {
                mulVec1[i + j * yShape[2] + m * matrixSize] = x[m, j, i];
                mulVec2[i + j * yShape[2] + m * matrixSize] = y[m, i, i];
            }
        }
    }

    product = mulVec1 * mulVec2;

    D T[[3]] result = reshape (product, count, xShape[1], yShape[2]);

    return result;
}

/** \endcond */


/** \addtogroup diag_matrixmultiplication
 *  @{
 *  @brief Function for multiplying two diagonal matrices
 *  @note **D** - any protection domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 */

/** \addtogroup diag_matrixmultiplication_mat
 *  @{
 *  @brief Function for multiplying two diagonal matrices
 *  @note **D** - any protection domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @warning NB! This matrix multiplication is very conditional. Before using, make sure that your matrices are in the right format. **y** must be diagonal
 *  @param x,y - 2-dimensional matrices of supported type and shape
 *  @return returns the matrix of x*y
 */

template <domain D>
D uint8[[2]] diagMatrixMultiplication (D uint8[[2]] x, D uint8[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D uint16[[2]] diagMatrixMultiplication (D uint16[[2]] x, D uint16[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D uint32[[2]] diagMatrixMultiplication (D uint32[[2]] x, D uint32[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D uint[[2]] diagMatrixMultiplication (D uint[[2]] x, D uint[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D int8[[2]] diagMatrixMultiplication (D int8[[2]] x, D int8[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D int16[[2]] diagMatrixMultiplication (D int16[[2]] x, D int16[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D int32[[2]] diagMatrixMultiplication (D int32[[2]] x, D int32[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D int[[2]] diagMatrixMultiplication (D int[[2]] x, D int[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D float32[[2]] diagMatrixMultiplication (D float32[[2]] x, D float32[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D float64[[2]] diagMatrixMultiplication (D float64[[2]] x, D float64[[2]] y) {
    return _diagMatrixMultiplication (x, y);
}

/** @}*/

/** \addtogroup diag_matrixmultiplication_cube
 *  @{
 *  @brief Function for multiplying two diagonal matrices
 *  @note **D** - any protection domain
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref float32 "float32" / \ref float64 "float64"
 *  @warning NB! This matrix multiplication is very conditional. Before using, make sure that your matrices are in the right format. **y** must be diagonal
 *  @param x,y - 3-dimensional matrices of supported type and shape
 *  @return We multiply across the last two dimensions and return a vector of product matrices
 */


template <domain D>
D uint8[[3]] diagMatrixMultiplication (D uint8[[3]] x, D uint8[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D uint16[[3]] diagMatrixMultiplication (D uint16[[3]] x, D uint16[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D uint32[[3]] diagMatrixMultiplication (D uint32[[3]] x, D uint32[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D uint[[3]] diagMatrixMultiplication (D uint[[3]] x, D uint[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D int8[[3]] diagMatrixMultiplication (D int8[[3]] x, D int8[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D int16[[3]] diagMatrixMultiplication (D int16[[3]] x, D int16[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D int32[[3]] diagMatrixMultiplication (D int32[[3]] x, D int32[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D int[[3]] diagMatrixMultiplication (D int[[3]] x, D int[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D float32[[3]] diagMatrixMultiplication (D float32[[3]] x, D float32[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

template <domain D>
D float64[[3]] diagMatrixMultiplication (D float64[[3]] x, D float64[[3]] y) {
    return _diagMatrixMultiplication (x, y);
}

/** @}*/
/** @}*/


/** \addtogroup determinant
 *  @{
 *  @brief Function for finding the determinant of a matrix
 *  @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 *  @param mat - a matrix of supported type
 *  @return returns the determinant of the input matrix
 */

/* Determinant using LUP-decomposition method. */
float32 determinant (float32[[2]] mat) {
    uint[[1]] s = shape(mat);
    assert(s[0] == s[1]);
    uint n = s[0];

    int exchanges = 0;

       for (uint k = 0; k < n; ++k) {
           float32 p = 0;
           uint kprim;
           for (uint i = k; i < n; ++i) {
               if (abs(mat[i,k]) > p) {
                   p = abs(mat[i,k]);
                   kprim = i;
               }
           }
           if (p == 0) {
               return 0;
           }

           if (k != kprim) {
               ++exchanges;

               float32[[1]] tmp1 = mat[k,:];
               mat[k,:] = mat[kprim,:];
               mat[kprim,:] = tmp1;
           }

           for (uint i = k+1; i < n; ++i) {
               mat[i,k] /= mat[k,k];
               for (uint j = k+1; j < n; ++j) {
                   mat[i,j] -= mat[i,k]*mat[k,j];
               }
           }

       }

       float32 det = 1;

       for (uint i = 0; i < n; ++i) {
           det *= mat[i,i];
       }

       if (exchanges % 2 == 1) {
           det = -det;
       }

       return det;
}

float64 determinant (float64[[2]] mat) {
    uint[[1]] s = shape(mat);
    assert(s[0] == s[1]);
    uint n = s[0];

    int exchanges = 0;

       for (uint k = 0; k < n; ++k) {
           float64 p = 0;
           uint kprim;
           for (uint i = k; i < n; ++i) {
               if (abs(mat[i,k]) > p) {
                   p = abs(mat[i,k]);
                   kprim = i;
               }
           }
           if (p == 0) {
               return 0;
           }

           if (k != kprim) {
               ++exchanges;

               float64[[1]] tmp1 = mat[k,:];
               mat[k,:] = mat[kprim,:];
               mat[kprim,:] = tmp1;
           }

           for (uint i = k+1; i < n; ++i) {
               mat[i,k] /= mat[k,k];
               for (uint j = k+1; j < n; ++j) {
                   mat[i,j] -= mat[i,k]*mat[k,j];
               }
           }

       }

       float64 det = 1;

       for (uint i = 0; i < n; ++i) {
           det *= mat[i,i];
       }

       if (exchanges % 2 == 1) {
           det = -det;
       }

       return det;
}


/**
* @note **D** - all protection domains
* @note naive determinant implementation
*/
template <domain D>
D float64 determinant(D float32[[2]] mat) {
    uint[[1]] s = shape(mat);
    assert(s[0] == s[1]);
    uint n = s[0];
    assert (n > 0);

    D float64 det;

    if (n == 1) {
          det = mat[0, 0];
    } else if (n == 2) {
          det = mat[0,0] * mat[1,1] - mat[1,0] * mat[0,1];
    } else {
        D float64[[2]] minor (n-1, n-1);
          for (uint j1 = 0; j1 < n; ++j1) {
             for (uint i = 1; i < n; ++i) {
                uint j2 = 0;
                for (uint j = 0; j < n; ++j) {
                       if (j == j1)
                          continue;
                       minor[i-1, j2] = mat[i, j];
                       ++j2;
                }
             }
             bool isEven = j1 % 2 == 0;
            det += isEven ? mat[0, j1] * determinant(minor) : -1 * mat[0, j1] * determinant(minor);
        }
    }
    return det;
}

/**
* @note **D** - all protection domains
* @note naive determinant implementation
*/
template <domain D>
D float64 determinant(D float64[[2]] mat) {
    uint[[1]] s = shape(mat);
    assert(s[0] == s[1]);
    uint n = s[0];
    assert (n > 0);

    D float64 det;

    if (n == 1) {
          det = mat[0, 0];
    } else if (n == 2) {
          det = mat[0,0] * mat[1,1] - mat[1,0] * mat[0,1];
    } else {
        D float64[[2]] minor (n-1, n-1);
          for (uint j1 = 0; j1 < n; ++j1) {
             for (uint i = 1; i < n; ++i) {
                uint j2 = 0;
                for (uint j = 0; j < n; ++j) {
                       if (j == j1)
                          continue;
                       minor[i-1, j2] = mat[i, j];
                       ++j2;
                }
             }
             bool isEven = j1 % 2 == 0;
            det += isEven ? mat[0, j1] * determinant(minor) : -1 * mat[0, j1] * determinant(minor);
        }
    }
    return det;
}


// for reference - creates P*mat = L*U in-place
// P - permutation matrix
// L - lower unit diagonal matrix
// U - upper diagonal matrix
// returns L and U in a single matrix, also calculates P, but doesn't return it

/**
* \cond
*/
float64[[2]] LupDecomposition (float64[[2]] mat) {
    uint[[1]] s = shape(mat);
    assert(s[0] == s[1]);
    uint n = s[0];

    uint[[1]] perm = (uint)mat[0,:];
       for (uint i = 0; i < n; ++i) {
           perm[i] = i;
       }

       for (uint k = 0; k < n; ++k) {
           float64 p = 0;
           uint kprim;
           for (uint i = k; i < n; ++i) {
               if (abs(mat[i,k]) > p) {
                   p = abs(mat[i,k]);
                   kprim = i;
               }
           }
           if (p == 0) {
               print("error singular mat");
               return mat;
           }

           if (k != kprim) {
               uint tmp = perm[k];
               perm[k] = perm[kprim];
               perm[kprim] = tmp;

               float64[[1]] tmp1 = mat[k,:];
               mat[k,:] = mat[kprim,:];
               mat[kprim,:] = tmp1;
           }

           for (uint i = k+1; i < n; ++i) {
               mat[i,k] /= mat[k,k];
               for (uint j = k+1; j < n; ++j) {
                   mat[i,j] -= mat[i,k]*mat[k,j];
               }
           }

       }

       return mat;
}

/**
* \endcond
*/
/** @}*/
/** @}*/

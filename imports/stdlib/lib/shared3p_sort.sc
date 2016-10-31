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
module shared3p_sort;

import stdlib;
import shared3p;
import shared3p_random;
import oblivious;
import shared3p_oblivious;
import shared3p;
/**
* \endcond
*/

/**
* @file
* \defgroup shared3p_sort shared3p_sort.sc
* \defgroup sort sort
* \defgroup sort_vec sort[[1]]
* \defgroup sort_mat sort[[2]]
* \defgroup sortingnetwork sortingNetworkSort
* \defgroup sortingnetwork_vec sortingNetworkSort[[1]]
* \defgroup sortingnetwork_mat sortingNetworkSort[[2]](1 column)
* \defgroup sortingnetwork_mat2 sortingNetworkSort[[2]](2 columns)
* \defgroup sortingnetwork_mat3 sortingNetworkSort[[2]](3 columns)
* \defgroup selectk selectK
* \defgroup selectk_vec selectK[[1]]
* \defgroup selectk_mat selectK[[2]]
*/

/** \addtogroup shared3p_sort
*@{
* @brief Module with functions for sorting values
*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  sort                                                                      **
**                                                                            **
********************************************************************************
*******************************************************************************/

/** \addtogroup sort
 *  @{
 *  @brief Functions for sorting values
 *  @note **D** - shared3p protection domain
 *  @note **T** - any \ref data_types "data" type
 *  @note boolean values are sorted after their numerical value. **false** first then **true**
 */

/** \addtogroup sort_vec
 *  @{
 *  @brief Function for sorting values in a vector
 *  @note **D** - shared3p protection domain
 *  @return returns a sorted vector from smaller to bigger values
 */


/**
* @note Supported types - \ref bool "bool"
*  @note boolean values are sorted after their numerical value. **false** first then **true**
* @param arr - a 1-dimensonal boolean vector
*/
template <domain D : shared3p>
D bool[[1]] sort(D bool[[1]] arr) {
    D uint [[1]] vec = (uint) arr;
    D uint [[1]] ivec = 1 - vec;

    uint n = size (arr);

    D uint [[1]] pTrue (n);
    D uint acc = 0;
    for (uint i = 0; i < n; ++ i) {
        pTrue[i] = acc;
        acc += ivec[i];
    }

    D uint [[1]] pFalse (n);
    acc = n - 1;
    for (uint i = 1; i <= n; ++ i) {
        pFalse[n-i] = acc;
        acc -= vec[n-i];
    }

    // vec*pFalse + ivec*pTrue
    // ivec = 1-vec
    D uint[[1]] indexes = vec * (pFalse - pTrue) + pTrue;
    uint[[1]] publishedIndexes = declassify(indexes);
    D bool[[1]] sortedArr (n);
    for (uint i = 0; i < n; ++i) {
        sortedArr[publishedIndexes[i]] = arr[i];
    }

    return sortedArr;
}

/**
* @note **T** - any \ref data_types "data" type
* @param vec - a 1-dimensonal supported type vector
*/
template <domain D : shared3p, type T>
D T[[1]] sort(D T[[1]] vec) {
    if (size(vec) <= 1)
        return vec;

    vec = shuffle(vec);

    uint n = size(vec);
    uint compSize = (n * (n - 1)) / 2;

    // Do the comparisons:
    /// \todo do check for matrix size so that comps etc can fit into memory
    D uint[[1]] comps;
    {
        // Generate the arrays to compare:
        D T[[1]] cArray1(compSize);
        D T[[1]] cArray2(compSize);
        uint i = 0;
        for (uint r = 0; r < n - 1; ++r) {
            for (uint c = r + 1; c < n; ++c) {
                cArray1[i] = vec[r];
                cArray2[i] = vec[c];
                ++i;
            }
        }

        // Do all the actual comparisons:
        comps = (uint) (cArray1 <= cArray2);
    }

    // Privately compute the new indexes:
    D uint[[1]] newIndexes(n);
    uint constOne = 1;
    {
        uint r = 0;
        uint c = 1;
        for (uint i = 0; i < compSize; ++i) {
            D uint v = comps[i];
            newIndexes[r] += constOne - v;
            newIndexes[c] += v;

            ++c;
            assert(c <= n);
            if (c >= n) {
                ++r;
                c = r + 1;
            }
        }
    }

    uint[[1]] publishedIndexes = declassify(newIndexes);

    D T[[1]] sorted(n);
    for (uint r = 0; r < n; ++r) {
        sorted[publishedIndexes[r]] = vec[r];
    }

    return sorted;
}
/** @}*/
/** \addtogroup sort_mat
 *  @{
 *  @brief Function for sorting rows of a matrix based on values of a column
 *  @note **D** - shared3p protection domain
 *  @return returns a matrix where the input matrix rows are sorted
 *  based on values of the specified column
 */

/**
 *  @note Supported types - \ref bool "bool"
 *  @note boolean values are sorted after their numerical value. **false** first then **true**
 *  @param column - index of the column used for ordering
 *  @param matrix - a matrix of supported type
*/
template <domain D : shared3p>
D bool[[2]] sort(D bool[[2]] matrix, uint column) {
    uint[[1]] matShape = shape(matrix);

    D uint[[1]] sortCol = (uint) matrix[:, column];
    D uint[[1]] isortCol = 1 - sortCol;

    uint n = matShape[0];
    {
        D uint[[1]] pTrue (n);
        D uint acc = 0;
        for (uint i = 0; i < n; ++i) {
            pTrue[i] = acc;
            acc += isortCol[i];
        }

        isortCol *= pTrue;
    }

    {
        D uint[[1]] pFalse (n);
        D uint acc = n - 1;
        for (uint i = 1; i <= n; ++i) {
            pFalse[n-i] = acc;
            acc -= sortCol[n-i];
        }

        sortCol *= pFalse;
    }

    uint[[1]] publishedIndexes = declassify(sortCol + isortCol);
    D bool[[2]] sortedMatrix (matShape[0], matShape[1]);
    for (uint i = 0; i < n; ++i) {
        sortedMatrix[publishedIndexes[i], :] = matrix[i, :];
    }

    return sortedMatrix;
}

/**
 *  @note **T** - any \ref data_types "data" type
 *  @param column - index of the column used for ordering
 *  @param matrix - a matrix of supported type
*/

template <domain D : shared3p, type T>
D T[[2]] sort(D T[[2]] matrix, uint column) {
    uint n = shape(matrix)[0];
    if (n <= 1)
        return matrix;

    uint columnCount = shape(matrix)[1];
    assert(column < columnCount);
    matrix = shuffleRows(matrix);

    uint64 compSize = (n * (n - 1)) / 2;

    // Do the comparisons:
    /// \todo do check for matrix size so that comps etc can fit into memory
    D uint[[1]] comps;
    {
        // Generate the arrays to compare:
        D T[[1]] cArray1(compSize);
        D T[[1]] cArray2(compSize);
        uint i = 0;
        for (uint r = 0; r < n - 1; ++r) {
            for (uint c = r + 1; c < n; ++c) {
                cArray1[i] = matrix[r, column];
                cArray2[i] = matrix[c, column];
                ++i;
            }
        }

        // Do all the actual comparisons:
        comps = (uint) (cArray1 <= cArray2);
    }

    // Privately compute the new indexes:
    D uint[[1]] newIndexes(n);
    uint constOne = 1;
    {
        uint r = 0;
        uint c = 1;
        for (uint i = 0; i < compSize; ++i) {
            D uint v = comps[i];
            newIndexes[r] += constOne - v;
            newIndexes[c] += v;

            ++c;
            assert(c <= n);
            if (c >= n) {
                ++r;
                c = r + 1;
            }
        }
    }

    uint[[1]] publishedIndexes = declassify(newIndexes);

    D T[[2]] sorted(n, columnCount);
    for (uint r = 0; r < n; ++r)
        sorted[publishedIndexes[r], :] = matrix[r, :];

    return sorted;
}
/** @}*/
/** @}*/

/*******************************************************************************
********************************************************************************
**                                                                            **
**  sortingNetworkSort                                                        **
**                                                                            **
********************************************************************************
*******************************************************************************/

/**
* \cond
*/
uint[[1]] generateSortingNetwork(uint arraysize) {
    uint snsize = 0;
    __syscall("SortingNetwork_serializedSize", arraysize, __return snsize);
    uint[[1]] sn (snsize);
    __syscall("SortingNetwork_serialize", arraysize, __ref sn);
    return sn;
}
/**
* \endcond
*/


/** \addtogroup sortingnetwork
 *  @{
 *  @brief Functions for sorting values with sorting networks
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 */

/** \addtogroup sortingnetwork_vec
 *  @{
 *  @brief Function for sorting values in a vector with sorting network
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param array - a vector of supported type
 *  @return returns a sorted vector from smaller to bigger values
 */


//is this only shared3p?
//doesn't work for bools
/**
* \cond
*/
template <domain D>
D uint8[[1]] sortingNetworkSort (D uint8[[1]] array) {
    D xor_uint8[[1]] sortIn = reshare (array);
    D xor_uint8[[1]] sortOut = sortingNetworkSort (sortIn);
    return reshare(sortOut);
}

template <domain D>
D uint16[[1]] sortingNetworkSort (D uint16[[1]] array) {
    D xor_uint16[[1]] sortIn = reshare (array);
    D xor_uint16[[1]] sortOut = sortingNetworkSort (sortIn);
    return reshare(sortOut);
}

template <domain D>
D uint32[[1]] sortingNetworkSort (D uint32[[1]] array) {
    D xor_uint32[[1]] sortIn = reshare (array);
    D xor_uint32[[1]] sortOut = sortingNetworkSort (sortIn);
    return reshare(sortOut);
}

template <domain D>
D uint64[[1]] sortingNetworkSort (D uint64[[1]] array) {
    D xor_uint64[[1]] sortIn = reshare (array);
    D xor_uint64[[1]] sortOut = sortingNetworkSort (sortIn);
    return reshare(sortOut);
}

template <domain D>
D int8[[1]] sortingNetworkSort (D int8[[1]] array) {
    D uint8[[1]] y = (uint8)array + 128;
    D xor_uint8[[1]] sortIn = reshare (y);
    D xor_uint8[[1]] sortOut = sortingNetworkSort (sortIn);
    y = reshare(sortOut) - 128;
    return (int8)y;
}

template <domain D>
D int16[[1]] sortingNetworkSort (D int16[[1]] array) {
    D uint16[[1]] y = (uint16)array + 32768;
    D xor_uint16[[1]] sortIn = reshare (y);
    D xor_uint16[[1]] sortOut = sortingNetworkSort (sortIn);
    y = reshare(sortOut) - 32768;
    return (int16)y;
}

template <domain D>
D int32[[1]] sortingNetworkSort (D int32[[1]] array) {
    D uint32[[1]] y = (uint32)array + 2147483648;
    D xor_uint32[[1]] sortIn = reshare (y);
    D xor_uint32[[1]] sortOut = sortingNetworkSort (sortIn);
    y = reshare(sortOut) - 2147483648;
    return (int32)y;
}

template <domain D>
D int64[[1]] sortingNetworkSort (D int64[[1]] array) {
    D uint64[[1]] y = (uint)array + 9223372036854775808;
    D xor_uint64[[1]] sortIn = reshare (y);
    D xor_uint64[[1]] sortOut = sortingNetworkSort (sortIn);
    y = reshare(sortOut) - 9223372036854775808;
    return (int64)y;
}
/**
* \endcond
*/
template <domain D, type T>
D T[[1]] sortingNetworkSort (D T[[1]] array) {

    if (size(array) <= 1)
        return array;

    // Generate sorting network
    uint[[1]] sortnet = generateSortingNetwork (size(array));

    // We will use this offset to decode the sorting network
    uint offset = 0;

    // Extract the number of stages
    uint numOfStages = sortnet[offset++];

    for (uint stage = 0; stage < numOfStages; stage++) {
        uint sizeOfStage = sortnet[offset++];

        D T[[1]] firstVector (sizeOfStage);
        D T[[1]] secondVector (sizeOfStage);
        D bool[[1]] exchangeFlagsVector (sizeOfStage);

        // Set up first comparison vector
        for (uint i = 0; i < sizeOfStage; ++i) {
            firstVector[i] = array[sortnet[offset]];
            offset++;
        }

        // Set up second comparison vector
        for (uint i = 0; i < sizeOfStage; ++i) {
            secondVector[i] = array[sortnet[offset]];
            offset++;
        }

        // Perform compares
        exchangeFlagsVector = firstVector <= secondVector;

        D bool[[1]] expandedExchangeFlagsVector (2 * sizeOfStage);

        uint counter = 0;
        for(uint i = 0; i < 2 * sizeOfStage; i = i + 2){
            expandedExchangeFlagsVector[i] =  exchangeFlagsVector[counter];
            expandedExchangeFlagsVector[i + 1] = exchangeFlagsVector[counter];
            counter++;
        }

        // Perform exchanges
        D T[[1]] firstFactor (2 * sizeOfStage);
        D T[[1]] secondFactor (2 * sizeOfStage);

        counter = 0;
        for (uint i = 0; i < 2 * sizeOfStage; i = i + 2) {

            firstFactor[i] = firstVector[counter];
            firstFactor[i + 1] = secondVector[counter];

            // Comparison bits

            secondFactor[i] = secondVector[counter];
            secondFactor[i + 1] = firstVector[counter];
            counter++;
        }

        D T[[1]] choiceResults (2 * sizeOfStage);

        choiceResults = choose(expandedExchangeFlagsVector,firstFactor,secondFactor);

        // Finalize oblivious choices
        for (uint i = 0; i < 2 * sizeOfStage; i = i + 2) {
            array[sortnet[offset++]] = choiceResults [i];
        }
        for (uint i = 1; i < (2 * sizeOfStage + 1); i = i + 2) {
            array[sortnet[offset++]] = choiceResults [i];
        }


    }
    return array;
}



/** @}*/
/** \addtogroup sortingnetwork_mat
 *  @{
 *  @brief Function for sorting rows of a matrix based on values of a column
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param column - index of the column used for ordering rows of the matrix
 *  @param matrix - a matrix of supported type
 *  @return returns a matrix with sorted rows
 */
template <domain D : shared3p>
D uint8[[2]] sortingNetworkSort (D uint8[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = reshare(shuffledMatrix[:,column]);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _sortingNetworkSort(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint8[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint16[[2]] sortingNetworkSort (D uint16[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = reshare(shuffledMatrix[:,column]);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _sortingNetworkSort(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint16[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint32[[2]] sortingNetworkSort (D uint32[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = reshare(shuffledMatrix[:,column]);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _sortingNetworkSort(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint32[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint64[[2]] sortingNetworkSort (D uint64[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = reshare(shuffledMatrix[:,column]);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint64[[1]] indexVector = publicIndices;
    indexVector = _sortingNetworkSort(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint64[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int8[[2]] sortingNetworkSort (D int8[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = reshare((uint8) shuffledMatrix[:,column] + 128);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _sortingNetworkSort(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int8[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int16[[2]] sortingNetworkSort (D int16[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = reshare((uint16) shuffledMatrix[:,column] + 32768);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _sortingNetworkSort(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int16[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int32[[2]] sortingNetworkSort (D int32[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = reshare((uint32) shuffledMatrix[:,column] + 2147483648);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _sortingNetworkSort(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int32[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int64[[2]] sortingNetworkSort (D int64[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = reshare((uint64) shuffledMatrix[:,column] + 9223372036854775808);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint64[[1]] indexVector = (uint64) publicIndices;
    indexVector = _sortingNetworkSort(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int64[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint8[[2]] sortingNetworkSort (D xor_uint8[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint8[[2]] shuffledMatrix = shuffleRows(matrix);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _sortingNetworkSort(shuffledMatrix[:,column], indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint8[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint16[[2]] sortingNetworkSort (D xor_uint16[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint16[[2]] shuffledMatrix = shuffleRows(matrix);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _sortingNetworkSort(shuffledMatrix[:,column], indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint16[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint32[[2]] sortingNetworkSort (D xor_uint32[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint32[[2]] shuffledMatrix = shuffleRows(matrix);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _sortingNetworkSort(shuffledMatrix[:,column], indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint32[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint64[[2]] sortingNetworkSort (D xor_uint64[[2]] matrix, uint column) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint64[[2]] shuffledMatrix = shuffleRows(matrix);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint64[[1]] indexVector = (uint64) publicIndices;
    indexVector = _sortingNetworkSort(shuffledMatrix[:,column], indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint64[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}
/**
 * \cond
 */
template <domain D>
D uint[[1]] iota (uint n) {
    uint [[1]] out (n);

    for (uint i = 0; i < n; ++ i)
        out[i] = i;

    return out;
}

template <domain D : shared3p, type T>
D T[[1]] _sortingNetworkSort (D T[[1]] vector, D T[[1]] indices) {
    uint[[1]] sortnet = generateSortingNetwork(size(vector));
    uint offset = 0;
    uint numOfStages = sortnet[offset++];

    for (uint stage = 0; stage < numOfStages; stage++) {
        uint sizeOfStage = sortnet[offset++];

        D T[[1]] first(2 * sizeOfStage), second(2 * sizeOfStage);

        for (uint i = 0; i < sizeOfStage; ++i) {
            first[i]                = vector[sortnet[offset]];
            first[i + sizeOfStage]  = indices[sortnet[offset]];
            offset++;
        }

        for (uint i = 0; i < sizeOfStage; ++i) {
            second[i]               = vector[sortnet[offset]];
            second[i + sizeOfStage] = indices[sortnet[offset]];
            offset++;
        }

        D bool[[1]] exchangeFlagsVector = first[:sizeOfStage] <= second[:sizeOfStage];
        exchangeFlagsVector = cat(exchangeFlagsVector, exchangeFlagsVector);

        D T[[1]] results  = choose(exchangeFlagsVector, first, second);

        second = results ^ first ^ second;
        first = results;

        for (uint i = 0; i < sizeOfStage; ++i) {
            vector[sortnet[offset]] = first[i];
            indices[sortnet[offset]] = first[i + sizeOfStage];
            offset++;
        }

        for (uint i = 0; i < sizeOfStage; ++i) {
            vector[sortnet[offset]] = second[i];
            indices[sortnet[offset]] = second[i + sizeOfStage];
            offset++;
        }
    }

    return indices;
}
/**
 * \endcond
 */

/** @}*/
/** \addtogroup sortingnetwork_mat2
 *  @{
 *  @brief Function for sorting rows of a matrix based on values of two columns
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param column1 - index of the first column used for ordering
 *  @param column2 - index of the second column used for ordering
 *  @param matrix - a matrix of supported type
 *  @return returns a matrix where the rows of the input matrix have
 *  been sorted. For ordering two rows, the values in column1 are
 *  compared first, if they are equal then the values in column2 are
 *  compared.
 */
template <domain D : shared3p>
D uint8[[2]] sortingNetworkSort (D uint8[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = reshare(cat(shuffledMatrix[:,column1],
                                                shuffledMatrix[:,column2]));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint8[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint16[[2]] sortingNetworkSort (D uint16[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = reshare(cat(shuffledMatrix[:,column1],
                                                 shuffledMatrix[:,column2]));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint16[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint32[[2]] sortingNetworkSort (D uint32[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = reshare(cat(shuffledMatrix[:,column1],
                                                 shuffledMatrix[:,column2]));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint32[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint64[[2]] sortingNetworkSort (D uint64[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = reshare(cat(shuffledMatrix[:,column1],
                                                 shuffledMatrix[:,column2]));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint64[[1]] indexVector = publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint64[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int8[[2]] sortingNetworkSort (D int8[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = reshare(cat((uint8) shuffledMatrix[:,column1] + 128,
                                                (uint8) shuffledMatrix[:,column2] + 128));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int8[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int16[[2]] sortingNetworkSort (D int16[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = reshare(cat((uint16) shuffledMatrix[:,column1] + 32768,
                                                 (uint16) shuffledMatrix[:,column2] + 32768));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int16[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int32[[2]] sortingNetworkSort (D int32[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = reshare(cat((uint32) shuffledMatrix[:,column1] + 2147483648,
                                                 (uint32) shuffledMatrix[:,column2] + 2147483648));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int32[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int64[[2]] sortingNetworkSort (D int64[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = reshare(cat((uint64) shuffledMatrix[:,column1] + 9223372036854775808,
                                                 (uint64) shuffledMatrix[:,column2] + 9223372036854775808));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint64[[1]] indexVector = (uint64) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int64[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint8[[2]] sortingNetworkSort (D xor_uint8[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = cat(shuffledMatrix[:,column1],
                                        shuffledMatrix[:,column2]);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint8[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint16[[2]] sortingNetworkSort (D xor_uint16[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = cat(shuffledMatrix[:,column1],
                                         shuffledMatrix[:,column2]);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint16[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint32[[2]] sortingNetworkSort (D xor_uint32[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = cat(shuffledMatrix[:,column1],
                                         shuffledMatrix[:,column2]);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint32[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint64[[2]] sortingNetworkSort (D xor_uint64[[2]] matrix, uint column1, uint column2) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = cat(shuffledMatrix[:,column1],
                                         shuffledMatrix[:,column2]);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint64[[1]] indexVector = (uint64) publicIndices;
    indexVector = _sortingNetworkSort2(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint64[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}
/**
 * \cond
 */
template <domain D : shared3p, type T>
D T[[1]] _sortingNetworkSort2 (D T[[1]] vector, D T[[1]] indices) {
    uint rows = size(vector) / 2;
    uint[[1]] sortnet = generateSortingNetwork(rows);
    uint offset = 0;
    uint numOfStages = sortnet[offset++];

    for (uint stage = 0; stage < numOfStages; stage++) {
        uint sizeOfStage = sortnet[offset++];

        D T[[1]] first(3 * sizeOfStage), second(3 * sizeOfStage);

        for (uint i = 0; i < sizeOfStage; ++i) {
            first[i]                   = vector[sortnet[offset]];
            first[i + sizeOfStage]     = vector[sortnet[offset] + rows];
            first[i + sizeOfStage * 2] = indices[sortnet[offset]];
            offset++;
        }

        for (uint i = 0; i < sizeOfStage; ++i) {
            second[i]                   = vector[sortnet[offset]];
            second[i + sizeOfStage]     = vector[sortnet[offset] + rows];
            second[i + sizeOfStage * 2] = indices[sortnet[offset]];
            offset++;
        }

        D T[[1]] compa = cat(first[:sizeOfStage], second[sizeOfStage:sizeOfStage*2]);
        D T[[1]] compb = cat(second[:sizeOfStage], first[sizeOfStage:sizeOfStage*2]);
        D bool[[1]] gte = compa >= compb;
        D bool[[1]] exchangeFlagsVector = !gte[:sizeOfStage] ||
            (first[:sizeOfStage] == second[:sizeOfStage] && gte[sizeOfStage:sizeOfStage*2]);
        exchangeFlagsVector = cat(cat(exchangeFlagsVector, exchangeFlagsVector), exchangeFlagsVector);

        D T[[1]] results  = choose(exchangeFlagsVector, first, second);

        second = results ^ first ^ second;
        first = results;

        for (uint i = 0; i < sizeOfStage; ++i) {
            vector[sortnet[offset]] = first[i];
            vector[sortnet[offset] + rows] = first[i + sizeOfStage];
            indices[sortnet[offset]] = first[i + sizeOfStage * 2];
            offset++;
        }

        for (uint i = 0; i < sizeOfStage; ++i) {
            vector[sortnet[offset]] = second[i];
            vector[sortnet[offset] + rows] = second[i + sizeOfStage];
            indices[sortnet[offset]] = second[i + sizeOfStage * 2];
            offset++;
        }
    }

    return indices;
}
/**
 * \endcond
 */
/** @}*/
/** \addtogroup sortingnetwork_mat3
 *  @{
 *  @brief Function for sorting rows of a matrix based on values of three columns
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @param column1 - index of the first column used for ordering
 *  @param column2 - index of the second column used for ordering
 *  @param column3 - index of the third column used for ordering
 *  @param matrix - a matrix of supported type
 *  @return returns a matrix where the rows of the input matrix have
 *  been sorted. For ordering two rows, the values in column1 are
 *  compared first, if they are equal then the values in column2 are
 *  compared, if they are equal then the values in column3 are
 *  compared.
 */
template <domain D : shared3p>
D uint8[[2]] sortingNetworkSort (D uint8[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = reshare(cat(cat(shuffledMatrix[:,column1],
                                                    shuffledMatrix[:,column2]),
                                                shuffledMatrix[:,column3]));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint8[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint16[[2]] sortingNetworkSort (D uint16[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = reshare(cat(cat(shuffledMatrix[:,column1],
                                                     shuffledMatrix[:,column2]),
                                                 shuffledMatrix[:,column3]));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint16[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint32[[2]] sortingNetworkSort (D uint32[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = reshare(cat(cat(shuffledMatrix[:,column1],
                                                     shuffledMatrix[:,column2]),
                                                 shuffledMatrix[:,column3]));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint32[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint64[[2]] sortingNetworkSort (D uint64[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D uint64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = reshare(cat(cat(shuffledMatrix[:,column1],
                                                     shuffledMatrix[:,column2]),
                                                 shuffledMatrix[:,column3]));

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint64[[1]] indexVector = publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D uint64[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int8[[2]] sortingNetworkSort (D int8[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = reshare(cat(cat((uint8) shuffledMatrix[:,column1] + 128,
                                                    (uint8) shuffledMatrix[:,column2] + 128),
                                                (uint8) shuffledMatrix[:,column3]) + 128);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int8[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int16[[2]] sortingNetworkSort (D int16[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = reshare(cat(cat((uint16) shuffledMatrix[:,column1] + 32768,
                                                     (uint16) shuffledMatrix[:,column2] + 32768),
                                                 (uint16) shuffledMatrix[:,column3]) + 32768);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int16[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int32[[2]] sortingNetworkSort (D int32[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = reshare(cat(cat((uint32) shuffledMatrix[:,column1] + 2147483648,
                                                     (uint32) shuffledMatrix[:,column2] + 2147483648),
                                                 (uint32) shuffledMatrix[:,column3]) + 2147483648);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int32[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int64[[2]] sortingNetworkSort (D int64[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D int64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = reshare(cat(cat((uint64) shuffledMatrix[:,column1] + 9223372036854775808,
                                                     (uint64) shuffledMatrix[:,column2] + 9223372036854775808),
                                                 (uint64) shuffledMatrix[:,column3]) + 9223372036854775808);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint64[[1]] indexVector = (uint64) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D int64[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint8[[2]] sortingNetworkSort (D xor_uint8[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = cat(cat(shuffledMatrix[:,column1],
                                            shuffledMatrix[:,column2]),
                                        shuffledMatrix[:,column3]);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint8[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint16[[2]] sortingNetworkSort (D xor_uint16[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = cat(cat(shuffledMatrix[:,column1],
                                             shuffledMatrix[:,column2]),
                                         shuffledMatrix[:,column3]);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint16[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint32[[2]] sortingNetworkSort (D xor_uint32[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = cat(cat(shuffledMatrix[:,column1],
                                             shuffledMatrix[:,column2]),
                                         shuffledMatrix[:,column3]);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint32[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint64[[2]] sortingNetworkSort (D xor_uint64[[2]] matrix, uint column1, uint column2, uint column3) {
    if (shape(matrix)[0] <= 1)
        return matrix;

    D xor_uint64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = cat(cat(shuffledMatrix[:,column1],
                                             shuffledMatrix[:,column2]),
                                         shuffledMatrix[:,column3]);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint64[[1]] indexVector = (uint64) publicIndices;
    indexVector = _sortingNetworkSort3(columnToSort, indexVector);
    publicIndices = (uint) declassify(indexVector);

    uint rows = shape(matrix)[0];
    D xor_uint64[[2]] out(rows, shape(matrix)[1]);
    for (uint i = 0; i < rows; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}
/**
 * \cond
 */
template <domain D : shared3p, type T>
D T[[1]] _sortingNetworkSort3 (D T[[1]] vector, D T[[1]] indices) {
    uint rows = size(vector) / 3;
    uint[[1]] sortnet = generateSortingNetwork(rows);
    uint offset = 0;
    uint numOfStages = sortnet[offset++];

    for (uint stage = 0; stage < numOfStages; stage++) {
        uint sizeOfStage = sortnet[offset++];

        D T[[1]] first(4 * sizeOfStage), second(4 * sizeOfStage);

        for (uint i = 0; i < sizeOfStage; ++i) {
            first[i]                   = vector[sortnet[offset]];
            first[i + sizeOfStage]     = vector[sortnet[offset] + rows];
            first[i + sizeOfStage * 2] = vector[sortnet[offset] + rows * 2];
            first[i + sizeOfStage * 3] = indices[sortnet[offset]];
            offset++;
        }

        for (uint i = 0; i < sizeOfStage; ++i) {
            second[i]                   = vector[sortnet[offset]];
            second[i + sizeOfStage]     = vector[sortnet[offset] + rows];
            second[i + sizeOfStage * 2] = vector[sortnet[offset] + rows * 2];
            second[i + sizeOfStage * 3] = indices[sortnet[offset]];
            offset++;
        }

        D T[[1]] compa = cat(cat(first[:sizeOfStage],
                                 first[sizeOfStage:sizeOfStage*2]),
                             second[sizeOfStage*2:sizeOfStage*3]);
        D T[[1]] compb = cat(cat(second[:sizeOfStage],
                                 second[sizeOfStage:sizeOfStage*2]),
                             first[sizeOfStage*2:sizeOfStage*3]);
        D bool[[1]] gte = compa >= compb;

        compa = cat(first[:sizeOfStage], first[sizeOfStage:sizeOfStage*2]);
        compb = cat(second[:sizeOfStage], second[sizeOfStage:sizeOfStage*2]);
        D bool[[1]] eq = compa == compb;

        D bool[[1]] exchangeFlagsVector = !(gte[:sizeOfStage]) ||
            (eq[:sizeOfStage] && (!(gte[sizeOfStage:sizeOfStage*2]) ||
                (eq[sizeOfStage:sizeOfStage*2] && gte[sizeOfStage*2:sizeOfStage*3])));
        exchangeFlagsVector = cat(cat(cat(exchangeFlagsVector, exchangeFlagsVector),
                                      exchangeFlagsVector),
                                  exchangeFlagsVector);

        D T[[1]] results  = choose(exchangeFlagsVector, first, second);

        second = results ^ first ^ second;
        first = results;

        for (uint i = 0; i < sizeOfStage; ++i) {
            vector[sortnet[offset]] = first[i];
            vector[sortnet[offset] + rows] = first[i + sizeOfStage];
            vector[sortnet[offset] + rows * 2] = first[i + sizeOfStage * 2];
            indices[sortnet[offset]] = first[i + sizeOfStage * 3];
            offset++;
        }

        for (uint i = 0; i < sizeOfStage; ++i) {
            vector[sortnet[offset]] = second[i];
            vector[sortnet[offset] + rows] = second[i + sizeOfStage];
            vector[sortnet[offset] + rows * 2] = second[i + sizeOfStage * 2];
            indices[sortnet[offset]] = second[i + sizeOfStage * 3];
            offset++;
        }
    }

    return indices;
}
/**
 * \endcond
 */
/** @}*/
/** @}*/

/**
 *\cond
 */
bool isPowerOfTwo (uint x) {
    return (x != 0 && (x & (x - 1)) == 0);
}

uint[[1]] generateTopKSortingNetwork (uint n, uint k) {
    assert(isPowerOfTwo (n));
    assert(k <= n);
    assert(n > 0);

    uint snsize = 0;
    __syscall ("TopKSortingNetwork_serializedSize", n, k, __return snsize);
    uint[[1]] sn(snsize);
    __syscall ("TopKSortingNetwork_serialize", n, k, __ref sn);
    return sn;
}
/**
 *\endcond
 */

/** \addtogroup selectk
 *  @{
 *  @brief Functions for selecting k values from a vector/matrix according to an ordering.
 *  @note **D** - all protection domains
 *  @note Supported types \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
*/

/** \addtogroup selectk_vec
 *  @{
 *  @brief Function for selecting the k smallest elements of a vector.
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @note Requires that the input array's length is a power of two.
 *  @note The algorithm behind this function is optimized for speed, accuracy is not guaranteed.
 *  @param vector - a vector of supported type
 *  @param k - the number of elements to be selected
 *  @return returns a vector of k elements selected from the input vector
 */

/**
 *\cond
 */
template <domain D : shared3p>
D uint8[[1]] selectK (D uint8[[1]] vector, uint k) {
    D xor_uint8[[1]] in = reshare (vector);
    D xor_uint8[[1]] out = selectK (in, k);
    return reshare(out);
}

template <domain D : shared3p>
D uint16[[1]] selectK (D uint16[[1]] vector, uint k) {
    D xor_uint16[[1]] in = reshare (vector);
    D xor_uint16[[1]] out = selectK (in, k);
    return reshare(out);
}

template <domain D : shared3p>
D uint32[[1]] selectK (D uint32[[1]] vector, uint k) {
    D xor_uint32[[1]] in = reshare (vector);
    D xor_uint32[[1]] out = selectK (in, k);
    return reshare(out);
}

template <domain D : shared3p>
D uint64[[1]] selectK (D uint64[[1]] vector, uint k) {
    D xor_uint64[[1]] in = reshare (vector);
    D xor_uint64[[1]] out = selectK (in, k);
    return reshare(out);
}

template <domain D : shared3p>
D int8[[1]] selectK (D int8[[1]] vector, uint k) {
    D uint8[[1]] y = (uint8)vector + 128;
    D xor_uint8[[1]] in = reshare (y);
    D xor_uint8[[1]] out = selectK (in, k);
    y = reshare (out) - 128;
    return (int8)y;
}

template <domain D : shared3p>
D int16[[1]] selectK (D int16[[1]] vector, uint k) {
    D uint16[[1]] y = (uint16)vector + 32768;
    D xor_uint16[[1]] in = reshare (y);
    D xor_uint16[[1]] out = selectK (in, k);
    y = reshare(out) - 32768;
    return (int16)y;
}

template <domain D : shared3p>
D int32[[1]] selectK (D int32[[1]] vector, uint k) {
    D uint32[[1]] y = (uint32)vector + 2147483648;
    D xor_uint32[[1]] in = reshare (y);
    D xor_uint32[[1]] out = selectK (in, k);
    y = reshare(out) - 2147483648;
    return (int32)y;
}

template <domain D : shared3p>
D int64[[1]] selectK (D int64[[1]] vector, uint k) {
    D uint64[[1]] y = (uint64)vector + 9223372036854775808;
    D xor_uint64[[1]] in = reshare (y);
    D xor_uint64[[1]] out = selectK (in, k);
    y = reshare(out) - 9223372036854775808;
    return (int64)y;
}
/**
 *\endcond
 */

template <domain D, type T>
D T[[1]] selectK (D T[[1]] vector, uint k) {
    uint[[1]] sortnet = generateTopKSortingNetwork (size(vector), k);
    uint offset = 0;
    uint numOfStages = sortnet[offset++];

    for (uint stage = 0; stage < numOfStages; stage++) {
        uint sizeOfStage = sortnet[offset++];

        D T[[1]] firstVector (sizeOfStage);
        D T[[1]] secondVector (sizeOfStage);
        D bool[[1]] exchangeFlagsVector (sizeOfStage);

        for (uint i = 0; i < sizeOfStage; i++) {
            firstVector[i] = vector[sortnet[offset]];
            secondVector[i] = vector[sortnet[offset+1]];
            offset += 2;
        }

        exchangeFlagsVector = firstVector <= secondVector;

        D bool[[2]] expandedExchangeFlagsVector (2, sizeOfStage);
        expandedExchangeFlagsVector[0,:] = exchangeFlagsVector;
        expandedExchangeFlagsVector[1,:] = exchangeFlagsVector;

        D T[[2]] firstFactor (2, sizeOfStage);
        D T[[2]] secondFactor (2, sizeOfStage);

        firstFactor[0, :] = firstVector;
        firstFactor[1, :] = secondVector;
        secondFactor[0, :] = secondVector;
        secondFactor[1, :] = firstVector;

        D T[[2]] choiceResults (2, sizeOfStage);

        choiceResults = choose(expandedExchangeFlagsVector,firstFactor,secondFactor);

        offset -= 2 * sizeOfStage;
        for (uint i = 0; i < sizeOfStage; i++) {
            vector[sortnet[offset++]] = choiceResults[0, i];
            vector[sortnet[offset++]] = choiceResults[1, i];
        }
    }

    return vector[:k];
}
/** @} */


/** \addtogroup selectk_mat
 *  @{
 *  @brief Function for selecting k rows from a matrix ordered by a column
 *  @note **D** - all protection domains
 *  @note Supported types - \ref uint8 "uint8" / \ref uint16 "uint16" / \ref uint32 "uint32" / \ref uint64 "uint" / \ref int8 "int8" / \ref int16 "int16" / \ref int32 "int32" / \ref int64 "int" / \ref xor_uint8 "xor_uint8" / \ref xor_uint16 "xor_uint16" / \ref xor_uint32 "xor_uint32" / \ref xor_uint64 "xor_uint64"
 *  @note The number of rows of the input matrix has to be a power of two.
 *  @note The algorithm behind this function is optimized for speed, accuracy is not guaranteed.
 *  @param matrix - a matrix of supported type
 *  @param k - number of elements to select
 *  @param column - column to select by
 *  @return returns a matrix with k rows selected from the input vector according to the input column index
 */
template <domain D : shared3p>
D uint8[[2]] selectK (D uint8[[2]] matrix, uint k, uint column) {
    D uint8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = reshare(shuffledMatrix[:,column]);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _selectK(columnToSort, indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D uint8[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint16[[2]] selectK (D uint16[[2]] matrix, uint k, uint column) {
    D uint16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = reshare(shuffledMatrix[:,column]);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _selectK(columnToSort, indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D uint16[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint32[[2]] selectK (D uint32[[2]] matrix, uint k, uint column) {
    D uint32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = reshare(shuffledMatrix[:,column]);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _selectK(columnToSort, indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D uint32[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D uint64[[2]] selectK (D uint64[[2]] matrix, uint k, uint column) {
    D uint64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = reshare(shuffledMatrix[:,column]);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint64[[1]] indexVector = publicIndices;
    indexVector = _selectK(columnToSort, indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D uint64[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int8[[2]] selectK (D int8[[2]] matrix, uint k, uint column) {
    D int8[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint8[[1]] columnToSort = reshare((uint8) shuffledMatrix[:,column] + 128);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _selectK(columnToSort, indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D int8[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int16[[2]] selectK (D int16[[2]] matrix, uint k, uint column) {
    D int16[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint16[[1]] columnToSort = reshare((uint16) shuffledMatrix[:,column] + 32768);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _selectK(columnToSort, indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D int16[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int32[[2]] selectK (D int32[[2]] matrix, uint k, uint column) {
    D int32[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint32[[1]] columnToSort = reshare((uint32) shuffledMatrix[:,column] + 2147483648);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _selectK(columnToSort, indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D int32[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D int64[[2]] selectK (D int64[[2]] matrix, uint k, uint column) {
    D int64[[2]] shuffledMatrix = shuffleRows(matrix);
    D xor_uint64[[1]] columnToSort = reshare((uint64) shuffledMatrix[:,column] + 9223372036854775808);

    uint[[1]] publicIndices = iota(size(columnToSort));
    D xor_uint64[[1]] indexVector = (uint64) publicIndices;
    indexVector = _selectK(columnToSort, indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D int64[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i], :];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint8[[2]] selectK (D xor_uint8[[2]] matrix, uint k, uint column) {
    D xor_uint8[[2]] shuffledMatrix = shuffleRows(matrix);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint8[[1]] indexVector = (uint8) publicIndices;
    indexVector = _selectK(shuffledMatrix[:,column], indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D xor_uint8[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i],:];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint16[[2]] selectK (D xor_uint16[[2]] matrix, uint k, uint column) {
    D xor_uint16[[2]] shuffledMatrix = shuffleRows(matrix);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint16[[1]] indexVector = (uint16) publicIndices;
    indexVector = _selectK(shuffledMatrix[:,column], indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D xor_uint16[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i],:];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint32[[2]] selectK (D xor_uint32[[2]] matrix, uint k, uint column) {
    D xor_uint32[[2]] shuffledMatrix = shuffleRows(matrix);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint32[[1]] indexVector = (uint32) publicIndices;
    indexVector = _selectK(shuffledMatrix[:,column], indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D xor_uint32[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i],:];
    }

    return out;
}

template <domain D : shared3p>
D xor_uint64[[2]] selectK (D xor_uint64[[2]] matrix, uint k, uint column) {
    D xor_uint64[[2]] shuffledMatrix = shuffleRows(matrix);

    uint[[1]] publicIndices = iota(shape(matrix)[0]);
    D xor_uint64[[1]] indexVector = (uint64) publicIndices;
    indexVector = _selectK(shuffledMatrix[:,column], indexVector, k);
    publicIndices = (uint) declassify(indexVector);

    D xor_uint64[[2]] out(k, shape(matrix)[1]);
    for (uint i = 0; i < k; i++) {
        out[i, :] = shuffledMatrix[publicIndices[i],:];
    }

    return out;
}

/**
 * \cond
 */
template <domain D : shared3p, type T>
D T[[1]] _selectK (D T[[1]] vector, D T[[1]] indices, uint k) {
    uint[[1]] sortnet = generateTopKSortingNetwork (size(vector), k);
    uint offset = 0;
    uint numOfStages = sortnet[offset++];

    for (uint stage = 0; stage < numOfStages; stage++) {
        uint sizeOfStage = sortnet[offset++];

        D T[[1]] first (2 * sizeOfStage), second (2 * sizeOfStage);

        for (uint i = 0; i < sizeOfStage; ++i) {
            first[i]                = vector[sortnet[offset+0]];
            first[i + sizeOfStage]  = indices[sortnet[offset+0]];
            second[i]               = vector[sortnet[offset+1]];
            second[i + sizeOfStage] = indices[sortnet[offset+1]];
            offset += 2;
        }

        D bool[[1]] exchangeFlagsVector = first[:sizeOfStage] <= second[:sizeOfStage];
        exchangeFlagsVector = cat (exchangeFlagsVector, exchangeFlagsVector);

        D T[[1]] results = choose(exchangeFlagsVector, first, second);

        second = results ^ first ^ second;
        first = results;

        offset -= 2 * sizeOfStage;
        for (uint i = 0; i < sizeOfStage; ++ i) {
            vector[sortnet[offset+0]]  = first[i];
            indices[sortnet[offset+0]] = first[i + sizeOfStage];
            vector[sortnet[offset+1]]  = second[i];
            indices[sortnet[offset+1]] = second[i + sizeOfStage];
            offset += 2;
        }
    }

    return indices;
}
/**
 * \endcond
 */
/** @} */
/** @} */
/** @}*/


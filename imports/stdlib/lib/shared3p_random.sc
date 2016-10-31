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
module shared3p_random;

import shared3p;
import matrix;
/**
* \endcond
*/

/**
* @file
* \defgroup shared3p_random shared3p_random.sc
* \defgroup shuffle shuffle
* \defgroup shuffle1 shuffle
* \defgroup shuffle2 shuffle(key)
* \defgroup shuffle3 inverseShuffle(key)
* \defgroup shufflerows1 shuffleRows
* \defgroup shufflerows2 shuffleRows(key)
* \defgroup shufflerows3 inverseShuffleRows(key)
* \defgroup shufflecols1 shuffleColumns
* \defgroup shufflecols2 shuffleColumns(key)
* \defgroup shufflecols3 inverseShuffleColumns(key)
* \defgroup randomize randomize
*/

/** \addtogroup shared3p_random
*@{
* @brief Module with functions for randomizing values
*/

/** \addtogroup shuffle
 *  @{
 *  @brief Functions for shuffling values
 *  @note **D** - shared3p protection domain
 *  @note **T** - any \ref data_types "data" type
 */

/** \addtogroup shuffle1
 *  @{
 *  @brief Function for shuffling values
 *  @note **D** - shared3p protection domain
 *  @return returns a shuffled vector
 */

/**
*  @note **T** - any \ref data_types "data" type
*  @param vec - a vector of supported type
*/
template <domain D : shared3p, type T>
D T[[1]] shuffle (D T[[1]] vec) {
    __syscall ("shared3p::vecshuf_$T\_vec", __domainid (D), vec);
    return vec;
}

/** @}*/
/** \addtogroup shuffle2
 *  @{
 *  @brief Protocols to shuffle an array with given key.
 *  @note **D** - shared3p protection domain
 *  @pre the key is exactly 32 bytes long
 *  @returns a random permutation of the input array
 *  @post the output is a permutation of the input
 *  @note the declassified value of the key does not matter, internally only the shares are used.
 *   If two vectors are shuffled using the same key the permutation applied is the same as long
 *   as the vectors are of the same length, and the key does not get reshared.
 */

/**
*  @note **T** - any \ref data_types "data" type
*  @param vec - input array to shuffle
*  @param key - an \ref uint8 "uint8" type key that specifies the permutation
*/
template <domain D : shared3p, type T>
D T[[1]] shuffle (D T[[1]] vec, D uint8[[1]] key) {
    assert (size (key) == 32);
    __syscall ("shared3p::vecshufkey_$T\_vec", __domainid (D), vec, key);
    return vec;
}

/** @}*/
/** \addtogroup shuffle3
 *  @{
 *  @brief Protocols to undo the shuffle of an array with given key.
 *  @note **D** - shared3p protection domain
 *  @pre the key is exactly 32 bytes long
 *  @returns the inverse of the permutation of the input array, defined by the key
 *  @post the output is a permutation of the input
 *  @note the declassified value of the key does not matter, internally only the shares are used.
 *   If two vectors are shuffled using the same key the permutation applied is the same as long
 *   as the vectors are of the same length, and the key does not get reshared.
 */

/**
*  @note **T** - any \ref data_types "data" type
*  @param vec - input array to shuffle
*  @param key - an \ref uint8 "uint8" type key that specifies the permutation
*/
template <domain D : shared3p, type T>
D T[[1]] inverseShuffle (D T[[1]] vec, D uint8[[1]] key) {
    assert (size (key) == 32);
    __syscall ("shared3p::vecshufinv_$T\_vec", __domainid (D), vec, key);
    return vec;
}

/** @}*/
/** \addtogroup shufflerows1
*  @{
*  @brief Function for shuffling rows in a matrix
*  @note **D** - shared3p protection domain
*  @return returns a matrix with shuffled rows
*/

/**
*  @note **T** - any \ref data_types "data" type
*  @param mat - a matrix of any type
*/
template <domain D : shared3p, type T>
D T[[2]] shuffleRows (D T[[2]] mat) {
    __syscall ("shared3p::matshuf_$T\_vec", __domainid (D), mat, shape (mat)[1]);
    return mat;
}

/** @}*/
/** \addtogroup shufflerows2
 *  @{
 *  @brief Protocols to shuffle rows in a matrix with given key.
 *  @note **D** - shared3p protection domain
 *  @pre the key is exactly 32 bytes long
 *  @returns a random permutation of the input matrix
 *  @post the output matrices rows are a permutation of the input
 *  @note the declassified value of the key does not matter, internally only the shares are used.
 *   If two vectors are shuffled using the same key the permutation applied is the same as long
 *   as the vectors are of the same length, and the key does not get reshared.
 */

/**
*  @note **T** - any \ref data_types "data" type
*  @param mat - input matrix to shuffle
*  @param key - an \ref uint8 "uint8" type key that specifies the permutation
*/
template <domain D : shared3p, type T>
D T[[2]] shuffleRows (D T[[2]] mat, D uint8[[1]] key) {
    assert (size (key) == 32);
    __syscall ("shared3p::matshufkey_$T\_vec", __domainid (D), mat, shape (mat)[1], key);
    return mat;
}

/** @}*/
/** \addtogroup shufflerows3
 *  @{
 *  @brief Protocols to undo the shuffling of rows in a matrix with given key.
 *  @note **D** - shared3p protection domain
 *  @pre the key is exactly 32 bytes long
 *  @returns the inverse of the permutation of the input matrix, defined by the key
 *  @post the output matrices rows are a permutation of the input
 *  @note the declassified value of the key does not matter, internally only the shares are used.
 *   If two vectors are shuffled using the same key the permutation applied is the same as long
 *   as the vectors are of the same length, and the key does not get reshared.
 */

/**
*  @note **T** - any \ref data_types "data" type
*  @param mat - input matrix to shuffle
*  @param key - an \ref uint8 "uint8" type key that specifies the permutation
*/
template <domain D : shared3p, type T>
D T[[2]] inverseShuffleRows (D T[[2]] mat, D uint8[[1]] key) {
    assert (size (key) == 32);
    __syscall ("shared3p::matshufinv_$T\_vec", __domainid (D), mat, shape (mat)[1], key);
    return mat;
}

/** @}*/
/** \addtogroup shufflecols1
*  @{
*  @brief Function for shuffling columns in a matrix
*  @note **D** - shared3p protection domain
*  @return returns a matrix with shuffled columns
*/

/**
*  @note **T** - any \ref data_types "data" type
*  @param mat - a matrix of any type
*/
template <domain D : shared3p, type T>
D T[[2]] shuffleColumns (D T[[2]] mat) {
    return transpose(shuffleRows(transpose(mat)));
}


/** @}*/
/** \addtogroup shufflecols2
 *  @{
 *  @brief Protocols to shuffle columns in a matrix with given key.
 *  @note **D** - shared3p protection domain
 *  @pre the key is exactly 32 bytes long
 *  @returns a random permutation of the input matrix
 *  @post the output matrixes columns are a permutation of the input
 *  @note the declassified value of the key does not matter, internally only the shares are used.
 *   If two vectors are shuffled using the same key the permutation applied is the same as long
 *   as the vectors are of the same length, and the key does not get reshared.
 */

/**
*  @note **T** - any \ref data_types "data" type
*  @param mat - input matrix to shuffle
*  @param key - an \ref uint8 "uint8" type key that specifies the permutation
*/
template <domain D : shared3p, type T>
D T[[2]] shuffleColumns (D T[[2]] mat, D uint8[[1]] key) {
    assert (size (key) == 32);
    return transpose(shuffleRows(transpose(mat), key));
}

/** @}*/
/** \addtogroup shufflecols3
 *  @{
 *  @brief Protocols to undo the shuffle of columns in a matrix with given key.
 *  @note **D** - shared3p protection domain
 *  @pre the key is exactly 32 bytes long
 *  @returns the inverse of the permutation of the input matrix, defined by the key
 *  @post the output matrixes columns are a permutation of the input
 *  @note the declassified value of the key does not matter, internally only the shares are used.
 *   If two vectors are shuffled using the same key the permutation applied is the same as long
 *   as the vectors are of the same length, and the key does not get reshared.
 */

/**
*  @note **T** - any \ref data_types "data" type
*  @param mat - input matrix to shuffle
*  @param key - an \ref uint8 "uint8" type key that specifies the permutation
*/
template <domain D : shared3p, type T>
D T[[2]] inverseShuffleColumns (D T[[2]] mat, D uint8[[1]] key) {
    assert (size (key) == 32);
    return transpose(inverseShuffleRows(transpose(mat), key));
}

/** @}*/
/** @}*/

/*******************************
    randomize
********************************/


/** \addtogroup randomize
 *  @{
 *  @brief Function for randomizing values
 *  @note **D** - shared3p protection domain
 *  @note **T** - any \ref data_types "data" type
 *  @param arr - an array of any dimension
 *  @return returns an array with randomized values
 */

template <domain D : shared3p, dim N>
D bool[[N]] randomize(D bool[[N]] arr) {
    __syscall("shared3p::randomize_bool_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D uint8[[N]] randomize(D uint8[[N]] arr) {
    __syscall("shared3p::randomize_uint8_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D uint16[[N]] randomize(D uint16[[N]] arr) {
    __syscall("shared3p::randomize_uint16_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D uint32[[N]] randomize(D uint32[[N]] arr) {
    __syscall("shared3p::randomize_uint32_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D uint[[N]] randomize(D uint[[N]] arr) {
    __syscall("shared3p::randomize_uint64_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D int8[[N]] randomize(D int8[[N]] arr) {
    __syscall("shared3p::randomize_int8_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D int16[[N]] randomize(D int16[[N]] arr) {
    __syscall("shared3p::randomize_int16_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D int32[[N]] randomize(D int32[[N]] arr) {
    __syscall("shared3p::randomize_int32_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D int[[N]] randomize(D int[[N]] arr) {
    __syscall("shared3p::randomize_int64_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D xor_uint8[[N]] randomize(D xor_uint8[[N]] arr) {
    __syscall("shared3p::randomize_xor_uint8_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D xor_uint16[[N]] randomize(D xor_uint16[[N]] arr) {
    __syscall("shared3p::randomize_xor_uint16_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D xor_uint32[[N]] randomize(D xor_uint32[[N]] arr) {
    __syscall("shared3p::randomize_xor_uint32_vec", __domainid(D), arr);
    return arr;
}

template <domain D : shared3p, dim N>
D xor_uint64[[N]] randomize(D xor_uint64[[N]] arr) {
    __syscall("shared3p::randomize_xor_uint64_vec", __domainid(D), arr);
    return arr;
}

/** @}*/
/** @}*/

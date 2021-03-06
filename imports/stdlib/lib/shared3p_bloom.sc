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
module shared3p_bloom;

import shared3p;
import profiling;
import shared3p_string;
/**
* \endcond
*/

/**
* @file
* \defgroup shared3p_bloom shared3p_bloom.sc
* \defgroup bloominsertmany bloomInsertMany
* \defgroup bloomquerymany bloomQueryMany
*/

/** \addtogroup shared3p_bloom
*@{
* @brief Module with bloom filter functions
*/

/**
 * \cond
*/

// TODO: workaround for a compiler bug
template <domain D : shared3p, dim N>
D xor_uint32 [[N]] classify_xor (uint32 [[N]] input) { return input; }

uint log2 (uint k) {
  uint l = 0;
  for (uint pow = 1; pow < k; ++ l) {
    pow = pow * 2;
  }

  return l;
}

template <type T, domain D>
D T[[1]] repeat (D T[[1]] arr, uint n) {
  uint m = size (arr), s = n*m;
  D T[[1]] out (s);
  for (uint i = 0; i < s; i += m) {
    out[i : i + m] = arr;
  }

  return out;
}

/**
 * Performs single equality. Can XOR comparison against public value be optimized?
 */
template <domain D : shared3p>
D bool[[1]] fromI2E (D xor_uint32[[1]] num, uint k){
  uint n = size (num);
  uint s = k * n;

  { // Mask the highest bits of num:
    int l = (int) (32 - log2 (k));
    num = shiftBitsLeftVec (num, l);
    num = shiftBitsRightVec (num, l);
  }

  uint32[[1]] idx (k);
  for (uint i = 0; i < k; ++ i) {
    idx[i] = (uint32) i;
  }

  uint32[[1]] idxs (s);
  D xor_uint32 [[1]] nums (s);
  for (uint i = 0, j = 0; i < s; i += n) {
    nums[i : i + n] = num;
    idxs[i : i + n] = idx[j ++];
  }

  D bool [[1]] eqs = nums == classify_xor (idxs);
  D bool [[1]] result = any (eqs, k);
  return result;
}

template <domain D : shared3p>
D bool[[2]] fromI2EVec (D xor_uint32[[2]] nums, uint k){
  uint m = shape (nums)[0], n = shape (nums)[1];
  uint s = k * n;

  { // Mask the highest bits of num:
    int l = (int) (32 - log2 (k));
    nums = shiftBitsLeftVec (nums, l);
    nums = shiftBitsRightVec (nums, l);
  }

  uint32[[1]] idxs (s);
  for (uint i = 0, j = 0; i < s; i += n) {
    idxs[i : i + n] = (uint32)(j ++);
  }

  idxs = repeat (idxs, m);

  D xor_uint32 [[2]] numss (m, s);
  for (uint i = 0; i < m; ++ i) {
    numss[i, :] = repeat (nums[i, :], k);
  }

  D bool[[1]] eqs = reshape (numss, m*s) == classify_xor (idxs);
  return reshape (any (eqs, m*k), m, k);
}



template <domain D, type T>
D T[[2]] dupRows (uint m, D T[[1]] row) {
    D T[[2]] out (m, size (row));
    for (uint i = 0; i < m; ++ i) {
        out[i, :] = row;
    }
    return out;
}

template <domain D : shared3p>
D xor_uint32 [[2]] dupCols (D xor_uint32[[1]] col, uint n) {
    D xor_uint32 [[2]] out (size (col), n);
    for (uint i = 0; i < n; ++ i) {
        out[:, i] = col;
    }

    return out;
}

/**
* \endcond
*/
/** \addtogroup bloominsertmany
*@{
* @brief function for inserting into the bloom filter
* @note **D** - shared3p protection domain
* @note Supported types - \ref xor_uint32 "xor_uint32"
*/

/**
* @param elem - the elements to add
* @param filter - filter data structure
* @param seed - seed
* @return returns the filter data structure
*/
template <domain D : shared3p>
D bool[[1]] bloomInsertMany (D xor_uint32[[1]] elem, D bool[[1]] filter, uint32[[1]] seed) {
    uint m = size (elem), n = size (seed);
    D xor_uint32[[1]] elems = reshape (dupCols (elem, n), m * n);
    uint32[[1]] seeds = reshape (dupRows (m, seed), m * n);
    D xor_uint32 [[1]] hashed = murmurHasherVec (elems, seeds);
    filter |= fromI2E (hashed, size (filter));
    return filter;
}

/** @}*/
/** \addtogroup bloomquerymany
*@{
* @brief function for querying from the bloom filter
* @note **D** - shared3p protection domain
* @note Supported types - \ref xor_uint32 "xor_uint32"
*/

/**
* @param elem - the elements to look for
* @param filter - filter data structure
* @param seed - seed
* @return returns a pointwise boolean vector whether the element is in the filter (may give false positive) or not (never gives false negative)
*/
template <domain D : shared3p>
D bool[[1]] bloomQueryMany (D  xor_uint32[[1]] elem,  D bool[[1]] filter, uint32[[1]] seed){
  uint m = size (elem), n = size (seed);

  D xor_uint32[[1]] elems = reshape (dupCols (elem, n), m * n);
  uint32[[1]] seeds = repeat (seed, m); // reshape (dupRows (m, seed), m * n);
  D xor_uint32 [[2]] hashed = reshape (murmurHasherVec (elems, seeds), m, n);

  uint filterSize = size (filter);
  D bool[[2]] filters = dupRows (m, filter);
  D bool[[2]] newElems = fromI2EVec (hashed, filterSize);
  D bool[[1]] result = all (reshape (filters | (! newElems), filterSize * m), m);
  return result;
}

/** @}*/
/** @}*/

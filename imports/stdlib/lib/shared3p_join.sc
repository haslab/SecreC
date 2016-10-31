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
module shared3p_join;

import stdlib;
import shared3p;
import shared3p_random;
import shared3p_aes;
/**
* \endcond
*/
/**
* @file
* \defgroup shared3p_join shared3p_join.sc
* \defgroup tablejoinaes128 tableJoinAes128
*/

/** \addtogroup shared3p_join
*@{
* @brief Module with tableJoinAes128
*/

/** \addtogroup tablejoinaes128
 *  @{
 *  @brief Function for joining two Aes128 matrices
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref xor_uint32 "xor_uint32"
 */


/**
 *  @param left - a matrix of supported type
 *  @param right - a matrix of supported type
 *  @param leftKeyCol - the key column to be joined after in the matrix **left**
 *  @param rightKeyCol - the key column to be joined after in the matrix **right**
 *  @pre the pointwise values of the columns specified by **leftKeyCol** and **rightKeyCol** are the same
 *  @return returns a joined matrix joined at **leftKeyCol** and **rightKeyCol**
 */
template <domain D : shared3p>
D xor_uint32[[2]] tableJoinAes128(D xor_uint32[[2]] left, uint leftKeyCol,
                                      D xor_uint32[[2]] right, uint rightKeyCol)
{
    uint[[1]] lShape = shape(left);
    uint[[1]] rShape = shape(right);
    uint leftCols = lShape[1];
    uint rightCols = rShape[1];

    left = shuffleRows(left);
    right = shuffleRows(right);
    //__syscall("shared3p::matshuf_xor_uint32_vec", __domainid(D), left, leftCols);
    //__syscall("shared3p::matshuf_xor_uint32_vec", __domainid(D), right, rightCols);
    uint leftRows = lShape[0];
    uint rightRows = rShape[0];

    assert(UINT64_MAX - leftRows >= rightRows); // Check for overflows
    assert(leftRows + rightRows <= UINT64_MAX / 4); // Check for overflows
    uint blocks = leftRows + rightRows;
    uint blocksTimesFour = blocks * 4;

    D xor_uint32[[1]] keyColumnData (blocksTimesFour);
    uint kIndex = 0;
    for (uint i = 0; i < leftRows; ++i) {
        keyColumnData[kIndex] = left[i, leftKeyCol];
        kIndex += 4;
    }
    uint rightStart = kIndex;
    for (uint i = 0; i < rightRows; ++i) {
        keyColumnData[kIndex] = right[i, rightKeyCol];
        kIndex += 4;
    }

    D xor_uint32[[1]] realKey (44 * blocks);
    {
        D xor_uint32[[1]] aesKey = aes128Genkey(1::uint);
        //__syscall("shared3p::randomize_xor_uint32_vec", __domainid(D), aesKey); // Generate random AES key
        D xor_uint32[[1]] expandedKey = aes128ExpandKey(aesKey);
        //__syscall("shared3p::aes128_xor_uint32_vec_expand_key", __domainid(D), aesKey, expandedKey); // expand key
        for (uint round = 0; round < 11; round++) {
            D xor_uint32[[1]] temp = expandedKey[round*4:round*4 + 4];
            for (uint j = 0; j < blocks; ++j) {
                realKey[4 * (round * blocks + j):4 * (round * blocks + j) + 4] = temp;
            }
        }
    }

    keyColumnData = aes128EncryptEcb(realKey, keyColumnData);
    //__syscall("shared3p::aes128_xor_uint32_vec", __domainid(D), keyColumnData, realKey, keyColumnData);
    uint32[[1]] publicKeyColumns = declassify(keyColumnData);

    uint allCols = leftCols + rightCols;
    D xor_uint32[[2]] joinedTable(leftRows * rightRows, allCols);

    uint resultRows = 0;
    uint tmp = 0;
    uint ri = 0;
    bool[[1]] comp;
    for (uint i = 0; i < leftRows; ++i) {
        uint rj = rightStart;
        for (uint j = 0; j < rightRows; ++j) {
            comp = publicKeyColumns[ri:ri + 4] == publicKeyColumns[rj:rj + 4];
            if (comp[0] && comp[1] && comp[2] && comp[3]) {
                joinedTable[resultRows, :leftCols] = left[i, :];
                joinedTable[resultRows, leftCols:] = right[j, :];
                ++resultRows;
            }
            rj += 4;
        }
        ri += 4;
    }
    joinedTable = joinedTable[:resultRows, :];
    joinedTable = shuffleRows(joinedTable);
    //__syscall("shared3p::matshuf_xor_uint32_vec", __domainid(D), joinedTable, allCols);
    return joinedTable;
}

/** @}*/
/** @}*/

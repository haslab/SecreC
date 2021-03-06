/*
 * This file is a part of the Sharemind framework.
 * Copyright (C) Cybernetica AS
 *
 * All rights are reserved. Reproduction in whole or part is prohibited
 * without the written consent of the copyright owner. The usage of this
 * code is subject to the appropriate license agreement.
 */

module x3p_join;

import stdlib;
import additive3pp;
import a3p_random;
import x3p_aes;

/**
 *  @param left - a matrix of supported type
 *  @param right - a matrix of supported type
 *  @param leftKeyCol - the key column to be joined after in the matrix **left**
 *  @param rightKeyCol - the key column to be joined after in the matrix **right**
 *  @pre the pointwise values of the columns specified by **leftKeyCol** and **rightKeyCol** are the same
 *  @return returns a joined matrix joined at **leftKeyCol** and **rightKeyCol**
 */
template <domain D : additive3pp>
D xor_uint32[[2]] tableJoinAes128(D xor_uint32[[2]] left, uint leftKeyCol,
                                  D xor_uint32[[2]] right, uint rightKeyCol)
{
    uint[[1]] lShape = shape(left);
    uint[[1]] rShape = shape(right);
    uint leftCols = lShape[1];
    uint rightCols = rShape[1];

    left = shuffleRows(left);
    right = shuffleRows(right);

    uint leftRows = lShape[0];
    uint rightRows = rShape[0];

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
        D xor_uint32[[1]] expandedKey = aes128ExpandKey(aesKey);
        for (uint round = 0; round < 11; round++) {
            D xor_uint32[[1]] temp = expandedKey[round*4:round*4 + 4];
            for (uint j = 0; j < blocks; ++j) {
                realKey[4 * (round * blocks + j):4 * (round * blocks + j) + 4] = temp;
            }
        }
    }

    keyColumnData = aes128EncryptEcb(realKey, keyColumnData);
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
    return joinedTable;
}

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

import stdlib;
import shared3p;
import shared3p_bloom;
import shared3p_random;
import shared3p_string;
import test_utility;

domain pd_shared3p shared3p;

void main(){
    string test_prefix = "Murmur";
    {
        bool [[1]] result(6);
        pd_shared3p xor_uint32[[1]] hashee (16);
        hashee = randomize(hashee);
        pd_shared3p uint32[[1]] temp (16);
        temp = randomize(temp);
        uint32[[1]] seed  = declassify(temp);
        pd_shared3p xor_uint32[[1]] cipherText (16);
        pd_shared3p xor_uint32[[1]] cipherText2 (16);
        for(uint i = 0; i < 6;++i){
            hashee = randomize(hashee);
            cipherText = murmurHasherVec(hashee,seed);
            cipherText2 = murmurHasherVec(hashee,seed);
            result[i] = all(declassify(cipherText == cipherText2));
        }

        test(test_prefix, result);
    }
    test_prefix = "Murmur vs harcoded answers";
    {
        pd_shared3p xor_uint32[[1]] hashee (16) = {0,43,2362,4,136,1,99,1058,435,128,100,489,1258639431,1582359,2059385813,1293547};
        uint32[[1]] seed (16) = {0,1,2,3,4,5,6,7,8,9,10,11,582602304,4985394,12980632,1284995};
        pd_shared3p xor_uint32[[1]] hash = murmurHasherVec(hashee, seed);
        uint32[[1]] control = {593689054, 2789264644, 2469316918, 1133932253, 3068893367, 51827383, 4015447857, 1446380866, 1197408155, 986356786, 2615377328, 3527425443, 3905575862, 3813275874, 1508441620, 3116924275};
        uint32[[1]] hash2 = declassify(hash);

        test(test_prefix, all(hash2 == control));
    }
    test_prefix = "Bloom filter";
    {
        bool [[1]] result(10);
        pd_shared3p xor_uint32[[1]] elem (1);
        elem = randomize(elem);
        pd_shared3p bool[[1]] filter (10) = false;
        bool[[1]] filter_orig (10) = declassify(filter);
        pd_shared3p bool[[1]] answer (1);
        pd_shared3p uint32[[1]] temp (5);
        uint32[[1]] seed (5);
        for(uint i = 0; i < 10; ++i){
            temp = randomize(temp);
            seed = declassify(temp);
            filter = bloomInsertMany(elem,filter,seed);

            answer = bloomQueryMany(elem,filter,seed);
            result[i] = !any(declassify(answer) == false);
            filter = false;
        }

        test(test_prefix, result);
    }
    test_prefix = "Bloom filter (2)";
    {
        bool [[1]] result(10);
        pd_shared3p xor_uint32[[1]] elem (5);
        pd_shared3p bool[[1]] filter (20) = false;
        bool[[1]] filter_orig (20) = declassify(filter);
        pd_shared3p bool[[1]] answer (5);
        pd_shared3p uint32[[1]] temp (10);
        uint32[[1]] seed (10);
        for(uint i = 0; i < 10; ++i){
            temp = randomize(temp);
            seed = declassify(temp);
            elem = randomize(elem);
            filter = bloomInsertMany(elem,filter,seed);

            answer = bloomQueryMany(elem,filter,seed);
            result[i] = !any(declassify(answer) == false);
            filter = false;
            filter_orig = declassify(filter);
        }

        test(test_prefix, result);
    }

    test_report();
}

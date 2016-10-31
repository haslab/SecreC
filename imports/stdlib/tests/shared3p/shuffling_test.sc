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
import shared3p_random;
import test_utility;

domain pd_shared3p shared3p;

template<domain D, type T>
bool vector_shuffle_test(D T t){
    D T[[1]] vec (50);
    vec = randomize(vec);
    D T[[1]] vec2 = shuffle(vec);
    bool[[1]] result = (declassify(vec) == declassify(vec2));

    return !all(result);
}

template<domain D, type T>
bool vector_shuffle_test_key(D T t){
    D uint8[[1]] key (32);
    D T[[1]] vec (50);
    D T[[1]] vec2 (50);
    key = randomize(key);
    vec = randomize(vec);
    vec2 = vec;
    vec = shuffle(vec,key);
    vec2 = shuffle(vec2,key);
    bool[[1]] result = (declassify(vec) == declassify(vec2));

    return all(result);
}

template<domain D, type T>
bool matrix_shuffle_test(D T t){
    D T[[2]] mat (50,6);
    mat = randomize(mat);
    D T[[2]] mat2 = shuffleRows(mat);
    bool[[2]] result = (declassify(mat) == declassify(mat2));

    return !all(result);
}

template<domain D, type T>
bool matrix_shuffle_test_key(D T t){
    D uint8[[1]] key (32);
    D T[[2]] mat (50,6);
    D T[[2]] mat2 (50,6);
    key = randomize(key);
    mat = randomize(mat);
    mat2 = mat;
    mat = shuffleRows(mat,key);
    mat2 = shuffleRows(mat2,key);
    bool[[2]] result = (declassify(mat) == declassify(mat2));

    return all(result);
}

template<domain D, type T>
bool random_test(D T t){
    D T[[1]] vec (50);
    D T[[1]] vec2 = randomize(vec);

    return !all(declassify(vec) == declassify(vec2));
}

void main(){
    string test_prefix = "Shuffling vectors with 50 elements without key";
    { pd_shared3p bool t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p int8 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p int16 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p int32 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p int64 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, vector_shuffle_test(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, vector_shuffle_test(t), t); }

    test_prefix = "Shuffling vectors with 50 elements with key";
    { pd_shared3p bool t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p int8 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p int16 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p int32 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p int64 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, vector_shuffle_test_key(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, vector_shuffle_test_key(t), t); }

    test_prefix = "Shuffling rows of (50,6) matrix without key";
    { pd_shared3p bool t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p int8 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p int16 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p int32 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p int64 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, matrix_shuffle_test(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, matrix_shuffle_test(t), t); }

    test_prefix = "Shuffling rows of (50,6) matrix with key";
    { pd_shared3p bool t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p int8 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p int16 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p int32 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p int64 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, matrix_shuffle_test_key(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, matrix_shuffle_test_key(t), t); }

    test_prefix = "Random test";
    { pd_shared3p bool t; test(test_prefix, random_test(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p int8 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p int16 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p int32 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p int64 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, random_test(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, random_test(t), t); }

    test_report();
}

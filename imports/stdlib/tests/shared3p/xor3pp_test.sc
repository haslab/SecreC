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
bool test_min(D T data){
    D T[[1]] temp (25);
    temp = randomize(temp);
    D T[[1]] vec = declassify(temp);
    D T result = min(temp);
    D T control = 0;
    for(uint i = 0; i < size(vec);++i){
        if(i == 0){
            control = vec[i];
        }
        else{
            if(declassify(vec[i]) < declassify(control)){
                control = vec[i];
            }
        }
    }

    return declassify(control) == declassify(result);
}

template<domain D, type T>
bool test_min2(D T data){
    D T[[1]] temp (10);
    D T[[1]] temp2 (10);
    temp = randomize(temp);
    temp2 = randomize(temp2);
    D T[[1]] vec = temp;
    D T[[1]] vec2 = temp2;
    D T[[1]] result = min(temp,temp2);
    D T[[1]] control (10) = 0;
    for(uint i = 0; i < size(vec);++i){
        if(declassify(vec[i]) <= declassify(vec2[i])){
            control[i] = vec[i];
        }
        else{
            control[i] = vec2[i];
        }
    }

    return all(declassify(control) == declassify(result));
}

template<domain D, type T>
bool test_max(D T data){
    D T[[1]] temp (25);
    temp = randomize(temp);
    D T[[1]] vec = temp;
    D T result = max(temp);
    D T control = 0;
    for(uint i = 0; i < size(vec);++i){
        if(declassify(vec[i]) > declassify(control)){
            control = vec[i];
        }
    }

    return declassify(control) == declassify(result);
}

template<domain D, type T>
bool test_max2(D T data){
    D T[[1]] temp (10);
    D T[[1]] temp2 (10);
    temp = randomize(temp);
    temp2 = randomize(temp2);
    D T[[1]] vec = temp;
    D T[[1]] vec2 = temp2;
    D T[[1]] result = max(temp,temp2);
    D T[[1]] control (10) = 0;
    for(uint i = 0; i < size(vec);++i){
        if(declassify(vec[i]) >= declassify(vec2[i])){
            control[i] = vec[i];
        }
        else{
            control[i] = vec2[i];
        }
    }

    return all(declassify(control) == declassify(result));
}

template<domain D, type T>
bool test_reshare(D T data){
    D T scalar = 0;
    scalar = randomize(scalar);
    D T scalar2 = reshare(reshare(scalar));

    if (declassify(scalar) != declassify(scalar2))
        return false;

    D T[[1]] vector (15) = 0;
    vector = randomize(vector);
    D T[[1]] vector2 = reshare(reshare(vector));

    if (!all(declassify(vector) == declassify(vector2)))
        return false;

    return true;
}

void main() {
    string test_prefix = "Min";
    { pd_shared3p xor_uint8 t; test(test_prefix, test_min(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, test_min(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, test_min(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, test_min(t), t); }

    test_prefix = "Min (2)";
    { pd_shared3p xor_uint8 t; test(test_prefix, test_min2(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, test_min2(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, test_min2(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, test_min2(t), t); }

    test_prefix = "Max";
    { pd_shared3p xor_uint8 t; test(test_prefix, test_max(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, test_max(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, test_max(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, test_max(t), t); }

    test_prefix = "Max (2)";
    { pd_shared3p xor_uint8 t; test(test_prefix, test_max2(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, test_max2(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, test_max2(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, test_max2(t), t); }

    test_prefix = "Resharing";
    { pd_shared3p xor_uint8 t; test(test_prefix, test_reshare(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, test_reshare(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, test_reshare(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, test_reshare(t), t); }

    test_report();
}

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
import matrix;
import shared3p;
import shared3p_matrix;
import shared3p_random;
import test_utility;

domain pd_shared3p shared3p;

template<domain D : shared3p,type T>
bool test_transpose(D T data){
    bool result = true;
    pd_shared3p T[[2]] mat (6,6);
    mat = randomize(mat);
    pd_shared3p T[[2]] mat2 = transpose(mat);
    for(uint i = 0; i < 6; ++i){
        if(!all(declassify(mat[:,i]) == declassify(mat2[i,:]))){
            result = false;
        }
    }

    return result;
}

template<domain D : shared3p,type T>
bool test_transpose2(D T data){
    bool result = true;
    pd_shared3p T[[3]] mat (5,5,5);
    mat = randomize(mat);
    pd_shared3p T[[3]] mat2 = transpose(mat);
    for(uint i = 0; i < 5; ++i){
        if(!all(declassify(mat[:,i,:]) == declassify(mat2[:,:,i]))){
            result = false;
        }
    }

    return result;
}

void main(){
    string test_prefix = "Matrix transpose 2D and 3D";
    { pd_shared3p bool t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p int8 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p int16 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p int32 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p int64 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, test_transpose(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, test_transpose(t), t); }

    test_prefix = "Matrix transpose 2D and 3D (2)";
    { pd_shared3p bool t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p int8 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p int16 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p int32 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p int64 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, test_transpose2(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, test_transpose2(t), t); }

    test_report();
}

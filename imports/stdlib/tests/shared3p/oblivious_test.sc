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
import shared3p_oblivious;
import oblivious;
import shared3p_random;
import test_utility;

domain pd_shared3p shared3p;

template<domain D, type T>
bool choice_test1(D T data){
    D bool cond = true;
    D T[[2]] mat (10,10);
    D T[[2]] mat2 (10,10);
    mat = randomize(mat); mat2 = randomize(mat2);
    D T[[2]] mat3 = choose(cond,mat,mat2);
    if (!all(declassify(mat) == declassify(mat3)))
        return false;

    cond = false;
    mat = randomize(mat); mat2 = randomize(mat2);
    mat3 = choose(cond,mat,mat2);
    if (!all(declassify(mat2) == declassify(mat3)))
        return false;

    return true;
}

template<domain D, type T>
bool choice_test2(D T data){
    bool result = true;
    uint column;
    D bool[[2]] cond (6,6);
    D T[[2]] mat (6,6);
    D T[[2]] mat2 (6,6);
    mat = randomize(mat); mat2 = randomize(mat2); cond = randomize(cond);
    D T[[2]] mat3 = choose(cond,mat,mat2);
    for(uint i = 0; i < 6;++i){
        for(uint j = 0; j < 6; ++j){
            if(declassify(cond[i,j])){
                if(!(declassify(mat3[i,j]) == declassify(mat[i,j]))){
                    result = false;
                    column = j;
                }
            }
            else{
                if(!(declassify(mat3[i,j]) == declassify(mat2[i,j]))){
                    result = false;
                    column = j;
                }
            }
            if (!result)
                break;
        }
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool vector_lookup_test(T data){
    bool result = true;
    pd_shared3p T scalar;
    pd_shared3p T control;
    pd_shared3p uint index;
    for(uint i = 3; i < 9;++i){
        pd_shared3p T[[1]] vec (i);
        vec = randomize(vec);
        for(uint j = 0; j < size(vec); ++j){
            index = j;
            scalar = vectorLookup(vec,index);
            if(declassify(scalar) != declassify(vec[j])){
                control = vec[j];
                result = false;
                break;
            }
        }
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool matrix_row_lookup(T data){
    bool result = true;
    pd_shared3p T[[2]] mat (5,5);
    mat = randomize(mat);
    pd_shared3p uint index;
    pd_shared3p T[[1]] row;
    public T[[1]] control;
    for(uint i = 0; i < 5; ++i){
        index = i;
        row = matrixLookupRow(mat,index);
        control = declassify(mat[i,:]);
        if(!all(declassify(row) == control)){
            result = false;
            break;
        }
    }

    return result;
}

template<type T>
bool matrix_col_lookup(T data){
    bool result = true;
    pd_shared3p T[[2]] mat (5,5);
    mat = randomize(mat);
    pd_shared3p uint index;
    pd_shared3p T[[1]] col;
    public T[[1]] control;
    for(uint i = 0; i < 5; ++i){
        index = i;
        col = matrixLookupColumn(mat,index);
        control = declassify(mat[:,i]);
        if(!all(declassify(col) == control)){
            result = false;
            break;
        }
    }

    return result;
}

template<type T>
bool matrix_lookup(T data){
    bool result = true;
    pd_shared3p T[[2]] mat (5,5);
    mat = randomize(mat);
    pd_shared3p uint row_index;
    pd_shared3p uint col_index;
    pd_shared3p T nr;
    public T control;
    for(uint i = 0; i < 5; ++i){
        row_index = i;
        for(uint j = 0; j < 5; ++j){
            col_index = j;
            nr = matrixLookup(mat,row_index,col_index);
            control = declassify(mat[i,j]);
            if(!(declassify(nr) == control)){
                result = false;
                break;
            }
        }
        if (!result)
            break;
    }

    return result;
}

template <type T>
bool vector_update(T data){
    bool result = true;
    pd_shared3p T[[1]] rand (1);
    rand = randomize(rand);
    pd_shared3p T scalar = rand[0];
    pd_shared3p uint index;
    pd_shared3p T control;
    for(uint i = 3; i < 9; ++i){
        pd_shared3p T[[1]] vec (i);
        vec = randomize(vec);
        for(uint j = 0; j < size(vec);++j){
            index = j;
            vec = vectorUpdate(vec,index,scalar);
            if(declassify(vec[j]) != declassify(scalar)){
                control = vec[j];
                result = false;
                break;
            }
        }
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool matrix_row_update(T data){
    bool result = true;
    pd_shared3p T[[2]] mat (5,5);
    mat = randomize(mat);

    pd_shared3p T[[1]] vec (5);
    vec = randomize(vec);

    pd_shared3p uint row_index;

    for(uint i = 0; i < 5; ++i){
        row_index = i;
        mat = matrixUpdateRow(mat,row_index,vec);
        if(!all(declassify(vec) == declassify(mat[i,:]))){
            result = false;
            break;
        }
    }

    return result;
}

template<type T>
bool matrix_col_update(T data){
    bool result = true;
    pd_shared3p T[[2]] mat (5,5);
    mat = randomize(mat);

    pd_shared3p T[[1]] vec (5);
    vec = randomize(vec);

    pd_shared3p uint col_index;

    for(uint i = 0; i < 5; ++i){
        col_index = i;
        mat = matrixUpdateColumn(mat,col_index,vec);
        if(!all(declassify(vec) == declassify(mat[:,i]))){
            result = false;
            break;
        }
    }

    return result;
}

template<type T>
bool matrix_update(T data){
    bool result = true;
    pd_shared3p T[[2]] mat (5,5);
    mat = randomize(mat);

    pd_shared3p T[[1]] vec (1);
    vec = randomize(vec);

    pd_shared3p T scalar = vec[0];
    pd_shared3p uint row_index;
    pd_shared3p uint col_index;

    for(uint i = 0; i < 5; ++i){
        row_index = i;
        for(uint j = 0; j < 5; ++j){
            col_index = j;
            mat = matrixUpdate(mat,row_index,col_index,scalar);
            if(!(declassify(scalar) == declassify(mat[i,j]))){
                result = false;
                break;
            }
        }
        if (!result)
            break;
    }

    return result;
}

void main(){
    string test_prefix = "Oblivious choice scalar condition";
    { pd_shared3p bool t; test(test_prefix, choice_test1(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, choice_test1(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, choice_test1(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, choice_test1(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, choice_test1(t), t); }
    { pd_shared3p int8 t; test(test_prefix, choice_test1(t), t); }
    { pd_shared3p int16 t; test(test_prefix, choice_test1(t), t); }
    { pd_shared3p int32 t; test(test_prefix, choice_test1(t), t); }
    { pd_shared3p int64 t; test(test_prefix, choice_test1(t), t); }
    // TODO not currently not supported
//    { pd_shared3p xor_uint8 t; test(test_prefix, choice_test1(t), t); }
//    { pd_shared3p xor_uint16 t; test(test_prefix, choice_test1(t), t); }
//    { pd_shared3p xor_uint32 t; test(test_prefix, choice_test1(t), t); }
//    { pd_shared3p xor_uint64 t; test(test_prefix, choice_test1(t), t); }

    test_prefix = "Oblivious choice matrix condition";
    { pd_shared3p bool t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p int8 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p int16 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p int32 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p int64 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, choice_test2(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, choice_test2(t), t); }

    test_prefix = "Oblivious vector lookup with 3-8 element vectors";
    test(test_prefix, vector_lookup_test(true), true);
    test(test_prefix, vector_lookup_test(0::uint8), 0::uint8);
    test(test_prefix, vector_lookup_test(0::uint16), 0::uint16);
    test(test_prefix, vector_lookup_test(0::uint32), 0::uint32);
    test(test_prefix, vector_lookup_test(0::uint64), 0::uint64);
    test(test_prefix, vector_lookup_test(0::int8), 0::int8);
    test(test_prefix, vector_lookup_test(0::int16), 0::int16);
    test(test_prefix, vector_lookup_test(0::int32), 0::int32);
    test(test_prefix, vector_lookup_test(0::int64), 0::int64);

    test_prefix = "Oblivious matrix row lookup in (5,5) matrix";
    test(test_prefix, matrix_row_lookup(true), true);
    test(test_prefix, matrix_row_lookup(0::uint8), 0::uint8);
    test(test_prefix, matrix_row_lookup(0::uint16), 0::uint16);
    test(test_prefix, matrix_row_lookup(0::uint32), 0::uint32);
    test(test_prefix, matrix_row_lookup(0::uint64), 0::uint64);
    test(test_prefix, matrix_row_lookup(0::int8), 0::int8);
    test(test_prefix, matrix_row_lookup(0::int16), 0::int16);
    test(test_prefix, matrix_row_lookup(0::int32), 0::int32);
    test(test_prefix, matrix_row_lookup(0::int64), 0::int64);

    test_prefix = "Oblivious matrix column lookup in (5,5) matrix";
    test(test_prefix, matrix_col_lookup(true), true);
    test(test_prefix, matrix_col_lookup(0::uint8), 0::uint8);
    test(test_prefix, matrix_col_lookup(0::uint16), 0::uint16);
    test(test_prefix, matrix_col_lookup(0::uint32), 0::uint32);
    test(test_prefix, matrix_col_lookup(0::uint64), 0::uint64);
    test(test_prefix, matrix_col_lookup(0::int8), 0::int8);
    test(test_prefix, matrix_col_lookup(0::int16), 0::int16);
    test(test_prefix, matrix_col_lookup(0::int32), 0::int32);
    test(test_prefix, matrix_col_lookup(0::int64), 0::int64);

    test_prefix = "Oblivious matrix lookup in (5,5) matrix";
    test(test_prefix, matrix_lookup(true), true);
    test(test_prefix, matrix_lookup(0::uint8), 0::uint8);
    test(test_prefix, matrix_lookup(0::uint16), 0::uint16);
    test(test_prefix, matrix_lookup(0::uint32), 0::uint32);
    test(test_prefix, matrix_lookup(0::uint64), 0::uint64);
    test(test_prefix, matrix_lookup(0::int8), 0::int8);
    test(test_prefix, matrix_lookup(0::int16), 0::int16);
    test(test_prefix, matrix_lookup(0::int32), 0::int32);
    test(test_prefix, matrix_lookup(0::int64), 0::int64);

    test_prefix = "Oblivious vector update in 3-8 element vector";
    test(test_prefix, vector_update(true), true);
    test(test_prefix, vector_update(0::uint8), 0::uint8);
    test(test_prefix, vector_update(0::uint16), 0::uint16);
    test(test_prefix, vector_update(0::uint32), 0::uint32);
    test(test_prefix, vector_update(0::uint64), 0::uint64);
    test(test_prefix, vector_update(0::int8), 0::int8);
    test(test_prefix, vector_update(0::int16), 0::int16);
    test(test_prefix, vector_update(0::int32), 0::int32);
    test(test_prefix, vector_update(0::int64), 0::int64);

    test_prefix = "Oblivious matrix row update";
    test(test_prefix, matrix_row_update(true), true);
    test(test_prefix, matrix_row_update(0::uint8), 0::uint8);
    test(test_prefix, matrix_row_update(0::uint16), 0::uint16);
    test(test_prefix, matrix_row_update(0::uint32), 0::uint32);
    test(test_prefix, matrix_row_update(0::uint64), 0::uint64);
    test(test_prefix, matrix_row_update(0::int8), 0::int8);
    test(test_prefix, matrix_row_update(0::int16), 0::int16);
    test(test_prefix, matrix_row_update(0::int32), 0::int32);
    test(test_prefix, matrix_row_update(0::int64), 0::int64);

    test_prefix = "Oblivious matrix column update";
    test(test_prefix, matrix_col_update(true), true);
    test(test_prefix, matrix_col_update(0::uint8), 0::uint8);
    test(test_prefix, matrix_col_update(0::uint16), 0::uint16);
    test(test_prefix, matrix_col_update(0::uint32), 0::uint32);
    test(test_prefix, matrix_col_update(0::uint64), 0::uint64);
    test(test_prefix, matrix_col_update(0::int8), 0::int8);
    test(test_prefix, matrix_col_update(0::int16), 0::int16);
    test(test_prefix, matrix_col_update(0::int32), 0::int32);
    test(test_prefix, matrix_col_update(0::int64), 0::int64);

    test_prefix = "Oblivious matrix update";
    test(test_prefix, matrix_update(true), true);
    test(test_prefix, matrix_update(0::uint8), 0::uint8);
    test(test_prefix, matrix_update(0::uint16), 0::uint16);
    test(test_prefix, matrix_update(0::uint32), 0::uint32);
    test(test_prefix, matrix_update(0::uint64), 0::uint64);
    test(test_prefix, matrix_update(0::int8), 0::int8);
    test(test_prefix, matrix_update(0::int16), 0::int16);
    test(test_prefix, matrix_update(0::int32), 0::int32);
    test(test_prefix, matrix_update(0::int64), 0::int64);

    test_report();
}

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
import oblivious;
import shared3p_oblivious;
import shared3p_random;
import test_utility;

domain pd_shared3p shared3p;

template<type T>
T random_float(T data){
    T rand = 1;
    pd_shared3p uint32 temp;
    pd_shared3p int8 temp2;
    T scalar;
    T scalar2;
    for(uint i = 0; i < 2; ++i){
        scalar = 0;
        while(scalar == 0 || scalar2 == 0){
            scalar = (T) declassify(randomize(temp));
            scalar2 = (T) declassify(randomize(temp2));
        }
        if((i % 2) == 0){
            rand *= scalar;
            rand *= scalar2;
        }
        else{
            rand /= scalar;
            rand /= scalar2;
        }
    }
    return rand;
}

template<domain D:shared3p,type T>
D T[[1]] random(D T[[1]] data){
    uint x_shape = size(data);
    T[[1]] rand (x_shape) = 1;
    pd_shared3p uint32[[1]] temp (x_shape);
    pd_shared3p int8[[1]] temp2 (x_shape);
    T[[1]] scalar (x_shape);
    T[[1]] scalar2 (x_shape);
    for(uint i = 0; i < 2; ++i){
        scalar[0] = 0;
        while(any(scalar == 0) || any(scalar2 == 0)){
            scalar = (T) declassify(randomize(temp));
            scalar2 = (T) declassify(randomize(temp2));
        }
        if((i % 2) == 0){
            rand *= scalar;
            rand *= scalar2;
        }
        else{
            rand /= scalar;
            rand /= scalar2;
        }
    }
    pd_shared3p T[[1]] result = rand;
    return result;
}

template<domain D:shared3p,type T>
D T[[2]] random(D T[[2]] data){
    uint x_shape = shape(data)[0];
    uint y_shape = shape(data)[1];
    T[[2]] rand (x_shape,y_shape) = 1;
    pd_shared3p uint32[[2]] temp (x_shape,y_shape);
    pd_shared3p int8[[2]] temp2 (x_shape,y_shape);
    T[[2]] scalar (x_shape,y_shape);
    T[[2]] scalar2 (x_shape,y_shape);
    for(uint i = 0; i < 2; ++i){
        scalar[0,0] = 0;
        while(any(scalar == 0) || any(scalar2 == 0)){
            scalar = (T) declassify(randomize(temp));
            scalar2 = (T) declassify(randomize(temp2));
        }
        if((i % 2) == 0){
            rand *= scalar;
            rand *= scalar2;
        }
        else{
            rand /= scalar;
            rand /= scalar2;
        }
    }
    pd_shared3p T[[2]] result = rand;
    return result;
}

template<domain D:shared3p,type T>
D T[[3]] random(D T[[3]] data){
    uint x_shape = shape(data)[0];
    uint y_shape = shape(data)[1];
    uint z_shape = shape(data)[2];
    T[[3]] rand (x_shape,y_shape,z_shape) = 1;
    pd_shared3p uint32[[3]] temp (x_shape,y_shape,z_shape);
    pd_shared3p int8[[3]] temp2 (x_shape,y_shape,z_shape);
    T[[3]] scalar (x_shape,y_shape,z_shape);
    T[[3]] scalar2 (x_shape,y_shape,z_shape);
    for(uint i = 0; i < 2; ++i){
        scalar[0,0,0] = 0;
        while(any(scalar == 0) || any(scalar2 == 0)){
            scalar = (T) declassify(randomize(temp));
            scalar2 = (T) declassify(randomize(temp2));
        }
        if((i % 2) == 0){
            rand *= scalar;
            rand *= scalar2;
        }
        else{
            rand /= scalar;
            rand /= scalar2;
        }
    }
    pd_shared3p T[[3]] result = rand;
    return result;
}

template<type T>
bool choice_test1(T data){
    pd_shared3p bool cond = true;
    pd_shared3p T[[2]] mat (3,3);
    pd_shared3p T[[2]] mat2 (3,3);
    mat = random(mat); mat2 = random(mat2);
    pd_shared3p T[[2]] mat3 = choose(cond,mat,mat2);
    if (all(declassify(mat) != declassify(mat3)))
        return false;

    cond = false;
    mat = random(mat); mat2 = random(mat2);
    mat3 = choose(cond,mat,mat2);
    if (all(declassify(mat2) != declassify(mat3)))
        return false;

    return true;
}

template<type T>
bool choice_test2(T data){
    bool result = true;
    uint column;
    pd_shared3p bool[[2]] cond (4,4);
    pd_shared3p T[[2]] mat (4,4);
    pd_shared3p T[[2]] mat2 (4,4);
    mat = random(mat); mat2 = random(mat2); cond = randomize(cond);
    pd_shared3p T[[2]] mat3 = choose(cond,mat,mat2);
    for(uint i = 0; i < 4;++i){
        for(uint j = 0; j < 4; ++j){
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
    for(uint i = 3; i < 6;++i){
        pd_shared3p T[[1]] vec (i);
        vec = random(vec);
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
    pd_shared3p T[[2]] mat (4,4);
    mat = random(mat);
    T[[2]] mat2 = declassify(mat);
    pd_shared3p uint index;
    pd_shared3p T[[1]] row;
    public T[[1]] control;
    for(uint i = 0; i < 4; ++i){
        index = i;
        row = matrixLookupRow(mat,index);
        control = mat2[i,:];
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
    pd_shared3p T[[2]] mat (4,4);
    mat = random(mat);
    T[[2]] mat2 = declassify(mat);
    pd_shared3p uint index;
    pd_shared3p T[[1]] col;
    public T[[1]] control;
    for(uint i = 0; i < 4; ++i){
        index = i;
        col = matrixLookupColumn(mat,index);
        control = mat2[:,i];
        if(!all(declassify(col) == control)){
            result = false;
            break;
        }
    }

    return result;
}

template<type T>
bool matrix_lookup(T data){
    {
        pd_shared3p uint index1 = 0;
        pd_shared3p uint index2 = 0;
        pd_shared3p T[[2]] mat2 (2,0);
        pd_shared3p T result = matrixLookup(mat2,index1,index2);
    }
    bool result = true;
    pd_shared3p T[[2]] mat (4,4);
    mat = random(mat);
    T[[2]] mat2 = declassify(mat);
    pd_shared3p uint row_index;
    pd_shared3p uint col_index;
    pd_shared3p T nr;
    public T control;
    for(uint i = 0; i < 4; ++i){
        row_index = i;
        for(uint j = 0; j < 4; ++j){
            col_index = j;
            nr = matrixLookup(mat,row_index,col_index);
            control = mat2[i,j];
            if(!(declassify(nr) == control)){
                result = false;
                break;
            }
        }
        if(!result){
            break;
        }
    }

    return result;
}

template <type T>
bool vector_update(T data){
    bool result = true;
    pd_shared3p T[[1]] rand (1);
    rand = random(rand);
    pd_shared3p T scalar = rand[0];
    pd_shared3p uint index;
    pd_shared3p T control;
    for(uint i = 3; i < 6; ++i){
        pd_shared3p T[[1]] vec (i);
        vec = random(vec);
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
    pd_shared3p T[[2]] mat (4,4);
    mat = random(mat);

    pd_shared3p T[[1]] vec (4);
    vec = random(vec);

    pd_shared3p uint row_index;

    for(uint i = 0; i < 4; ++i){
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
    pd_shared3p T[[2]] mat (4,4);
    mat = random(mat);

    pd_shared3p T[[1]] vec (4);
    vec = random(vec);

    pd_shared3p uint col_index;

    for(uint i = 0; i < 4; ++i){
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
    pd_shared3p T[[2]] mat (4,4);
    mat = random(mat);

    pd_shared3p T[[1]] vec (1);
    vec = random(vec);

    pd_shared3p T scalar = vec[0];
    pd_shared3p uint row_index;
    pd_shared3p uint col_index;

    for(uint i = 0; i < 4; ++i){
        row_index = i;
        for(uint j = 0; j < 4; ++j){
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
    test(test_prefix, choice_test1(0::float32), 0::float32);
    test(test_prefix, choice_test1(0::float64), 0::float64);

    test_prefix = "Oblivious choice matrix condition";
    test(test_prefix, choice_test2(0::float32), 0::float32);
    test(test_prefix, choice_test2(0::float64), 0::float64);

    test_prefix = "Oblivious vector lookup with 3-5 element vectors";
    test(test_prefix, vector_lookup_test(0::float32), 0::float32);
    test(test_prefix, vector_lookup_test(0::float64), 0::float64);

    test_prefix = "Oblivious matrix row lookup in (4,4) matrix";
    test(test_prefix, matrix_row_lookup(0::float32), 0::float32);
    test(test_prefix, matrix_row_lookup(0::float64), 0::float64);

    test_prefix = "Oblivious matrix column lookup in (4,4) matrix";
    test(test_prefix, matrix_col_lookup(0::float32), 0::float32);
    test(test_prefix, matrix_col_lookup(0::float64), 0::float64);

    test_prefix = "Oblivious matrix lookup in (4,4) matrix";
    test(test_prefix, matrix_lookup(0::float32), 0::float32);
    test(test_prefix, matrix_lookup(0::float64), 0::float64);

    test_prefix = "Oblivious vector update";
    test(test_prefix, vector_update(0::float32), 0::float32);
    test(test_prefix, vector_update(0::float64), 0::float64);

    test_prefix = "Oblivious matrix row update";
    test(test_prefix, matrix_row_update(0::float32), 0::float32);
    test(test_prefix, matrix_row_update(0::float64), 0::float64);

    test_prefix = "Oblivious matrix column update";
    test(test_prefix, matrix_col_update(0::float32), 0::float32);
    test(test_prefix, matrix_col_update(0::float64), 0::float64);

    test_prefix = "Oblivious matrix update";
    test(test_prefix, matrix_update(0::float32), 0::float32);
    test(test_prefix, matrix_update(0::float64), 0::float64);

    test_report();
}

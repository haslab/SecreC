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
bool test_flattening(T data){
    bool result = true;
    pd_shared3p T[[2]] temp (3,3);
    temp = random(temp);
    T[[2]] object = declassify(temp);
    T[[1]] vec = flatten(object);
    for(uint i = 0; i < shape(object)[0];++i){
        for(uint j = 0; j < shape(object)[1];++j){
            if(object[i,j] != vec[(3*i + j)]){
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

template<type T>
bool equal_shapes_test(T data){
    {
        pd_shared3p T[[2]] mat (3,3);
        pd_shared3p T[[2]] mat2 (3,3);
        T[[2]] mat3 = declassify(random(mat));
        T[[2]] mat4 = declassify(random(mat2));
        bool result = shapesAreEqual(mat3,mat4);
        if (!all(shape(mat3) == shape(mat4)))
            return false;
    }
    {
        pd_shared3p T[[2]] mat (3,2);
        pd_shared3p T[[2]] mat2 (5,1);
        T[[2]] mat3 = declassify(random(mat));
        T[[2]] mat4 = declassify(random(mat2));
        bool result = shapesAreEqual(mat3,mat4);
        if(all(shape(mat3) == shape(mat4)))
            return false;
    }

    return true;
}

template<type T>
bool test_sum(T data){
    pd_shared3p T[[1]] temp (6);
    T[[1]] vec = declassify(random(temp));
    T result = sum(vec);
    T control = 0;
    for(uint i = 0; i < size(vec);++i){
        control += vec[i];
    }

    return all(control == result);
}


template<type T>
bool test_sum2(T data){
    pd_shared3p T[[1]] temp (6);
    T[[1]] vec = declassify(random(temp));
    T[[1]] result = sum(vec,2::uint);
    uint startingIndex = 0;
    uint endIndex = size(vec) / 2;
    T[[1]] control (2)= 0;
    for(uint i = 0;i < 2;++i){
        for(uint j = startingIndex;j < endIndex;++j){
            control[i] += vec[j];
        }
        startingIndex = 3;
        endIndex = 6;
    }

    return all(control == result);
}

template<type T>
bool test_product(T data){
    pd_shared3p T[[1]] temp (6);
    T[[1]] vec = declassify(random(temp));
    T result = product(vec);
    T control = 1;
    for(uint i = 0; i < size(vec);++i){
        control *= vec[i];
    }

    return control == result;
}

template<type T>
bool test_product2(T data){
    pd_shared3p T[[1]] temp (6);
    T[[1]] vec = declassify(random(temp));
    T[[1]] result = product(vec,2::uint);
    T[[1]] control (2)= 1;
    uint startingIndex = 0;
    uint endIndex = size(vec) / 2;
    for(uint i = 0; i < 2;++i){
        for(uint j = startingIndex; j < endIndex; ++j){
            control[i] *= vec[j];
        }
        startingIndex += size(vec) / 2;
        endIndex += size(vec) / 2;
    }

    return all(control == result);
}

void main(){
    string test_prefix = "Flattening utility";
    test(test_prefix, test_flattening(0::float32), 0::float32);
    test(test_prefix, test_flattening(0::float64), 0::float64);

    test_prefix = "Shapes are equal utility";
    test(test_prefix, equal_shapes_test(0::float32), 0::float32);
    test(test_prefix, equal_shapes_test(0::float64), 0::float64);

    test_prefix = "Sum";
    test(test_prefix, test_sum(0::float32), 0::float32);
    test(test_prefix, test_sum(0::float64), 0::float64);

    test_prefix = "Sum (2)";
    test(test_prefix, test_sum2(0::float32), 0::float32);
    test(test_prefix, test_sum2(0::float64), 0::float64);

    test_prefix = "Product";
    test(test_prefix, test_product(0::float32), 0::float32);
    test(test_prefix, test_product(0::float64), 0::float64);

    test_prefix = "Product (2)";
    test(test_prefix, test_product2(0::float32), 0::float32);
    test(test_prefix, test_product2(0::float64), 0::float64);

    test_report();
}

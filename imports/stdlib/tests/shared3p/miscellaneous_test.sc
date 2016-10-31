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

module miscellaneous_test;

import stdlib;
import shared3p;
import shared3p_random;
import test_utility;

domain pd_shared3p shared3p;

template<type T>
T random_float(T data){
    T rand = 1;
    for(uint i = 0; i < 2; ++i){
        pd_shared3p uint32 temp;
        pd_shared3p int8 temp2;
        while(declassify(temp) == 0 || declassify(temp2) == 0){
            temp = randomize(temp);
            temp2 = randomize(temp2);
        }
        T scalar = (T) declassify(temp);
        T scalar2 = (T) declassify(temp2);
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

template<domain D: shared3p,type T>
D T[[1]] random(D T[[1]] data){
    uint x_shape = shape(data)[0];
    T[[1]] temp (x_shape);
    for(uint i = 0; i < x_shape;++i){
        temp[i] = random_float(0::T);
    }
    D T[[1]] result = temp;
    return result;
}

template<domain D, type T>
bool cast_bool_to_type(D T data) {
    bool result = true;
    D bool[[1]] temp (5);
    D bool[[1]] a = randomize(temp);
    D T[[1]] b (5) = (T)a;
    for (uint i = 0; i < 5; ++i) {
        if (declassify(a[i]) == true && declassify(b[i]) == 0) {
            result = false;
            break;
        }
        if (declassify(a[i]) == false && declassify(b[i]) == 1) {
            result = false;
            break;
        }
    }

    return result;
}

template<domain D, type T>
bool cast_type_to_bool(D T data) {
    bool result = true;
    D T[[1]] temp (10);
    D T[[1]] a = randomize(temp);
    a[0] = 0;
    a[1] = 1;
    a[2] = -1;

    D bool[[1]] b (10) = (bool)a;

    for (uint i = 0; i < 10; ++i) {
        if (declassify(b[i]) == true && declassify(a[i]) == 0) {
            result = false;
            break;
        }
        if (declassify(b[i]) == false && declassify(a[i]) != 0) {
            result = false;
            break;
        }
    }

    return result;
}

template<domain D1, type T1, domain D2, type T2, dim N>
bool cast_type_to_type(D1 T1 [[N]] t1, D2 T2 [[N]] t2) {
    D2 T2[[1]] c = (T2)(t1);
    return all(declassify(c) == declassify(t2));
}

void main(){
    string test_prefix = "Casting values";
    {
        pd_shared3p bool a;
        { pd_shared3p uint8 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p uint16 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p uint32 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p uint64 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p int8 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p int16 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p int32 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p int64 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p xor_uint8 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p xor_uint16 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p xor_uint32 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p xor_uint64 b; test(test_prefix, cast_bool_to_type(b), a, b); }
//        { pd_shared3p float32 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p float32 b; test(test_prefix, false, a, b); }
//        { pd_shared3p float64 b; test(test_prefix, cast_bool_to_type(b), a, b); }
        { pd_shared3p float64 b; test(test_prefix, false, a, b); }
        { pd_shared3p uint8 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p uint16 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p uint32 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p uint64 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p int8 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p int16 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p int32 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p int64 b; test(test_prefix, cast_type_to_bool(b), b, a); }
//        { pd_shared3p xor_uint8 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p xor_uint8 b; test(test_prefix, false, b, a); }
//        { pd_shared3p xor_uint16 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p xor_uint16 b; test(test_prefix, false, b, a); }
//        { pd_shared3p xor_uint32 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p xor_uint32 b; test(test_prefix, false, b, a); }
//        { pd_shared3p xor_uint64 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p xor_uint64 b; test(test_prefix, false, b, a); }
//        { pd_shared3p float32 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p float32 b; test(test_prefix, false, b, a); }
//        { pd_shared3p float64 b; test(test_prefix, cast_type_to_bool(b), b, a); }
        { pd_shared3p float64 b; test(test_prefix, false, b, a); }
    }

    {
        pd_shared3p uint8[[1]] a = {0, 100, 200, 255};
        {
            pd_shared3p uint16[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int8[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int16[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int32[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int64[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float32[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float64[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
    }
    {
        pd_shared3p uint16[[1]] a = {0,15385,38574,65535};
        {
            pd_shared3p uint8[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int8[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int16[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int32[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int64[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float32[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float64[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
    }
    {
        pd_shared3p uint32[[1]] a = {0,21424,21525341,4294967295};
        {
            pd_shared3p uint8[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int8[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int16[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int32[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int64[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float32[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float64[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
    }
    {
        pd_shared3p uint64[[1]] a = {0,55161532,142234215413552,18446744073709551615};
        {
            pd_shared3p uint8[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int8[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int16[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int64[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            //test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float64[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
    }
    {
        pd_shared3p int8[[1]] a = {-128,-40,40,127};
        {
            pd_shared3p uint8[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int16[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int32[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int64[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {-128,-40,40,127};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {-128,-40,40,127};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {-128,-40,40,127};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {-128,-40,40,127};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float32[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float64[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
    }
    {
        pd_shared3p int16[[1]] a = {-32768,-16325,12435,32767};
        {
            pd_shared3p uint8[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int8[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int32[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int64[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {-32768,-16325,12435,32767};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {-32768,-16325,12435,32767};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {-32768,-16325,12435,32767};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {-32768,-16325,12435,32767};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float32[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float64[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
    }
    {
        pd_shared3p int32[[1]] a = {-2147483648,-483648,2147483,2147483647};
        {
            pd_shared3p uint8[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int8[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int16[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int64[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {-2147483648,-483648,2147483,2147483647};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {-2147483648,-483648,2147483,2147483647};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {-2147483648,-483648,2147483,2147483647};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {-2147483648,-483648,2147483,2147483647};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float32[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float64[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
    }
    {
        pd_shared3p int64[[1]] a = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
        {
            pd_shared3p uint8[[1]] b =  {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int8[[1]] b =  {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int16[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p int32[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float32[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float64[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
    }
    {
        pd_shared3p xor_uint8[[1]] a = {0, 100, 200, 255};
        {
            pd_shared3p uint8[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int8[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int16[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int32[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int64[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float32[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float64[[1]] b = {0, 100, 200, 255};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
    }
    {
        pd_shared3p xor_uint16[[1]] a = {0,15385,38574,65535};
        {
            pd_shared3p uint8[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int8[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int16[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int32[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int64[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float32[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float64[[1]] b = {0,15385,38574,65535};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
    }
    {
        pd_shared3p xor_uint32[[1]] a = {0,21424,21525341,4294967295};
        {
            pd_shared3p uint8[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int8[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int16[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int32[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int64[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float32[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float64[[1]] b = {0,21424,21525341,4294967295};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
    }
    {
        pd_shared3p xor_uint64[[1]] a = {0,55161532,142234215413552,18446744073709551615};
        {
            pd_shared3p uint8[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int8[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int16[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int64[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
        {
            pd_shared3p float32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float64[[1]] b = {0,55161532,142234215413552,18446744073709551615};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
    }
    {
        pd_shared3p float32[[1]] a = {-3.40282e+38,0.0,1.17549e-38,1.0,3.40282e+38};
        {
            pd_shared3p uint8[[1]] b = {UINT8_MIN,0,0,1,UINT8_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {UINT16_MIN,0,0,1,UINT16_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {UINT32_MIN,0,0,1,UINT32_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {UINT64_MIN,0,0,1,UINT64_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int8[[1]] b = {INT8_MIN,0,0,1,INT8_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int16[[1]] b = {INT16_MIN,0,0,1,INT16_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int32[[1]] b = {INT32_MIN,0,0,1,INT32_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int64[[1]] b = {INT64_MIN,0,0,1,INT64_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {UINT8_MIN,0,0,1,UINT8_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {UINT16_MIN,0,0,1,UINT16_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {UINT32_MIN,0,0,1,UINT32_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {UINT64_MIN,0,0,1,UINT64_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float64[[1]] b = {-3.40282e+38,0,1.17549e-38,1,3.40282e+38};
            test(test_prefix, cast_type_to_type(a, b), a, b);
        }
    }
    {
        pd_shared3p float64[[1]] a = {-1.79769e+308,0.0,2.22507e-308,1.0,1.79769e+308};
        {
            pd_shared3p uint8[[1]] b = {UINT8_MIN,0,0,1,UINT8_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint16[[1]] b = {UINT16_MIN,0,0,1,UINT16_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint32[[1]] b = {UINT32_MIN,0,0,1,UINT32_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p uint64[[1]] b = {UINT64_MIN,0,0,1,UINT64_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int8[[1]] b = {INT8_MIN,0,0,1,INT8_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int16[[1]] b = {INT16_MIN,0,0,1,INT16_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int32[[1]] b = {INT32_MIN,0,0,1,INT32_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p int64[[1]] b = {INT64_MIN,0,0,1,INT64_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint8[[1]] b = {UINT8_MIN,0,0,1,UINT8_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint16[[1]] b = {UINT16_MIN,0,0,1,UINT16_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint32[[1]] b = {UINT32_MIN,0,0,1,UINT32_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p xor_uint64[[1]] b = {UINT64_MIN,0,0,1,UINT64_MAX};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
        {
            pd_shared3p float32[[1]] b = {-1.79769e+308,0.0,2.22507e-308,1.0,1.79769e+308};
//            test(test_prefix, cast_type_to_type(a, b), a, b);
            test(test_prefix, false, a, b);
        }
    }

    test_report();
}

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
T random_float(T data) {
    T rand = 1;
    for (uint i = 0; i < 2; ++i) {
        pd_shared3p uint32 temp;
        pd_shared3p int8 temp2;
        while(declassify(temp) == 0 || declassify(temp2) == 0) {
            temp = randomize(temp);
            temp2 = randomize(temp2);
        }
        T scalar = (T) declassify(temp);
        T scalar2 = (T) declassify(temp2);
        if ((i % 2) == 0) {
            rand *= scalar;
            rand *= scalar2;
        } else {
            rand /= scalar;
            rand /= scalar2;
        }
    }
    return rand;
}

float32[[1]] randomize(float32[[1]] data) {
    uint s = size(data);
    for (uint i = 0; i < s; ++i)
        data[i] = random_float(0::float32);
    return data;
}

float64[[1]] randomize(float64[[1]] data) {
    uint s = size(data);
    for (uint i = 0; i < s; ++i)
        data[i] = random_float(0::float64);
    return data;
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

template <type T, dim N>
bool test_classification(T[[N]] value){
    public T[[N]] a; a = value;
    pd_shared3p T[[N]] b; b = a;
    a = declassify(b);
    return all(a == value);
}

void main() {
    float32 FLOAT32_MAX = 3.4028234e38;
    float64 FLOAT64_MAX = 1.7976931348623157e308;
    float32 FLOAT32_MIN = 1.18e-38;
    float64 FLOAT64_MIN = 2.2250738585072014e-308;

    string test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with 0 ";
    test(test_prefix, test_classification(0::float32), 0::float32);
    test(test_prefix, test_classification(0::float64), 0::float64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with 1.0";
    test(test_prefix, test_classification(1::float32), 0::float32);
    test(test_prefix, test_classification(1::float64), 0::float64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with -1.0";
    test(test_prefix, test_classification(-11::float32), 0::float32);
    test(test_prefix, test_classification(-11::float64), 0::float64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with MAX positive values";
    test(test_prefix, test_classification(FLOAT32_MAX), 0::float32);
    test(test_prefix, test_classification(FLOAT64_MAX), 0::float64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with MAX negative values";
    test(test_prefix, test_classification(-FLOAT32_MAX), 0::float32);
    test(test_prefix, test_classification(-FLOAT64_MAX), 0::float64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with MIN positive values";
    test(test_prefix, test_classification(FLOAT32_MIN), 0::float32);
    test(test_prefix, test_classification(FLOAT64_MIN), 0::float64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with MIN negative values";
    test(test_prefix, test_classification(-FLOAT32_MIN), 0::float32);
    test(test_prefix, test_classification(-FLOAT64_MIN), 0::float64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with random values";
    {
        float32 pub = 162874612958512.981269182562198642198623;
        test(test_prefix, test_classification(pub), pub);
        pub = 1982651298573509437643.598327659803275819256127984621748;
        test(test_prefix, test_classification(pub), pub);
        pub = 59036783265903267329856195.7832658723657128561245872457583265823;
        test(test_prefix, test_classification(pub), pub);
        pub = 43298537829532953.87326587325632875632874215428714;
        test(test_prefix, test_classification(pub), pub);
        pub = -29872165932578329573285.89832659823657328563;
        test(test_prefix, test_classification(pub), pub);
        pub = -6732854632859328563298.648732458128742198;
        test(test_prefix, test_classification(pub), pub);
        pub = -9853467894363275093275893247325.8932659873265832754;
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float32);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float32);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float32);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float32);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float32);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float32);
        test(test_prefix, test_classification(pub), pub);
    }
    {
        float64 pub = 162874612923523532558512.981269182562643643634198642198623;
        test(test_prefix, test_classification(pub), pub);
        pub = 1982632423423551298573509437643.59832765980327581918264219849256127984621748;
        test(test_prefix, test_classification(pub), pub);
        pub = 5903678326590332512759267329856195.7832658723657128566219841245872457583265823;
        test(test_prefix, test_classification(pub), pub);
        pub = 43298537216985416274832593257829532953.873265873256328329807512475632874215428714;
        test(test_prefix, test_classification(pub), pub);
        pub = -29872121984721503265932578329573285.89832659329759832412823657328563;
        test(test_prefix, test_classification(pub), pub);
        pub = -32047325906732854632859332532528563298.64873245813253253228742198;
        test(test_prefix, test_classification(pub), pub);
        pub = -985346789436398216598326578356275093275893247325.89326598798127492143265832754;
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float64);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float64);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float64);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float64);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float64);
        test(test_prefix, test_classification(pub), pub);
        pub = random_float(0::float64);
        test(test_prefix, test_classification(pub), pub);
    }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with -1/3 and +1/3";
    {
        float32 pub = 1/3;
        test(test_prefix, test_classification(pub), pub);
        pub = -1/3;
        test(test_prefix, test_classification(pub), pub);
    }
    {
        float64 pub = 1/3;
        test(test_prefix, test_classification(pub), pub);
        pub = -1/3;
        test(test_prefix, test_classification(pub), pub);
    }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with 0 vectors ";
    {
        float32[[1]] pub (15)= 0.0;
        test(test_prefix, test_classification(pub), pub);
    }
    {
        float64[[1]] pub (15)= 0.0;
        test(test_prefix, test_classification(pub), pub);
    }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with 1.0 vectors";
    {
        float32[[1]] pub (15)= 1.0;
        test(test_prefix, test_classification(pub), pub);
    }
    {
        float64[[1]] pub (15)= 1.0;
        test(test_prefix, test_classification(pub), pub);
    }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with -1.0 vectors";
    {
        float32[[1]] pub (15)= -1.0;
        test(test_prefix, test_classification(pub), pub);
    }
    {
        float64[[1]] pub (15)= -1.0;
        test(test_prefix, test_classification(pub), pub);
    }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC conversion with Float32/64 MAX/MIN values over 1-10 element vectors";
    for(uint i = 1; i < 11; ++i){
        {
            float32[[1]] pub (i) = FLOAT32_MAX;
            test(test_prefix, test_classification(pub), pub);
            pub = -FLOAT32_MAX;
            test(test_prefix, test_classification(pub), pub);
            float32[[1]] pub2 (i) = FLOAT32_MIN;
            test(test_prefix, test_classification(pub2), pub2);
            pub2 = -FLOAT32_MIN;
            test(test_prefix, test_classification(pub2), pub2);
        }
        {
            float64[[1]] pub (i) = FLOAT64_MAX;
            test(test_prefix, test_classification(pub), pub);
            pub = -FLOAT64_MAX;
            test(test_prefix, test_classification(pub), pub);
            float64[[1]] pub2 (i) = FLOAT64_MIN;
            test(test_prefix, test_classification(pub2), pub2);
            pub2 = -FLOAT64_MIN;
            test(test_prefix, test_classification(pub2), pub2);
        }
    }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with random vectors";
    {
        float32[[1]] pub (15)= 162874612958512.981269182562198642198623;
        test(test_prefix, test_classification(pub), pub);
        pub = 1982651298573509437643.598327659803275819256127984621748;
        test(test_prefix, test_classification(pub), pub);
        pub = 59036783265903267329856195.7832658723657128561245872457583265823;
        test(test_prefix, test_classification(pub), pub);
        pub = 43298537829532953.87326587325632875632874215428714;
        test(test_prefix, test_classification(pub), pub);
        pub = -29872165932578329573285.89832659823657328563;
        test(test_prefix, test_classification(pub), pub);
        pub = -6732854632859328563298.648732458128742198;
        test(test_prefix, test_classification(pub), pub);
        pub = -9853467894363275093275893247325.8932659873265832754;
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
    }
    {
        float64[[1]] pub (15)= 162874612923523532558512.981269182562643643634198642198623;
        test(test_prefix, test_classification(pub), pub);
        pub = 1982632423423551298573509437643.59832765980327581918264219849256127984621748;
        test(test_prefix, test_classification(pub), pub);
        pub = 5903678326590332512759267329856195.7832658723657128566219841245872457583265823;
        test(test_prefix, test_classification(pub), pub);
        pub = 43298537216985416274832593257829532953.873265873256328329807512475632874215428714;
        test(test_prefix, test_classification(pub), pub);
        pub = -29872121984721503265932578329573285.89832659329759832412823657328563;
        test(test_prefix, test_classification(pub), pub);
        pub = -32047325906732854632859332532528563298.64873245813253253228742198;
        test(test_prefix, test_classification(pub), pub);
        pub = -985346789436398216598326578356275093275893247325.89326598798127492143265832754;
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
        pub = randomize(pub);
        test(test_prefix, test_classification(pub), pub);
    }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC for Float32/64 with -1/3 and +1/3 vectors";
    {
        float32[[1]] pub (15)= 1/3;
        test(test_prefix, test_classification(pub), pub);
        pub = -1/3;
        test(test_prefix, test_classification(pub), pub);
    }
    {
        float64[[1]] pub (15)= 1/3;
        test(test_prefix, test_classification(pub), pub);
        pub = -1/3;
        test(test_prefix, test_classification(pub), pub);
    }

    test_report();
}

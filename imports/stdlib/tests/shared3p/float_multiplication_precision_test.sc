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


/****************************************************
*****************************************************
*****************************************************
*****/      public uint test_amount = 10;       /****
******  increase for more accurate percentages  *****
*****************************************************
*****************************************************
*****************************************************/


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

template<type T>
PrecisionTest<T> test_multiplication(T data){
    T max_absolute = 0, max_relative = 0;
    T temp; T temp2;
    pd_shared3p T a;
    pd_shared3p T b;
    T sum; T sum2;
    for(uint i = 0; i < test_amount; ++i){
        a = classify(random_float(0::T)); b = classify(random_float(0::T));
        sum = declassify(a*b); sum2 = declassify(a) * declassify(b);
        temp = sum-sum2; temp2 = sum2;
        if(temp < 0){temp = -temp};
        if(temp2 < 0){temp2 = -temp2};
        if (max_absolute < temp)
            max_absolute = temp;
        if (max_relative < temp / temp2)
            max_relative = temp / temp2;
    }

    public PrecisionTest<T> rv;
    rv.res = true;
    rv.max_abs_error = max_absolute;
    rv.max_rel_error = max_relative;

    return rv;
}

void main(){
    string test_prefix = "Float32/64 Multiplication precision";
    {
        PrecisionTest<float32> rv = test_multiplication(0::float32);
        test(test_prefix, rv);
    }
    {
        PrecisionTest<float64> rv = test_multiplication(0::float64);
        test(test_prefix, rv);
    }

    test_report();
}

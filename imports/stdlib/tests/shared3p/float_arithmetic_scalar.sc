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
import test_utility;

domain pd_shared3p shared3p;

template<type T>
bool test_addition_random(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {0,999,999999,-2,-1001,-1000001,1,1000,1000000,-1,-1000,-1000000,2,1001,1000001,0,-999,-999999};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            a = in[j]; b = (T)i;
            c = a + b;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
            c = b + a;

            if (declassify(c) != control[cur_pos]){
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_addition_random2(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {0,999,999999,-2,-1001,-1000001,1,1000,1000000,-1,-1000,-1000000,2,1001,1000001,0,-999,-999999};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            a = in[j]; d = (T)i;
            c = a + d;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
            c = d + a;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_addition_random3(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {0,999,999999,-2,-1001,-1000001,1,1000,1000000,-1,-1000,-1000000,2,1001,1000001,0,-999,-999999};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            d = in[j]; a = (T)i;
            c = d + a;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
            c = a + d;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_addition_random4(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {0,999,999999,-2,-1001,-1000001,1,1000,1000000,-1,-1000,-1000000,2,1001,1000001,0,-999,-999999};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d; T e; T f;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            d = in[j]; e = (T)i;
            f = d + e;

            if (f != control[cur_pos]) {
                result = false;
                break;
            }
            f = e + d;

            if (f != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_subtraction_random(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {2,1001,1000001,0,-999,-999999,1,1000,1000000,-1,-1000,-1000000,0,999,999999,-2,-1001,-1000001};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            a = in[j]; b = (T)i;
            c = a - b;
            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_subtraction_random2(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {2,1001,1000001,0,-999,-999999,1,1000,1000000,-1,-1000,-1000000,0,999,999999,-2,-1001,-1000001};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            a = in[j]; d = (T)i;
            c = a - d;
            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_subtraction_random3(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {2,1001,1000001,0,-999,-999999,1,1000,1000000,-1,-1000,-1000000,0,999,999999,-2,-1001,-1000001};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            d = in[j]; a = (T)i;
            c = d - a;
            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_subtraction_random4(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {2,1001,1000001,0,-999,-999999,1,1000,1000000,-1,-1000,-1000000,0,999,999999,-2,-1001,-1000001};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d; T e; T f;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            d = in[j]; e = (T)i;
            f = d - e;
            if (f != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_multiplication_random(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {-1,-1000,-1000000,1,1000,1000000,0,0,0,0,0,0,1,1000,1000000,-1,-1000,-1000000};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            a = in[j]; b = (T)i;
            c = a * b;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
            c = b * a;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_multiplication_random2(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {-1,-1000,-1000000,1,1000,1000000,0,0,0,0,0,0,1,1000,1000000,-1,-1000,-1000000};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            a = in[j]; d = (T)i;
            c = a * d;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
            c = d * a;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_multiplication_random3(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {-1,-1000,-1000000,1,1000,1000000,0,0,0,0,0,0,1,1000,1000000,-1,-1000,-1000000};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            d = in[j]; a = (T)i;
            c = d * a;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
            c = a * d;

            if (declassify(c) != control[cur_pos]){
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_multiplication_random4(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {-1,-1000,-1000000,1,1000,1000000,0,0,0,0,0,0,1,1000,1000000,-1,-1000,-1000000};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d; T e; T f;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            d = in[j]; e = (T)i;
            f = d * e;

            if (f != control[cur_pos]) {
                result = false;
                break;
            }
            f = e * d;

            if (f != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_division_random(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {-1,-0.001,-0.000001,1,0.001,0.000001,0,0,0,0,0,0,1,0.001,0.000001,-1,-0.001,-0.000001};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            a = in[j]; b = (T)i;
            c = b / a;

            if (declassify(c) != control[cur_pos]) {
                result = false;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_division_random2(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {-1,-0.001,-0.000001,1,0.001,0.000001,0,0,0,0,0,0,1,0.001,0.000001,-1,-0.001,-0.000001};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            a = in[j]; d = (T)i;
            c = d / a;

            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_division_random3(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {-1,-0.001,-0.000001,1,0.001,0.000001,0,0,0,0,0,0,1,0.001,0.000001,-1,-0.001,-0.000001};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            d = in[j]; a = (T)i;
            c = a / d;
            if (declassify(c) != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

template<type T>
bool test_division_random4(T data){
    T[[1]] in = {1,1000,1000000,-1,-1000,-1000000};
    T[[1]] control = {-1,-0.001,-0.000001,1,0.001,0.000001,0,0,0,0,0,0,1,0.001,0.000001,-1,-0.001,-0.000001};
    bool result = true;
    uint temp = 0;
    uint cur_pos = 0;
    pd_shared3p T a;pd_shared3p T b;pd_shared3p T c;
    T d; T e; T f;
    for(int i = -1; i < 2;++i){
        for(uint j = 0; j < 6; ++j){
            cur_pos = (temp*6) + j;
            d = in[j]; e = (T)i;
            f = e / d;
            if (f != control[cur_pos]) {
                result = false;
                break;
            }
        }
        temp += 1;
        if (!result)
            break;
    }

    return result;
}

void main(){
    // TODO Some of the test may currently not make sense.

    string test_prefix = "Addition with two private values";
    {
        pd_shared3p float32 a = 15, b = 174, c = 189;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 175, b = 45876, c = 46051;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }

    test_prefix = "Addition with one private one public value";
    {
        pd_shared3p float32 a = 15; float32 b = 174; pd_shared3p float32 c = 189;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 175; float64 b = 45876; pd_shared3p float64 c = 46051;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }

    test_prefix = "Addition with one private one public value(2)";
    {
        pd_shared3p float32 a = 15; float32 b = 174; pd_shared3p float32 c = 189;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 175; float64 b = 45876; pd_shared3p float64 c = 46051;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }

    test_prefix = "Addition with important values. All combinations of public and private";
    test(test_prefix, test_addition_random(0::float32), 0::float32);
    test(test_prefix, test_addition_random2(0::float32), 0::float32);
    test(test_prefix, test_addition_random3(0::float32), 0::float32);
    test(test_prefix, test_addition_random4(0::float32), 0::float32);
    test(test_prefix, test_addition_random(0::float64), 0::float64);
    test(test_prefix, test_addition_random2(0::float64), 0::float64);
    test(test_prefix, test_addition_random3(0::float64), 0::float64);
    test(test_prefix, test_addition_random4(0::float64), 0::float64);

    test_prefix = "Subtraction with two private values";
    {
        pd_shared3p float32 a = 15, b = 174, c = 159;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 175, b = 45876, c = 45701;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }

    test_prefix = "Subtraction with one private one public value";
    {
        pd_shared3p float32 a = 15; float32 b = 174; pd_shared3p float32 c = 159;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 175; float64 b = 45876; pd_shared3p float64 c = 45701;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }

    test_prefix = "Subtraction with one private one public value(2)";
    {
        pd_shared3p float32 a = 174; float32 b = 15; pd_shared3p float32 c = 159;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 45876; float64 b = 175; pd_shared3p float64 c = 45701;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }

    test_prefix = "Subtraction with private-private important values";
    test(test_prefix, test_subtraction_random(0::float32), 0::float32);
    test(test_prefix, test_subtraction_random2(0::float32), 0::float32);
    test(test_prefix, test_subtraction_random3(0::float32), 0::float32);
    test(test_prefix, test_subtraction_random4(0::float32), 0::float32);
    test(test_prefix, test_subtraction_random(0::float64), 0::float64);
    test(test_prefix, test_subtraction_random2(0::float64), 0::float64);
    test(test_prefix, test_subtraction_random3(0::float64), 0::float64);
    test(test_prefix, test_subtraction_random4(0::float64), 0::float64);

    test_prefix = "Multiplication with two private values";
    {
        pd_shared3p float32 a = 15, b = 12, c = 180;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 175, b = 139, c = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }

    test_prefix = "Multiplication with one private one public value";
    {
        pd_shared3p float32 a = 15; float32 b = 12; pd_shared3p float32 c = 180;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 175; float64 b = 139; pd_shared3p float64 c = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }

    test_prefix = "Multiplication with one private one public value(2)";
    {
        pd_shared3p float32 a = 15; float32 b = 12; pd_shared3p float32 c = 180;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 175; float64 b = 139; pd_shared3p float64 c = 24325;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }

    test_prefix = "Multiplication with important values. All combinations of public and private";
    test(test_prefix, test_multiplication_random(0::float32), 0::float32);
    test(test_prefix, test_multiplication_random2(0::float32), 0::float32);
    test(test_prefix, test_multiplication_random3(0::float32), 0::float32);
    test(test_prefix, test_multiplication_random4(0::float32), 0::float32);
    test(test_prefix, test_multiplication_random(0::float64), 0::float64);
    test(test_prefix, test_multiplication_random2(0::float64), 0::float64);
    test(test_prefix, test_multiplication_random3(0::float64), 0::float64);
    test(test_prefix, test_multiplication_random4(0::float64), 0::float64);

    test_prefix = "Division with two private values";
    {
        pd_shared3p float32 a = 15, b = 174, c = 11.6;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 180, b = 45900, c = 255;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }

    test_prefix = "Division with one private one public value";
    {
        pd_shared3p float32 a = 15; float32 b = 174; pd_shared3p float32 c = 11.6;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 180; float64 b = 45900; pd_shared3p float64 c = 255;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }

    test_prefix = "Division with one private one public value(2)";
    {
        pd_shared3p float32 a = 180; float32 b = 15; pd_shared3p float32 c = 12;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 45900; float64 b = 180; pd_shared3p float64 c = 255;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }

    test_prefix = "private 0 divided with random public values";
    {
        float32 a = 2398; pd_shared3p float32 b = 0;pd_shared3p float32 c = 0;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        float64 a = 9083275; pd_shared3p float64 b = 0;pd_shared3p float64 c = 0;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }

    test_prefix = "Division of private 0 with public 2^n";
    {
        bool result = true;
        pd_shared3p float32 a = 0;
        float32 b = 2;
        pd_shared3p float32 c;
        for(uint i = 0; i < 10; ++i){
            c = a/b;
            if (declassify(c) != 0) {
                result = false;
                break;
            }
            b *= 2;
        }

        test(test_prefix, result, c);
    }
    {
        bool result = true;
        pd_shared3p float64 a = 0;
        float64 b = 2;
        pd_shared3p float64 c;
        for(uint i = 0; i < 10; ++i){
            c = a/b;
            if (declassify(c) != 0) {
                result = false;
                break;
            }
            b *= 2;
        }

        test(test_prefix, result, c);
    }

    test_prefix = "Division accuracy private";
    {
        pd_shared3p float32 a = 645, b = 40, c = 16.125;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }
    {
        pd_shared3p float64 a = 645, b = 40, c = 16.125;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }

    test_prefix = "Division with important values. All combinations of public and private";
    test(test_prefix, test_division_random(0::float32), 0::float32);
    test(test_prefix, test_division_random2(0::float32), 0::float32);
    test(test_prefix, test_division_random3(0::float32), 0::float32);
    test(test_prefix, test_division_random4(0::float32), 0::float32);
    test(test_prefix, test_division_random(0::float64), 0::float64);
    test(test_prefix, test_division_random2(0::float64), 0::float64);
    test(test_prefix, test_division_random3(0::float64), 0::float64);
    test(test_prefix, test_division_random4(0::float64), 0::float64);

    test_report();
}

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

module sorting_test;

import stdlib;
import matrix;
import shared3p;
import shared3p_matrix;
import oblivious;
import shared3p_random;
import shared3p_sort;
import shared3p_bloom;
import shared3p_string;
import shared3p_aes;
import shared3p_join;
import profiling;
import shared3p;
import test_utility;

domain pd_shared3p shared3p;

template<type T>
bool test_sign(T data){
    pd_shared3p T[[1]] temp (15);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T[[1]] result = declassify(sign(temp));
    T[[1]] control (size(result));
    for(uint i = 0; i < size(control);++i){
        if(vec[i] < 0){
            control[i] = -1;
        }
        if(vec[i] > 0){
            control[i] = 1;
        }
        if(vec[i] == 0){
            control[i] = 0;
        }
    }

    return all(result == control);
}

template<type T,type T2>
bool test_abs(T data, T2 data2){
    pd_shared3p T[[1]] temp (15);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T2[[1]] result = declassify(abs(temp));
    T2[[1]] control (size(result));
    for(uint i = 0; i < size(control);++i){
        if(vec[i] < 0){
            control[i] = (T2)(-vec[i]);
        }
        if(vec[i] >= 0){
            control[i] = (T2)(vec[i]);
        }
    }

    return all(result == control);
}

template<type T>
bool test_sum(T data){
    pd_shared3p T[[1]] temp (10);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T result = declassify(sum(temp));
    T control = 0;
    for(uint i = 0; i < size(vec);++i){
        control += vec[i];
    }

    return control == result;
}


template<type T>
bool test_sum2(T data){
    pd_shared3p T[[1]] temp (10);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T[[1]] result = declassify(sum(temp,2::uint));
    uint startingIndex = 0;
    uint endIndex = size(vec) / 2;
    T[[1]] control (2)= 0;
    for(uint i = 0;i < 2;++i){
        for(uint j = startingIndex;j < endIndex;++j){
            control[i] += vec[j];
        }
        startingIndex = 5;
        endIndex = 10;
    }

    return all(control == result);
}

template<type T>
bool test_product(T data){
    /**
    \todo product does not take 0 element vectors as parameters
    {
        pd_shared3p T[[1]] vec (0);
        pd_shared3p T vec2 = product(vec);
    }*/
    pd_shared3p T[[1]] temp (10);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T result = declassify(product(temp));
    T control = 1;
    for(uint i = 0; i < size(vec);++i){
        control *= vec[i];
    }

    return control == result;
}

template<type T>
bool test_product2(T data){
    pd_shared3p T[[1]] temp (10);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T[[1]] result = declassify(product(temp,2::uint));
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

bool test_any(){
    bool result = true;
    pd_shared3p bool[[1]] vec (6) = {true,false,true,true,false,false};
    pd_shared3p bool[[1]] vec2 (6) = {true,false,false,false,false,false};
    pd_shared3p bool[[1]] vec3 (6) = true;
    pd_shared3p bool[[1]] vec4 (6) = false;
    pd_shared3p bool control = any(vec);
    if(declassify(control) != true){result = false;}

    control = any(vec2);
    if(declassify(control) != true){result = false;}

    control = any(vec3);
    if(declassify(control) != true){result = false;}

    control = any(vec4);
    if(declassify(control) != false){result = false;}

    return result;
}

bool test_all(){
    bool result = true;
    pd_shared3p bool[[1]] vec (6) = {true,false,true,true,false,false};
    pd_shared3p bool[[1]] vec2 (6) = {true,true,true,false,true,true};
    pd_shared3p bool[[1]] vec3 (6) = true;
    pd_shared3p bool[[1]] vec4 (6) = false;
    pd_shared3p bool control = all(vec);
    if(declassify(control) == true){result = false;}

    control = all(vec2);
    if(declassify(control) == true){result = false;}

    control = all(vec3);
    if(declassify(control) != true){result = false;}

    control = all(vec4);
    if(declassify(control) == true){result = false;}

    return result;
}


template<type T>
bool test_min(T data){
    pd_shared3p T[[1]] temp (25);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T result = declassify(min(temp));
    T control = 0;
    for(uint i = 0; i < size(vec);++i){
        if(i == 0){
            control = vec[i];
        }
        else{
            if(vec[i] < control){
                control = vec[i];
            }
        }
    }

    return control == result;
}


template<type T>
bool test_min2(T data){
    pd_shared3p T[[1]] temp (25);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T[[1]] result = declassify(min(temp,5::uint));
    T[[1]] control (5)= 0;
    uint startingIndex = 0;
    uint endIndex = 5;
    for(uint i = 0; i < 5; ++i){
        for(uint j = startingIndex; j < endIndex;++j){
            if(j == startingIndex){
                control[i] = vec[j];
            }
            else{
                if(vec[j] < control[i]){
                    control[i] = vec[j];
                }
            }
        }
        startingIndex += 5;
        endIndex += 5;
    }

    return all(control == result);
}

template<type T>
bool test_min3(T data){
    pd_shared3p T[[1]] temp (10);
    pd_shared3p T[[1]] temp2 (10);
    temp = randomize(temp);
    temp2 = randomize(temp2);
    T[[1]] vec = declassify(temp);
    T[[1]] vec2 = declassify(temp2);
    T[[1]] result = declassify(min(temp,temp2));
    T[[1]] control (10) = 0;
    for(uint i = 0; i < size(vec);++i){
        if(vec[i] <= vec2[i]){
            control[i] = vec[i];
        }
        else{
            control[i] = vec2[i];
        }
    }

    return all(control == result);
}

template<type T>
bool test_max(T data){
    pd_shared3p T[[1]] temp (25);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T result = declassify(max(temp));
    T control = 0;
    for(uint i = 0; i < size(vec);++i){
        if(vec[i] > control){
            control = vec[i];
        }
    }

    return control == result;
}

template<type T>
bool test_max2(T data){
    pd_shared3p T[[1]] temp (25);
    temp = randomize(temp);
    T[[1]] vec = declassify(temp);
    T[[1]] result = declassify(max(temp,5::uint));
    T[[1]] control (5)= 0;
    uint startingIndex = 0;
    uint endIndex = 5;
    for(uint i = 0; i < 5; ++i){
        for(uint j = startingIndex; j < endIndex;++j){
            if(j == startingIndex){
                control[i] = vec[j];
            }
            else{
                if(vec[j] > control[i]){
                    control[i] = vec[j];
                }
            }
        }
        startingIndex += 5;
        endIndex += 5;
    }

    return all(control == result);
}

template<type T>
bool test_max3(T data){
    pd_shared3p T[[1]] temp (10);
    pd_shared3p T[[1]] temp2 (10);
    temp = randomize(temp);
    temp2 = randomize(temp2);
    T[[1]] vec = declassify(temp);
    T[[1]] vec2 = declassify(temp2);
    T[[1]] result = declassify(max(temp,temp2));
    T[[1]] control (10) = 0;
    for(uint i = 0; i < size(vec);++i){
        if(vec[i] >= vec2[i]){
            control[i] = vec[i];
        }
        else{
            control[i] = vec2[i];
        }
    }
    return all(control == result);
}

bool test_floor(){
    //scalar
    pd_shared3p float64[[1]] value = {15.892356329, 5.12974291, 7.5009235790235, -52.325623, -12.5002362, -1.873258};
    float64[[1]] control = {15, 5, 7, -53, -13, -2};
    for(uint i = 0; i < size(value); ++i){
        float64 result = declassify(floor(value[i]));
        if (control[i] != result)
            return false;
    }

    //vector
    float64[[1]] result = declassify(floor(value));
    return all(control == result);
}

bool test_ceiling(){
    //scalar
    pd_shared3p float64[[1]] value = {15.892356329, 5.12974291, 7.5009235790235, -52.325623, -12.5002362, -1.873258};
    float64[[1]] control = {16, 6, 8, -52, -12, -1};
    for(uint i = 0; i < size(value); ++i){
        float64 result = declassify(ceiling(value[i]));
        if (control[i] != result)
            return false;
    }

    //vector
    float64[[1]] result = declassify(ceiling(value));
    return all(control == result);
}

void main(){
// TODO Remove this test? It either works or asserts.
//    print("Classify");
//    {
//        print("uint8");
//        uint8 a = 5; pd_shared3p uint8 b = classify(a);
//        print("SUCCESS!");
//        succeeded_tests = succeeded_tests + 1;
//        all_tests = all_tests +1;
//    }
//    {
//        print("uint16");
//        uint16 a = 5; pd_shared3p uint16 b = classify(a);
//        print("SUCCESS!");
//        succeeded_tests = succeeded_tests + 1;
//        all_tests = all_tests +1;
//    }
//    {
//        print("uint32");
//        uint32 a = 5; pd_shared3p uint32 b = classify(a);
//        print("SUCCESS!");
//        succeeded_tests = succeeded_tests + 1;
//        all_tests = all_tests +1;
//    }
//    {
//        print("uint64/uint");
//        uint a = 5; pd_shared3p uint b = classify(a);
//        print("SUCCESS!");
//        succeeded_tests = succeeded_tests + 1;
//        all_tests = all_tests +1;
//    }
//    {
//        print("int8");
//        int8 a = 5; pd_shared3p int8 b = classify(a);
//        print("SUCCESS!");
//        succeeded_tests = succeeded_tests + 1;
//        all_tests = all_tests +1;
//    }
//    {
//        print("int16");
//        int16 a = 5; pd_shared3p int16 b = classify(a);
//        print("SUCCESS!");
//        succeeded_tests = succeeded_tests + 1;
//        all_tests = all_tests +1;
//    }
//    {
//        print("int32");
//        int32 a = 5; pd_shared3p int32 b = classify(a);
//        print("SUCCESS!");
//        succeeded_tests = succeeded_tests + 1;
//        all_tests = all_tests +1;
//    }
//    {
//        print("int64/int");
//        int a = 5; pd_shared3p int b = classify(a);
//        print("SUCCESS!");
//        succeeded_tests = succeeded_tests + 1;
//        all_tests = all_tests +1;
//    }

    string test_prefix = "Sign";
    test(test_prefix, test_sign(0::int8), 0::int8);
    test(test_prefix, test_sign(0::int16), 0::int16);
    test(test_prefix, test_sign(0::int32), 0::int32);
    test(test_prefix, test_sign(0::int64), 0::int64);

    test_prefix = "Abs";
    test(test_prefix, test_abs(0::int8, 0::uint8), 0::int8);
    test(test_prefix, test_abs(0::int16, 0::uint16), 0::int16);
    test(test_prefix, test_abs(0::int32, 0::uint32), 0::int32);
    test(test_prefix, test_abs(0::int64, 0::uint64), 0::int64);

    test_prefix = "Sum";
    test(test_prefix, test_sum(0::uint8), 0::uint8);
    test(test_prefix, test_sum(0::uint16), 0::uint16);
    test(test_prefix, test_sum(0::uint32), 0::uint32);
    test(test_prefix, test_sum(0::uint64), 0::uint64);
    test(test_prefix, test_sum(0::int8), 0::int8);
    test(test_prefix, test_sum(0::int16), 0::int16);
    test(test_prefix, test_sum(0::int32), 0::int32);
    test(test_prefix, test_sum(0::int64), 0::int64);

    test_prefix = "Sum (2)";
    test(test_prefix, test_sum2(0::uint8), 0::uint8);
    test(test_prefix, test_sum2(0::uint16), 0::uint16);
    test(test_prefix, test_sum2(0::uint32), 0::uint32);
    test(test_prefix, test_sum2(0::uint64), 0::uint64);
    test(test_prefix, test_sum2(0::int8), 0::int8);
    test(test_prefix, test_sum2(0::int16), 0::int16);
    test(test_prefix, test_sum2(0::int32), 0::int32);
    test(test_prefix, test_sum2(0::int64), 0::int64);

    test_prefix = "Product";
    test(test_prefix, test_product(0::uint8), 0::uint8);
    test(test_prefix, test_product(0::uint16), 0::uint16);
    test(test_prefix, test_product(0::uint32), 0::uint32);
    test(test_prefix, test_product(0::uint64), 0::uint64);
    test(test_prefix, test_product(0::int8), 0::int8);
    test(test_prefix, test_product(0::int16), 0::int16);
    test(test_prefix, test_product(0::int32), 0::int32);
    test(test_prefix, test_product(0::int64), 0::int64);

    test_prefix = "Product (2)";
    test(test_prefix, test_product2(0::uint8), 0::uint8);
    test(test_prefix, test_product2(0::uint16), 0::uint16);
    test(test_prefix, test_product2(0::uint32), 0::uint32);
    test(test_prefix, test_product2(0::uint64), 0::uint64);
    test(test_prefix, test_product2(0::int8), 0::int8);
    test(test_prefix, test_product2(0::int16), 0::int16);
    test(test_prefix, test_product2(0::int32), 0::int32);
    test(test_prefix, test_product2(0::int64), 0::int64);

    test_prefix = "Any and All functions";
    test(test_prefix, test_any());
    test(test_prefix, test_all());

    test_prefix = "True Prefix Length";
    {
        bool res = true;
        for (uint i = 0; i < 5; ++i){
            pd_shared3p bool[[1]] arr (10);
            arr = randomize(arr);
            bool[[1]] arr2 = declassify(arr);
            uint result = declassify(truePrefixLength(arr));
            uint control = 0;
            for(uint j = 0; j < size(arr2);++j){
                if(arr2[j]){
                    control += 1;
                }
                else{
                    break;
                }
            }

            if (control != result) {
                res = false;
                break;
            }
        }

        test(test_prefix, res);
    }

    test_prefix = "Min";
    test(test_prefix, test_min(0::uint8), 0::uint8);
    test(test_prefix, test_min(0::uint16), 0::uint16);
    test(test_prefix, test_min(0::uint32), 0::uint32);
    test(test_prefix, test_min(0::uint64), 0::uint64);
    test(test_prefix, test_min(0::int8), 0::int8);
    test(test_prefix, test_min(0::int16), 0::int16);
    test(test_prefix, test_min(0::int32), 0::int32);
    test(test_prefix, test_min(0::int64), 0::int64);

    test_prefix = "Min (2)";
    test(test_prefix, test_min2(0::uint8), 0::uint8);
    test(test_prefix, test_min2(0::uint16), 0::uint16);
    test(test_prefix, test_min2(0::uint32), 0::uint32);
    test(test_prefix, test_min2(0::uint64), 0::uint64);
    test(test_prefix, test_min2(0::int8), 0::int8);
    test(test_prefix, test_min2(0::int16), 0::int16);
    test(test_prefix, test_min2(0::int32), 0::int32);
    test(test_prefix, test_min2(0::int64), 0::int64);

    test_prefix = "Min (3)";
    test(test_prefix, test_min3(0::uint8), 0::uint8);
    test(test_prefix, test_min3(0::uint16), 0::uint16);
    test(test_prefix, test_min3(0::uint32), 0::uint32);
    test(test_prefix, test_min3(0::uint64), 0::uint64);
    test(test_prefix, test_min3(0::int8), 0::int8);
    test(test_prefix, test_min3(0::int16), 0::int16);
    test(test_prefix, test_min3(0::int32), 0::int32);
    test(test_prefix, test_min3(0::int64), 0::int64);

    test_prefix = "Max";
    test(test_prefix, test_max(0::uint8), 0::uint8);
    test(test_prefix, test_max(0::uint16), 0::uint16);
    test(test_prefix, test_max(0::uint32), 0::uint32);
    test(test_prefix, test_max(0::uint64), 0::uint64);
    test(test_prefix, test_max(0::int8), 0::int8);
    test(test_prefix, test_max(0::int16), 0::int16);
    test(test_prefix, test_max(0::int32), 0::int32);
    test(test_prefix, test_max(0::int64), 0::int64);

    test_prefix = "Max (2)";
    test(test_prefix, test_max2(0::uint8), 0::uint8);
    test(test_prefix, test_max2(0::uint16), 0::uint16);
    test(test_prefix, test_max2(0::uint32), 0::uint32);
    test(test_prefix, test_max2(0::uint64), 0::uint64);
    test(test_prefix, test_max2(0::int8), 0::int8);
    test(test_prefix, test_max2(0::int16), 0::int16);
    test(test_prefix, test_max2(0::int32), 0::int32);
    test(test_prefix, test_max2(0::int64), 0::int64);

    test_prefix = "Max (3)";
    test(test_prefix, test_max3(0::uint8), 0::uint8);
    test(test_prefix, test_max3(0::uint16), 0::uint16);
    test(test_prefix, test_max3(0::uint32), 0::uint32);
    test(test_prefix, test_max3(0::uint64), 0::uint64);
    test(test_prefix, test_max3(0::int8), 0::int8);
    test(test_prefix, test_max3(0::int16), 0::int16);
    test(test_prefix, test_max3(0::int32), 0::int32);
    test(test_prefix, test_max3(0::int64), 0::int64);

    // Uncomment when SecreC is updated to support these Syscalls
    test_prefix = "Floor";
    test(test_prefix, test_floor());

    test_prefix = "Ceiling";
    test(test_prefix, test_ceiling());

    test_report();
}

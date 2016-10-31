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
import shared3p_sort;
import test_utility;

domain pd_shared3p shared3p;

public uint repeats = 7; // alter the range of elements to be tested for sorting (min = 4). From function test_sorting()

template<type T, dim N>
bool have_same_elements(T[[N]] input,T[[N]] output){
    T[[1]] vec = flatten(input);
    T[[1]] vec2 = flatten(output);
    uint hits = 0;
    for(uint i = 0; i < size(vec);++i){
        for(uint j = 0; j < size(vec2);++j){
            if(vec[i] == vec2[j]){
                hits += 1;
                break;
            }
        }
    }
    return hits == size(vec);
}

template <domain D : shared3p, type T>
bool test_sorting(D T data){
    for(uint i = 3; i < repeats; ++i){
        D T[[1]] vec (i);
        vec = randomize(vec);
        if (!run_test(vec, declassify(vec)))
            return false;
    }

    return true;
}

template <domain D : shared3p, type T, type U, dim N, dim M>
bool run_test(D T[[N]] vec, U[[M]] u){
    U last;
    U[[N]] vec2 = declassify(sort(vec));
    if(!have_same_elements(declassify(vec),vec2)){
        return false;
    }
    bool result = true;
    for(uint i = 0; i < size(vec);++i){
        if(i != 0){
            if(last > vec2[i]){
                result = false;
                break;
            }
            else{
                last = vec2[i];
            }
        }
        else{
            last = vec2[i];
        }
    }

    return result;
}

template <domain D : shared3p, type T, type U>
bool test_4(D T t, U u){
    D T[[2]] mat (5,5);
    mat = randomize(mat);
    bool result = true;
    U last;
    uint column;
    for(uint i = 0; i < 5; ++i){
        U[[2]] mat2 = declassify(sort(mat,i));
        if(!have_same_elements(declassify(mat),mat2)){
            return false;
        }
        for(uint j = 0; j < 5; ++j){
            if(j != 0){
                if(last > mat2[j,i]){
                    result = false;
                    column = i;
                    break;
                }
                else{
                    last = mat2[j,i];
                }
            }
            else{
                last = mat2[j,i];
            }
        }
        if (!result)
            return false;
    }

    return true;
}

template<domain D: shared3p, type T>
bool sorting_network(D T data){
    for(uint i = 3; i < repeats; ++i){
        bool result = true;
        D T[[1]] vec (i);
        D T last;
        vec = randomize(vec);
        D T[[1]] vec2 = sortingNetworkSort(vec);
        for(uint j = 0; j < size(vec);++j){
            if(j != 0){
                if(declassify(last) > declassify(vec2[j])){
                    result = false;
                    break;
                }
                else{
                    last = vec2[j];
                }
            }
            else{
                last = vec2[j];
            }
        }

        if (!result)
            return false;
    }

    return true;
}

template <domain D : shared3p, type T>
bool sorting_network_matrix(D T data){
    D T[[2]] mat (5,5);
    mat = randomize(mat);
    public bool result = true;
    public T last;
    public uint column;
    for(uint i = 0; i < 5; ++i){
        column = i;
        T[[2]] mat2 = declassify(sortingNetworkSort(mat,i));
        for(uint j = 0; j < 5; ++j){
            if(j != 0){
                if(last > mat2[j,i]){
                    result = false;
                    break;
                }
                else{
                    last = mat2[j,i];
                }
            }
            else{
                last = mat2[j,i];
            }
        }
        if (!result)
            return false;
    }

    return true;
}

template <domain D : shared3p, type T>
bool sorting_network_matrix2(D T data){
    D T[[2]] mat (4,2);
    mat[:,0] = {1,1,0,0};
    mat[:,1] = {1,0,1,0};
    T[[2]] result = declassify(sortingNetworkSort(mat,0::uint,1::uint));
    T[[2]] control (4,2);
    control[:,0] = {0,0,1,1};
    control[:,1] = {0,1,0,1};
    return all(result == control);
}

template <domain D : shared3p, type T>
bool sorting_network_matrix3(D T data){
    D T[[2]] mat (8,3);
    mat[:,0] = {1,1,1,1,0,0,0,0};
    mat[:,1] = {1,1,0,0,1,1,0,0};
    mat[:,2] = {1,0,1,0,1,0,1,0};
    T[[2]] result = declassify(sortingNetworkSort(mat,0::uint,1::uint,2::uint));
    T[[2]] control (8,3);
    control[:,0] = {0,0,0,0,1,1,1,1};
    control[:,1] = {0,0,1,1,0,0,1,1};
    control[:,2] = {0,1,0,1,0,1,0,1};
    return all(result == control);
}

void main() {
    string test_prefix = "1-dimensional 3-8 element vector sorting";
    { pd_shared3p uint8 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p int8 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p int16 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p int32 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p int64 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, test_sorting(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, test_sorting(t), t); }

    // highest bit makes comparison within sorting wrong, to show this i've created TEST 1.b
    test_prefix = "1-dimensional 6 element vector sorting with highest bit always 0";
    {
        // TODO remove this test?
        {
            bool result = true;
            for(uint j = 0; j < 10; ++j){
                pd_shared3p uint8[[1]] vec (6);
                uint8 check = 0b01111111;
                vec = randomize(vec);
                uint8[[1]] vec2 (6) = declassify(vec);
                for(uint i = 0; i < size(vec);++i){
                    while(vec2[i] >= check){
                        vec2[i] -= 1;
                    }
                }
                vec = vec2;
                if (!run_test(vec, 0::uint8)) {
                    result = false;
                    break;
                }
            }
            test(test_prefix, result, 0::uint8);
        }
        {
            bool result = true;
            for(uint j = 0; j < 10; ++j){
                pd_shared3p uint16[[1]] vec (6);
                uint16 check = 0b0111111111111111;
                vec = randomize(vec);
                uint16[[1]] vec2 (6) = declassify(vec);
                for(uint i = 0; i < size(vec);++i){
                    while(vec2[i] >= check){
                        vec2[i] -= 1;
                    }
                }
                vec = vec2;
                if (!run_test(vec, 0::uint16)) {
                    result = false;
                    break;
                }
            }
            test(test_prefix, result, 0::uint16);
        }
    }

    test_prefix = "1-dimensional boolean vector sorting";
    {
        bool result = true;
        for(uint i = 3; i < repeats;++i){
            pd_shared3p bool[[1]] vec (i);
            vec = randomize(vec);
            bool last;
            bool[[1]] vec2 = declassify(sort(vec));
            for(uint j = 0; j < size(vec);++j){
                if(j != 0){
                    if((last == true) && (vec2[j] == false)){
                        result = false;
                        break;
                    }
                    else{
                        last = vec2[j];
                    }
                }
                else{
                    last = vec2[j];
                }
            }

            if (!result)
                break;
        }

        test(test_prefix, result, true);
    }

    test_prefix = "2-dimensional (5,5) boolean matrix sorting by all columns";
    {
        pd_shared3p bool[[2]] mat (5,5) = false;
        mat = randomize(mat);
        bool result = true;
        bool last;
        uint column;
        for(uint i = 0; i < 5; ++i){
            bool[[2]] mat2 = declassify(sort(mat,i));
            for(uint j = 0; j < 5; ++j){
                if(j != 0){
                    if((last == true) && (mat2[j,i] == false)){
                        result = false;
                        column = i;
                        break;
                    }
                    else{
                        last = mat2[j,i];
                    }
                }
                else{
                    last = mat2[j,i];
                }
            }

            if (!result)
                break;
        }

        test(test_prefix, result, true);
    }

    test_prefix = "2-dimensional (5,5) matrix sorting by all columns";
    { pd_shared3p uint8 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p uint16 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p uint32 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p uint64 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p int8 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p int16 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p int32 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p int64 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, test_4(t, declassify(t)), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, test_4(t, declassify(t)), t); }

    test_prefix = "Sorting network sort on vectors";
    { pd_shared3p uint8 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p int8 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p int16 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p int32 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p int64 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, sorting_network(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, sorting_network(t), t); }

    test_prefix = "sorting network sort on matrices";
    { pd_shared3p uint8 t; test(test_prefix, sorting_network_matrix(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, sorting_network_matrix(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, sorting_network_matrix(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, sorting_network_matrix(t), t); }
    { pd_shared3p int8 t; test(test_prefix, sorting_network_matrix(t), t); }
    { pd_shared3p int16 t; test(test_prefix, sorting_network_matrix(t), t); }
    { pd_shared3p int32 t; test(test_prefix, sorting_network_matrix(t), t); }
    { pd_shared3p int64 t; test(test_prefix, sorting_network_matrix(t), t); }

    test_prefix = "Sorting network sort on matrices(2)";
    { pd_shared3p uint8 t; test(test_prefix, sorting_network_matrix2(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, sorting_network_matrix2(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, sorting_network_matrix2(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, sorting_network_matrix2(t), t); }
    { pd_shared3p int8 t; test(test_prefix, sorting_network_matrix2(t), t); }
    { pd_shared3p int16 t; test(test_prefix, sorting_network_matrix2(t), t); }
    { pd_shared3p int32 t; test(test_prefix, sorting_network_matrix2(t), t); }
    { pd_shared3p int64 t; test(test_prefix, sorting_network_matrix2(t), t); }

    test_prefix = "Sorting network sort on matrices(3)";
    { pd_shared3p uint8 t; test(test_prefix, sorting_network_matrix3(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, sorting_network_matrix3(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, sorting_network_matrix3(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, sorting_network_matrix3(t), t); }
    { pd_shared3p int8 t; test(test_prefix, sorting_network_matrix3(t), t); }
    { pd_shared3p int16 t; test(test_prefix, sorting_network_matrix3(t), t); }
    { pd_shared3p int32 t; test(test_prefix, sorting_network_matrix3(t), t); }
    { pd_shared3p int64 t; test(test_prefix, sorting_network_matrix3(t), t); }

    test_report();
}

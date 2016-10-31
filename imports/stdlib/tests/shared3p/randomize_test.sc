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

uint8 uintMax(uint8 x) { return UINT8_MAX; }
uint16 uintMax(uint16 x) { return UINT16_MAX; }
uint32 uintMax(uint32 x) { return UINT32_MAX; }
uint64 uintMax(uint64 x) { return UINT64_MAX; }


/*
 * This is mainly designed to have few sanity checks on the random number
 * generator. For this reason we are not currently testing XOR types or signed
 * types.
 */


template<domain D:shared3p,type T>
bool randomize_empty (D T dummy_) {
    D T[[1]] empty;
    empty = randomize(empty);
    return size(empty) == 0;
}

template<domain D:shared3p,type T>
bool randomize_single (D T dummy_) {
    D T scalar;

    uint n = 80; // 2^-80

    // Must be able to eventually generate an even number.
    for (uint i = 0; true; ++ i) {
        scalar = randomize(scalar);
        if (declassify(scalar) % 2 == 0) return true;
        if (i >= n) return false;
    }

    // Must be able to eventually generate an odd number.
    for (uint i = 0; true; ++ i) {
        scalar = randomize(scalar);
        if (declassify(scalar) % 2 == 1) return true;
        if (i >= n) return false;
    }

    // Must be able to eventually generate a small(ish) number.
    for (uint i = 0; true; ++ i) {
        scalar = randomize(scalar);
        if (declassify(scalar) < uintMax(0 :: T) / 2) return true;
        if (i >= n) return false;
    }

    // Must be able to eventually generate a big number.
    for (uint i = 0; true; ++ i) {
        scalar = randomize(scalar);
        if (declassify(scalar) > uintMax(0 :: T) / 2) return true;
        if (i >= n) return false;
    }

    return false;
}

template<domain D : shared3p,type T>
bool randomize_few (D T dummy_, uint n) {
    D T[[1]] vec (n);

    assert (n <= 10000);

    uint n = 80; // 2^-80

    // Must be able to generate even numbers.
    for (uint i = 0; true; ++ i) {
        vec = randomize(vec);
        if (any (declassify(vec) % 2 == 0)) return true;
        if (i >= n) return false;
    }

    // Must be able to generate odd numbers.
    for (uint i = 0; true; ++ i) {
        vec = randomize(vec);
        if (any (declassify(vec) % 2 == 1)) return true;
        if (i >= n) return false;
    }

    // Must be able to generate small numbers.
    for (uint i = 0; true; ++ i) {
        vec = randomize(vec);
        if (any (declassify(vec) < uintMax(0 :: T) / 2)) return true;
        if (i >= n) return false;
    }

    // Must be able to generate big numbers.
    for (uint i = 0; true; ++ i) {
        vec = randomize(vec);
        if (any (declassify(vec) > uintMax(0 :: T) / 2)) return true;
        if (i >= n) return false;
    }

    // Must eventually get all non-zero numbers.
    for (uint i = 0; true; ++ i) {
        vec = randomize(vec);
        if (all (declassify(vec) != 0)) return true;
        if (i >= n) return false;
    }

    // Must eventually get all non-one numbers.
    for (uint i = 0; true; ++ i) {
        vec = randomize(vec);
        if (all (declassify(vec) != 1)) return true;
        if (i >= n) return false;
    }

    // Must eventually get all non-maximum numbers.
    for (uint i = 0; true; ++ i) {
        vec = randomize(vec);
        if (all (declassify(vec) != uintMax(0 :: T))) return true;
        if (i >= n) return false;
    }

    return false;
}

template<domain D : shared3p,type T>
bool randomize_many(D T dummy_, uint n) {
    D T[[1]] vec (n);

    assert(n >= 5000);

    // For a proper RNG the limit gives us failure probability of less than
    // 2^-80 for n >= 5000.
    uint limit = n / 3;

    // Test if we have sufficiently many:
    //  odds, evens, big values, small values
    // Feel free to extend with predicates that roughly hold on half of the
    // domain.
    T[[1]] pubVec = declassify (randomize (vec));
    if (sum (pubVec % 2 == 0) < limit) return false;
    if (sum (pubVec % 2 == 1) < limit) return false;
    if (sum (pubVec < uintMax(0 :: T)/2) < limit) return false;
    if (sum (pubVec > uintMax(0 :: T)/2) < limit) return false;

    return true;
}

void main(){
    string test_prefix = "Randomize on empty vector";
    { pd_shared3p uint8 t; test(test_prefix, randomize_empty(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, randomize_empty(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, randomize_empty(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, randomize_empty(t), t); }

    test_prefix = "Randomize on a single value";
    { pd_shared3p uint8 t; test(test_prefix, randomize_single(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, randomize_single(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, randomize_single(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, randomize_single(t), t); }

    test_prefix = "Randomize on 10 values";
    { pd_shared3p uint8 t; test(test_prefix, randomize_few(t, 10 :: uint), t); }
    { pd_shared3p uint16 t; test(test_prefix, randomize_few(t, 10 :: uint), t); }
    { pd_shared3p uint32 t; test(test_prefix, randomize_few(t, 10 :: uint), t); }
    { pd_shared3p uint64 t; test(test_prefix, randomize_few(t, 10 :: uint), t); }

    test_prefix = "Randomize on 1k values";
    { pd_shared3p uint8 t; test(test_prefix, randomize_few(t, 1000 :: uint), t); }
    { pd_shared3p uint16 t; test(test_prefix, randomize_few(t, 1000 :: uint), t); }
    { pd_shared3p uint32 t; test(test_prefix, randomize_few(t, 1000 :: uint), t); }
    { pd_shared3p uint64 t; test(test_prefix, randomize_few(t, 1000 :: uint), t); }

    test_prefix = "Randomize on 5k values";
    { pd_shared3p uint8 t; test(test_prefix, randomize_many(t, 5000 :: uint), t); }
    { pd_shared3p uint16 t; test(test_prefix, randomize_many(t, 5000 :: uint), t); }
    { pd_shared3p uint32 t; test(test_prefix, randomize_many(t, 5000 :: uint), t); }
    { pd_shared3p uint64 t; test(test_prefix, randomize_many(t, 5000 :: uint), t); }

    test_prefix = "Randomize on 10k values";
    { pd_shared3p uint8 t; test(test_prefix, randomize_many(t, 100000 :: uint), t); }
    { pd_shared3p uint16 t; test(test_prefix, randomize_many(t, 100000 :: uint), t); }
    { pd_shared3p uint32 t; test(test_prefix, randomize_many(t, 100000 :: uint), t); }
    { pd_shared3p uint64 t; test(test_prefix, randomize_many(t, 100000 :: uint), t); }

    test_report();
}

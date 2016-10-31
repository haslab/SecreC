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

uint32 random_tests = 10;

template <type T>
bool test_classification(T value){
    public T a; a = value;
    pd_shared3p T b; b = a;
    a = declassify(b);
    return a == value;
}

template<domain D : shared3p ,type T, type T2>
bool test_classification_xor(D T priv, T2 pub){
    return declassify(priv) == pub;
}

//template <type T>
//void test_0a(T pub){
//    pd_shared3p T priv;
//    priv = pub;
//    succeeded_tests = succeeded_tests + 1;
//    all_tests = all_tests +1;
//    print("SUCCESS!");
//}
//
//template <domain D : shared3p, type T>
//void test_0b(D T priv){
//    public T pub;
//    pub = declassify(priv);
//    succeeded_tests = succeeded_tests + 1;
//    all_tests = all_tests +1;
//    print("SUCCESS!");
//}

template <type T>
bool rand_test(T pub, uint32 nr) {
    public bool result = true;
    for (public uint32 i = 0; i < nr; ++i){
        pd_shared3p T[[1]] a (1);
        a = randomize(a);
        pd_shared3p T priv = a[0];
        result &= test_classification(declassify(priv));
    }

    return result;
}

void main() {
//    string test_prefix = "PUBLIC -> PRIVATE conversions throws no errors";
//    {
//        public bool pub = true;
//        test_0a(pub);
//    }
//    {
//        public uint8 pub = 1;
//        test_0a(pub);
//    }
//    {
//        public uint16 pub = 1;
//        test_0a(pub);
//    }
//    {
//        public uint32 pub = 1;
//        test_0a(pub);
//    }
//    {
//        public uint pub = 1;
//        test_0a(pub);
//    }
//    {
//        public int8 pub = 1;
//        test_0a(pub);
//    }
//    {
//        public int16 pub = 1;
//        test_0a(pub);
//    }
//    {
//        public int32 pub = 1;
//        test_0a(pub);
//    }
//    {
//        public int pub = 1;
//        test_0a(pub);
//    }
//    test_prefix = "PRIVATE -> PUBLIC conversion throws no errors";
//    {
//        pd_shared3p bool priv = false;
//        test_0b(priv);
//    }
//    {
//        pd_shared3p uint8 priv = 0;
//        test_0b(priv);
//    }
//    {
//        pd_shared3p uint16 priv = 0;
//        test_0b(priv);
//    }
//    {
//        pd_shared3p uint32 priv = 0;
//        test_0b(priv);
//    }
//    {
//        pd_shared3p uint priv = 0;
//        test_0b(priv);
//    }
//    {
//        pd_shared3p int8 priv = 0;
//        test_0b(priv);
//    }
//    {
//        pd_shared3p int16 priv = 0;
//        test_0b(priv);
//    }
//    {
//        pd_shared3p int32 priv = 0;
//        test_0b(priv);
//    }
//    {
//        pd_shared3p int priv = 0;
//        test_0b(priv);
//    }

    string test_prefix = "PUBLIC -> PRIVATE -> PUBLIC conversion with (0)";
    test(test_prefix, test_classification(false), true);
    test(test_prefix, test_classification(0::uint8), 0::uint8);
    test(test_prefix, test_classification(0::uint16), 0::uint16);
    test(test_prefix, test_classification(0::uint32), 0::uint32);
    test(test_prefix, test_classification(0::uint64), 0::uint64);
    test(test_prefix, test_classification(0::int8), 0::int8);
    test(test_prefix, test_classification(0::int16), 0::int16);
    test(test_prefix, test_classification(0::int32), 0::int32);
    test(test_prefix, test_classification(0::int64), 0::int64);
    { pd_shared3p xor_uint8 t = 0; test(test_prefix, test_classification_xor(t, 0::uint8), 0::uint8); }
    { pd_shared3p xor_uint16 t = 0; test(test_prefix, test_classification_xor(t, 0::uint16), 0::uint16); }
    { pd_shared3p xor_uint32 t = 0; test(test_prefix, test_classification_xor(t, 0::uint32), 0::uint32); }
    { pd_shared3p xor_uint64 t = 0; test(test_prefix, test_classification_xor(t, 0::uint64), 0::uint64); }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC conversion with (1)";
    test(test_prefix, test_classification(false), true);
    test(test_prefix, test_classification(1::uint8), 0::uint8);
    test(test_prefix, test_classification(1::uint16), 0::uint16);
    test(test_prefix, test_classification(1::uint32), 0::uint32);
    test(test_prefix, test_classification(1::uint64), 0::uint64);
    test(test_prefix, test_classification(1::int8), 0::int8);
    test(test_prefix, test_classification(1::int16), 0::int16);
    test(test_prefix, test_classification(1::int32), 0::int32);
    test(test_prefix, test_classification(1::int64), 0::int64);
    { pd_shared3p xor_uint8 t = 1; test(test_prefix, test_classification_xor(t, 1::uint8), 0::uint8); }
    { pd_shared3p xor_uint16 t = 1; test(test_prefix, test_classification_xor(t, 1::uint16), 0::uint16); }
    { pd_shared3p xor_uint32 t = 1; test(test_prefix, test_classification_xor(t, 1::uint32), 0::uint32); }
    { pd_shared3p xor_uint64 t = 1; test(test_prefix, test_classification_xor(t, 1::uint64), 0::uint64); }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC conversion with (-1)";
    test(test_prefix, test_classification(-1::int8), 0::int8);
    test(test_prefix, test_classification(-1::int16), 0::int16);
    test(test_prefix, test_classification(-1::int32), 0::int32);
    test(test_prefix, test_classification(-1::int64), 0::int64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC with MAX-1 values";
    test(test_prefix, test_classification(UINT8_MAX-1), 0::uint8);;
    test(test_prefix, test_classification(UINT16_MAX-1), 0::uint16);;
    test(test_prefix, test_classification(UINT32_MAX-1), 0::uint32);;
    test(test_prefix, test_classification(UINT64_MAX-1), 0::uint64);;
    test(test_prefix, test_classification(INT8_MAX-1), 0::int8);;
    test(test_prefix, test_classification(INT16_MAX-1), 0::int16);;
    test(test_prefix, test_classification(INT32_MAX-1), 0::int32);;
    test(test_prefix, test_classification(INT64_MAX-1), 0::int64);;
    { pd_shared3p xor_uint8 t = UINT8_MAX-1; test(test_prefix, test_classification_xor(t, UINT8_MAX-1), 0::uint8); }
    { pd_shared3p xor_uint16 t = UINT16_MAX-1; test(test_prefix, test_classification_xor(t, UINT16_MAX-1), 0::uint16); }
    { pd_shared3p xor_uint32 t = UINT32_MAX-1; test(test_prefix, test_classification_xor(t, UINT32_MAX-1), 0::uint32); }
    { pd_shared3p xor_uint64 t = UINT64_MAX-1; test(test_prefix, test_classification_xor(t, UINT64_MAX-1), 0::uint64); }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC with MAX values";
    test(test_prefix, test_classification(UINT8_MAX), 0::uint8);;
    test(test_prefix, test_classification(UINT16_MAX), 0::uint16);;
    test(test_prefix, test_classification(UINT32_MAX), 0::uint32);;
    test(test_prefix, test_classification(UINT64_MAX), 0::uint64);;
    test(test_prefix, test_classification(INT8_MAX), 0::int8);;
    test(test_prefix, test_classification(INT16_MAX), 0::int16);;
    test(test_prefix, test_classification(INT32_MAX), 0::int32);;
    test(test_prefix, test_classification(INT64_MAX), 0::int64);;
    { pd_shared3p xor_uint8 t = UINT8_MAX; test(test_prefix, test_classification_xor(t, UINT8_MAX), 0::uint8); }
    { pd_shared3p xor_uint16 t = UINT16_MAX; test(test_prefix, test_classification_xor(t, UINT16_MAX), 0::uint16); }
    { pd_shared3p xor_uint32 t = UINT32_MAX; test(test_prefix, test_classification_xor(t, UINT32_MAX), 0::uint32); }
    { pd_shared3p xor_uint64 t = UINT64_MAX; test(test_prefix, test_classification_xor(t, UINT64_MAX), 0::uint64); }

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC with MIN+1 values";
    test(test_prefix, test_classification(INT8_MIN+1), 0::int8);
    test(test_prefix, test_classification(INT16_MIN+1), 0::int16);
    test(test_prefix, test_classification(INT32_MIN+1), 0::int32);
    test(test_prefix, test_classification(INT64_MIN+1), 0::int64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC with MIN values";
    test(test_prefix, test_classification(INT8_MIN), 0::int8);
    test(test_prefix, test_classification(INT16_MIN), 0::int16);
    test(test_prefix, test_classification(INT32_MIN), 0::int32);
    test(test_prefix, test_classification(INT64_MIN), 0::int64);

    test_prefix = "PUBLIC -> PRIVATE -> PUBLIC with " + tostring(random_tests) + " random values";
    test(test_prefix, rand_test(0::uint8, random_tests), 0::uint8);
    test(test_prefix, rand_test(0::uint16, random_tests), 0::uint16);
    test(test_prefix, rand_test(0::uint32, random_tests), 0::uint32);
    test(test_prefix, rand_test(0::uint64, random_tests), 0::uint64);
    test(test_prefix, rand_test(0::int8, random_tests), 0::int8);
    test(test_prefix, rand_test(0::int16, random_tests), 0::int16);
    test(test_prefix, rand_test(0::int32, random_tests), 0::int32);
    test(test_prefix, rand_test(0::int64, random_tests), 0::int64);

    test_report();
}

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
import test_utility;
import test_utility_random;

template<type T>
bool neg_values(T data) {
    bool [[1]] result(2);
    T a;
    T[[1]] b (5);
    a = randomize(a); b = randomize(b);
    T c = -a;
    result[0] = (a + c) == 0;

    T[[1]] d (5) = -b;
    c = -a;
    result[1] = all((b + d) == 0);

    return all(result);
}

template<type T>
bool neg_values_float(T data) {
    bool [[1]] result(2);
    T a;
    T[[1]] b (5);
    a = random_float(0::T); b = randomize(b);
    T c = -a;
    result[0] = (a + c) == 0;

    T[[1]] d (5) = -b;
    c = -a;
    result[1] = all((b + d) == 0);

    return all(result);
}

template<type T>
bool cast_bool_to_type(T data) {
    //public
    bool result = true;
    bool[[1]] temp (5);
    bool[[1]] a = randomize(temp);
    T[[1]] b (5) = (T)a;
    for (uint i = 0; i < 5; ++i) {
        if (a[i] == true && b[i] == 0) {
            result = false;
        }
        if (a[i] == false && b[i] == 1) {
            result = false;
        }
    }

    return result;
}

template<type T>
bool cast_type_to_bool(T data) {
    // public
    bool result = true;
    T[[1]] temp (10);
    T[[1]] a = randomize(temp);
    a[0] = 0;
    a[1] = 1;
    a[2] = -1;
    
    bool[[1]] b (10) = (bool)a;

    for (uint i = 0; i < 10; ++i) {
        if (b[i] == true && a[i] == 0) {
            result = false;
        }
        if (b[i] == false && a[i] != 0) {
            result = false;
        }
    }

    return result;
}

template<type T, type U, dim N>
bool cast_type_to_type(T [[N]] t, U [[N]] u) {
    U[[1]] c = (U)(t);
    return all(c == u);
}

void main() {
    string test_prefix = "Negating values";
    test(test_prefix, neg_values(0::uint8), 0::uint8);
    test(test_prefix, neg_values(0::uint16), 0::uint16);
    test(test_prefix, neg_values(0::uint32), 0::uint32);
    test(test_prefix, neg_values(0::uint64), 0::uint64);
    test(test_prefix, neg_values(0::int8), 0::int8);
    test(test_prefix, neg_values(0::int16), 0::int16);
    test(test_prefix, neg_values(0::int32), 0::int32);
    test(test_prefix, neg_values(0::int64), 0::int64);
    test(test_prefix, neg_values_float(0::float32), 0::float32);
    test(test_prefix, neg_values_float(0::float64), 0::float64);

    test_prefix = "Casting values";
    test(test_prefix, cast_bool_to_type(0::uint8), true, 0::uint8);
    test(test_prefix, cast_bool_to_type(0::uint16), true, 0::uint16);
    test(test_prefix, cast_bool_to_type(0::uint32), true, 0::uint32);
    test(test_prefix, cast_bool_to_type(0::uint64), true, 0::uint64);
    test(test_prefix, cast_bool_to_type(0::int8), true, 0::int8);
    test(test_prefix, cast_bool_to_type(0::int16), true, 0::int16);
    test(test_prefix, cast_bool_to_type(0::int32), true, 0::int32);
    test(test_prefix, cast_bool_to_type(0::int64), true, 0::int64);
    test(test_prefix, cast_bool_to_type(0::float32), true, 0::float32);
    test(test_prefix, cast_bool_to_type(0::float64), true, 0::float64);
    test(test_prefix, cast_type_to_bool(0::uint8), 0::uint8, true);
    test(test_prefix, cast_type_to_bool(0::uint16), 0::uint16, true);
    test(test_prefix, cast_type_to_bool(0::uint32), 0::uint32, true);
    test(test_prefix, cast_type_to_bool(0::uint64), 0::uint64, true);
    test(test_prefix, cast_type_to_bool(0::int8), 0::int8, true);
    test(test_prefix, cast_type_to_bool(0::int16), 0::int16, true);
    test(test_prefix, cast_type_to_bool(0::int32), 0::int32, true);
    test(test_prefix, cast_type_to_bool(0::int64), 0::int64, true);
    // TODO
//    test(test_prefix, cast_type_to_bool(0::float32), 0::float32, true);
//    test(test_prefix, cast_type_to_bool(0::float64), 0::float64, true);

    {
        uint8[[1]] a = {0, 100, 200, 255};
        {
            uint16[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), 0::uint8, 0::uint32);
        }
        {
            uint32[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), 0::uint8, 0::uint32);
        }
        {
            uint64[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), 0::uint8, 0::uint64);
        }
        {
            int8[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), 0::uint8, 0::int8);
        }
        {
            int16[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), 0::uint8, 0::int16);
        }
        {
            int32[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), 0::uint8, 0::int32);
        }
        {
            int64[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), 0::uint8, 0::int64);
        }
        {
            float32[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), 0::uint8, 0::float32);
        }
        {
            float64[[1]] b = {0, 100, 200, 255};
            test(test_prefix, cast_type_to_type(a, b), 0::uint8, 0::float64);
        }
    }
    {
        uint16[[1]] a = {0,15385,38574,65535};
        {
            uint8[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), 0::uint16, 0::uint8);
        }
        {
            uint32[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), 0::uint16, 0::uint32);
        }
        {
            uint64[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), 0::uint16, 0::uint64);
        }
        {
            int8[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), 0::uint16, 0::int8);
        }
        {
            int16[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), 0::uint16, 0::int16);
        }
        {
            int32[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), 0::uint16, 0::int32);
        }
        {
            int64[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), 0::uint16, 0::int64);
        }
        {
            float32[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), 0::uint16, 0::float32);
        }
        {
            float64[[1]] b = {0,15385,38574,65535};
            test(test_prefix, cast_type_to_type(a, b), 0::uint16, 0::float64);
        }
    }
    {
        uint32[[1]] a = {0,21424,21525341,4294967295};
        {
            uint8[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), 0::uint32, 0::uint8);
        }
        {
            uint16[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), 0::uint32, 0::uint16);
        }
        {
            uint64[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), 0::uint32, 0::uint64);
        }
        {
            int8[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), 0::uint32, 0::int8);
        }
        {
            int16[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), 0::uint32, 0::int16);
        }
        {
            int32[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), 0::uint32, 0::int32);
        }
        {
            int64[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), 0::uint32, 0::int64);
        }
        {
            float32[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), 0::uint32, 0::float32);
        }
        {
            float64[[1]] b = {0,21424,21525341,4294967295};
            test(test_prefix, cast_type_to_type(a, b), 0::uint32, 0::float64);
        }
    }
    {
        uint64[[1]] a = {0,55161532,142234215413552,18446744073709551615};
        {
            uint8[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), 0::uint64, 0::uint8);
        }
        {
            uint16[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), 0::uint64, 0::uint16);
        }
        {
            uint32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), 0::uint64, 0::uint32);
        }
        {
            int8[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), 0::uint64, 0::int8);
        }
        {
            int16[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), 0::uint64, 0::int16);
        }
        {
            int32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), 0::uint64, 0::int32);
        }
        {
            int64[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), 0::uint64, 0::int64);
        }
        {
            float32[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), 0::uint64, 0::float32);
        }
        {
            float64[[1]] b = {0,55161532,142234215413552,18446744073709551615};
            test(test_prefix, cast_type_to_type(a, b), 0::uint64, 0::float64);
        }
    }
    {
        int8[[1]] a = {-128,-40,40,127};
        {
            uint8[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), 0::int8, 0::uint8);
        }
        {
            uint16[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), 0::int8, 0::uint16);
        }
        {
            uint32[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), 0::int8, 0::uint32);
        }
        {
            uint64[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), 0::int8, 0::uint64);
        }
        {
            int16[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), 0::int8, 0::int16);
        }
        {
            int32[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), 0::int8, 0::int32);
        }
        {
            int64[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), 0::int8, 0::int64);
        }
        {
            float32[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), 0::int8, 0::float32);
        }
        {
            float64[[1]] b = {-128,-40,40,127};
            test(test_prefix, cast_type_to_type(a, b), 0::int8, 0::float64);
        }
    }
    {
        int16[[1]] a = {-32768,-16325,12435,32767};
        {
            uint8[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), 0::int16, 0::uint8);
        }
        {
            uint16[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), 0::int16, 0::uint16);
        }
        {
            uint32[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), 0::int16, 0::uint32);
        }
        {
            uint64[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), 0::int16, 0::uint64);
        }
        {
            int8[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), 0::int16, 0::int8);
        }
        {
            int32[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), 0::int16, 0::int32);
        }
        {
            int64[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), 0::int16, 0::int64);
        }
        {
            float32[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), 0::int16, 0::float32);
        }
        {
            float64[[1]] b = {-32768,-16325,12435,32767};
            test(test_prefix, cast_type_to_type(a, b), 0::int16, 0::float64);
        }
    }
    {
        int32[[1]] a = {-2147483648,-483648,2147483,2147483647};
        {
            uint8[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), 0::int32, 0::uint8);
        }
        {
            uint16[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), 0::int32, 0::uint16);
        }
        {
            uint32[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), 0::int32, 0::uint32);
        }
        {
            uint64[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), 0::int32, 0::uint64);
        }
        {
            int8[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), 0::int32, 0::int8);
        }
        {
            int16[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), 0::int32, 0::int16);
        }
        {
            int64[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), 0::int32, 0::int64);
        }
        {
            float32[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), 0::int32, 0::float32);
        }
        {
            float64[[1]] b = {-2147483648,-483648,2147483,2147483647};
            test(test_prefix, cast_type_to_type(a, b), 0::int32, 0::float64);
        }
    }
    {
        int64[[1]] a = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
        {
            uint8[[1]] b =  {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), 0::int64, 0::uint8);
        }
        {
            uint16[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), 0::int64, 0::uint16);
        }
        {
            uint32[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), 0::int64, 0::uint32);
        }
        {
            uint64[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), 0::int64, 0::uint64);
        }
        {
            int8[[1]] b =  {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), 0::int64, 0::int8);
        }
        {
            int16[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), 0::int64, 0::int16);
        }
        {
            int32[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), 0::int64, 0::int32);
        }
        {
            float32[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), 0::int64, 0::float32);
        }
        {
            float64[[1]] b = {-9223372036854775808,-7036854775808,9223372036854,9223372036854775807};
            test(test_prefix, cast_type_to_type(a, b), 0::int64, 0::float64);
        }
    }
    {
        float32[[1]] a = {-3.40282e+38,0.0,1.17549e-38,1.0,3.40282e+38};
        {
            uint8[[1]] b = {UINT8_MIN,0,0,1,UINT8_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float32, 0::uint8);
        }
        {
            uint16[[1]] b = {UINT16_MIN,0,0,1,UINT16_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float32, 0::uint16);
        }
        {
            uint32[[1]] b = {UINT32_MIN,0,0,1,UINT32_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float32, 0::uint32);
        }
        {
            uint64[[1]] b = {UINT64_MIN,0,0,1,UINT64_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float32, 0::uint64);
        }
        {
            int8[[1]] b = {INT8_MIN,0,0,1,INT8_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float32, 0::int8);
        }
        {
            int16[[1]] b = {INT16_MIN,0,0,1,INT16_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float32, 0::int16);
        }
        {
            int32[[1]] b = {INT32_MIN,0,0,1,INT32_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float32, 0::int32);
        }
        {
            int64[[1]] b = {INT64_MIN,0,0,1,INT64_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float32, 0::int64);
        }
        {
            float64[[1]] b = {-3.40282e+38,0,1.17549e-38,1,3.40282e+38};
            test(test_prefix, cast_type_to_type(a, b), 0::float32, 0::float64);
        }
    }
    {
        float64[[1]] a = {-1.79769e+308,0.0,2.22507e-308,1.0,1.79769e+308};
        {
            uint8[[1]] b = {UINT8_MIN,0,0,1,UINT8_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float64, 0::uint8);
        }
        {
            uint16[[1]] b = {UINT16_MIN,0,0,1,UINT16_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float64, 0::uint16);
        }
        {
            uint32[[1]] b = {UINT32_MIN,0,0,1,UINT32_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float64, 0::uint32);
        }
        {
            uint64[[1]] b = {UINT64_MIN,0,0,1,UINT64_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float64, 0::uint64);
        }
        {
            int8[[1]] b = {INT8_MIN,0,0,1,INT8_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float64, 0::int8);
        }
        {
            int16[[1]] b = {INT16_MIN,0,0,1,INT16_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float64, 0::int16);
        }
        {
            int32[[1]] b = {INT32_MIN,0,0,1,INT32_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float64, 0::int32);
        }
        {
            int64[[1]] b = {INT64_MIN,0,0,1,INT64_MAX};
            //test(test_prefix, cast_type_to_type(a, b), 0::float64, 0::int64);
        }
        {
            float32[[1]] b = {-1.79769e+308,0.0,2.22507e-308,1.0,1.79769e+308};
            test(test_prefix, cast_type_to_type(a, b), 0::float64, 0::float32);
        }
    }

    test_report();
}

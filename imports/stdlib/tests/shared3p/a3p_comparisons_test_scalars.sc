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

template<domain D, type T>
bool eq(D T t) {
    D T a = 0, b = 1;
    bool [[1]] result = {
        declassify(a == a),
        !declassify(a == b),
        !declassify(b == a),
        declassify(b == b)
    };

    return all(result);
}

template<domain D>
bool eq(D bool t) {
    D bool a = false, b = true;
    bool [[1]] result = {
        declassify(a == a),
        !declassify(a == b),
        !declassify(b == a),
        declassify(b == b)
    };

    return all(result);
}

template<domain D, type T>
bool gt(D T t) {
    D T a = 0, b = 1;
    bool [[1]] result = {
        !declassify(a > a),
        !declassify(a > b),
        declassify(b > a),
        !declassify(b > b)
    };

    return all(result);
}

template<domain D>
bool gt(D bool t) {
    D bool a = false, b = true;
    bool [[1]] result = {
        !declassify(a > a),
        !declassify(a > b),
        declassify(b > a),
        !declassify(b > b)
    };

    return all(result);
}

template<domain D, type T>
bool gt_or_eq(D T t) {
    D T a = 0, b = 1;
    bool [[1]] result = {
        declassify(a >= a),
        !declassify(a >= b),
        declassify(b >= a),
        declassify(b >= b)
    };

    return all(result);
}

template<domain D>
bool gt_or_eq(D bool t) {
    D bool a = false, b = true;
    bool [[1]] result = {
        declassify(a >= a),
        !declassify(a >= b),
        declassify(b >= a),
        declassify(b >= b)
    };

    return all(result);
}

template<domain D, type T>
bool lt(D T t) {
    D T a = 0, b = 1;
    bool [[1]] result = {
        !declassify(a < a),
        declassify(a < b),
        !declassify(b < a),
        !declassify(b < b)
    };

    return all(result);
}

template<domain D>
bool lt(D bool t) {
    D bool a = false, b = true;
    bool [[1]] result = {
        !declassify(a < a),
        declassify(a < b),
        !declassify(b < a),
        !declassify(b < b)
    };

    return all(result);
}

template<domain D, type T>
bool lt_or_eq(D T t) {
    D T a = 0, b = 1;
    bool [[1]] result = {
        declassify(a <= a),
        declassify(a <= b),
        !declassify(b <= a),
        declassify(b <= b)
    };

    return all(result);
}

template<domain D>
bool lt_or_eq(D bool t) {
    D bool a = false, b = true;
    bool [[1]] result = {
        declassify(a <= a),
        declassify(a <= b),
        !declassify(b <= a),
        declassify(b <= b)
    };

    return all(result);
}

template<domain D, type T>
bool ne(D T t) {
    D T a = 0, b = 1;
    bool [[1]] result = {
        !declassify(a != a),
        declassify(a != b),
        declassify(b != a),
        !declassify(b != b)
    };

    return all(result);
}

template<domain D>
bool ne(D bool t) {
    D bool a = false, b = true;
    bool [[1]] result = {
        !declassify(a != a),
        declassify(a != b),
        declassify(b != a),
        !declassify(b != b)
    };

    return all(result);
}

void main(){
    string test_prefix = "Operator >";
//    { pd_shared3p bool t; test(test_prefix, gt(t), t); }
    { pd_shared3p bool t; test(test_prefix, false, t); }
    { pd_shared3p uint8 t; test(test_prefix, gt(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, gt(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, gt(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, gt(t), t); }
    { pd_shared3p int8 t; test(test_prefix, gt(t), t); }
    { pd_shared3p int16 t; test(test_prefix, gt(t), t); }
    { pd_shared3p int32 t; test(test_prefix, gt(t), t); }
    { pd_shared3p int64 t; test(test_prefix, gt(t), t); }
    { pd_shared3p float32 t; test(test_prefix, gt(t), t); }
    { pd_shared3p float64 t; test(test_prefix, gt(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, gt(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, gt(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, gt(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, gt(t), t); }

    test_prefix = "Operator <";
//    { pd_shared3p bool t; test(test_prefix, lt(t), t); }
    { pd_shared3p bool t; test(test_prefix, false, t); }
    { pd_shared3p uint8 t; test(test_prefix, lt(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, lt(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, lt(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, lt(t), t); }
    { pd_shared3p int8 t; test(test_prefix, lt(t), t); }
    { pd_shared3p int16 t; test(test_prefix, lt(t), t); }
    { pd_shared3p int32 t; test(test_prefix, lt(t), t); }
    { pd_shared3p int64 t; test(test_prefix, lt(t), t); }
    { pd_shared3p float32 t; test(test_prefix, lt(t), t); }
    { pd_shared3p float64 t; test(test_prefix, lt(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, lt(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, lt(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, lt(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, lt(t), t); }

    test_prefix = "Operator >=";
//    { pd_shared3p bool t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p bool t; test(test_prefix, false, t); }
    { pd_shared3p uint8 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p int8 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p int16 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p int32 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p int64 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p float32 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p float64 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, gt_or_eq(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, gt_or_eq(t), t); }

    test_prefix = "Operator <=";
//    { pd_shared3p bool t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p bool t; test(test_prefix, false, t); }
    { pd_shared3p uint8 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p int8 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p int16 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p int32 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p int64 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p float32 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p float64 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, lt_or_eq(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, lt_or_eq(t), t); }

    test_prefix = "Operator ==";
    { pd_shared3p bool t; test(test_prefix, eq(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, eq(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, eq(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, eq(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, eq(t), t); }
    { pd_shared3p int8 t; test(test_prefix, eq(t), t); }
    { pd_shared3p int16 t; test(test_prefix, eq(t), t); }
    { pd_shared3p int32 t; test(test_prefix, eq(t), t); }
    { pd_shared3p int64 t; test(test_prefix, eq(t), t); }
    { pd_shared3p float32 t; test(test_prefix, eq(t), t); }
    { pd_shared3p float64 t; test(test_prefix, eq(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, eq(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, eq(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, eq(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, eq(t), t); }

    test_prefix = "Operator !=";
    { pd_shared3p bool t; test(test_prefix, ne(t), t); }
    { pd_shared3p uint8 t; test(test_prefix, ne(t), t); }
    { pd_shared3p uint16 t; test(test_prefix, ne(t), t); }
    { pd_shared3p uint32 t; test(test_prefix, ne(t), t); }
    { pd_shared3p uint64 t; test(test_prefix, ne(t), t); }
    { pd_shared3p int8 t; test(test_prefix, ne(t), t); }
    { pd_shared3p int16 t; test(test_prefix, ne(t), t); }
    { pd_shared3p int32 t; test(test_prefix, ne(t), t); }
    { pd_shared3p int64 t; test(test_prefix, ne(t), t); }
    { pd_shared3p float32 t; test(test_prefix, ne(t), t); }
    { pd_shared3p float64 t; test(test_prefix, ne(t), t); }
    { pd_shared3p xor_uint8 t; test(test_prefix, ne(t), t); }
    { pd_shared3p xor_uint16 t; test(test_prefix, ne(t), t); }
    { pd_shared3p xor_uint32 t; test(test_prefix, ne(t), t); }
    { pd_shared3p xor_uint64 t; test(test_prefix, ne(t), t); }

    test_report();
}

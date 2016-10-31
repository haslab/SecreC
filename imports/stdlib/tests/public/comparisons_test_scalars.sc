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

template<type T>
bool eq(T t) {
    T a = 0, b = 1;
    bool [[1]] result = {
        a == a,
        !(a == b),
        !(b == a),
        b == b
    };

    return all(result);
}

bool eq(bool t) {
    bool a = false, b = true;
    bool [[1]] result = {
        a == a,
        !(a == b),
        !(b == a),
        b == b
    };

    return all(result);
}

template<type T>
bool gt(T t) {
    T a = 0, b = 1;
    bool [[1]] result = {
        !(a > a),
        !(a > b),
        b > a,
        !(b > b)
    };

    return all(result);
}

bool gt(bool t) {
    bool a = false, b = true;
    bool [[1]] result = {
        !(a > a),
        !(a > b),
        b > a,
        !(b > b)
    };

    return all(result);
}

template<type T>
bool gt_or_eq(T t) {
    T a = 0, b = 1;
    bool [[1]] result = {
        a >= a,
        !(a >= b),
        b >= a,
        b >= b
    };

    return all(result);
}

bool gt_or_eq(bool t) {
    bool a = false, b = true;
    bool [[1]] result = {
        a >= a,
        !(a >= b),
        b >= a,
        b >= b
    };

    return all(result);
}

template<type T>
bool lt(T t) {
    T a = 0, b = 1;
    bool [[1]] result = {
        !(a < a),
        a < b,
        !(b < a),
        !(b < b)
    };

    return all(result);
}

bool lt(bool t) {
    bool a = false, b = true;
    bool [[1]] result = {
        !(a < a),
        a < b,
        !(b < a),
        !(b < b)
    };

    return all(result);
}

template<type T>
bool lt_or_eq(T t) {
    T a = 0, b = 1;
    bool [[1]] result = {
        a <= a,
        a <= b,
        !(b <= a),
        b <= b
    };

    return all(result);
}

bool lt_or_eq(bool t) {
    bool a = false, b = true;
    bool [[1]] result = {
        a <= a,
        a <= b,
        !(b <= a),
        b <= b
    };

    return all(result);
}

template<type T>
bool ne(T t) {
    T a = 0, b = 1;
    bool [[1]] result = {
        !(a != a),
        a != b,
        b != a,
        !(b != b)
    };

    return all(result);
}

bool ne(bool t) {
    bool a = false, b = true;
    bool [[1]] result = {
        !(a != a),
        a != b,
        b != a,
        !(b != b)
    };

    return all(result);
}

void main() {
    string test_prefix = "Operator >";
    test(test_prefix, gt(true), true);
    test(test_prefix, gt(0::uint8), 0::uint8);
    test(test_prefix, gt(0::uint16), 0::uint16);
    test(test_prefix, gt(0::uint32), 0::uint32);
    test(test_prefix, gt(0::uint64), 0::uint64);
    test(test_prefix, gt(0::int8), 0::int8);
    test(test_prefix, gt(0::int16), 0::int16);
    test(test_prefix, gt(0::int32), 0::int32);
    test(test_prefix, gt(0::int64), 0::int64);
    test(test_prefix, gt(0::float32), 0::float32);
    test(test_prefix, gt(0::float64), 0::float64);

    test_prefix = "Operator <";
    test(test_prefix, lt(true), true);
    test(test_prefix, lt(0::uint8), 0::uint8);
    test(test_prefix, lt(0::uint16), 0::uint16);
    test(test_prefix, lt(0::uint32), 0::uint32);
    test(test_prefix, lt(0::uint64), 0::uint64);
    test(test_prefix, lt(0::int8), 0::int8);
    test(test_prefix, lt(0::int16), 0::int16);
    test(test_prefix, lt(0::int32), 0::int32);
    test(test_prefix, lt(0::int64), 0::int64);
    test(test_prefix, lt(0::float32), 0::float32);
    test(test_prefix, lt(0::float64), 0::float64);

    test_prefix = "Operator >=";
    test(test_prefix, gt_or_eq(true), true);
    test(test_prefix, gt_or_eq(0::uint8), 0::uint8);
    test(test_prefix, gt_or_eq(0::uint16), 0::uint16);
    test(test_prefix, gt_or_eq(0::uint32), 0::uint32);
    test(test_prefix, gt_or_eq(0::uint64), 0::uint64);
    test(test_prefix, gt_or_eq(0::int8), 0::int8);
    test(test_prefix, gt_or_eq(0::int16), 0::int16);
    test(test_prefix, gt_or_eq(0::int32), 0::int32);
    test(test_prefix, gt_or_eq(0::int64), 0::int64);
    test(test_prefix, gt_or_eq(0::float32), 0::float32);
    test(test_prefix, gt_or_eq(0::float64), 0::float64);

    test_prefix = "Operator <=";
    test(test_prefix, lt_or_eq(true), true);
    test(test_prefix, lt_or_eq(0::uint8), 0::uint8);
    test(test_prefix, lt_or_eq(0::uint16), 0::uint16);
    test(test_prefix, lt_or_eq(0::uint32), 0::uint32);
    test(test_prefix, lt_or_eq(0::uint64), 0::uint64);
    test(test_prefix, lt_or_eq(0::int8), 0::int8);
    test(test_prefix, lt_or_eq(0::int16), 0::int16);
    test(test_prefix, lt_or_eq(0::int32), 0::int32);
    test(test_prefix, lt_or_eq(0::int64), 0::int64);
    test(test_prefix, lt_or_eq(0::float32), 0::float32);
    test(test_prefix, lt_or_eq(0::float64), 0::float64);

    test_prefix = "Operator ==";
    test(test_prefix, eq(true), true);
    test(test_prefix, eq(0::uint8), 0::uint8);
    test(test_prefix, eq(0::uint16), 0::uint16);
    test(test_prefix, eq(0::uint32), 0::uint32);
    test(test_prefix, eq(0::uint64), 0::uint64);
    test(test_prefix, eq(0::int8), 0::int8);
    test(test_prefix, eq(0::int16), 0::int16);
    test(test_prefix, eq(0::int32), 0::int32);
    test(test_prefix, eq(0::int64), 0::int64);
    test(test_prefix, eq(0::float32), 0::float32);
    test(test_prefix, eq(0::float64), 0::float64);

    test_prefix = "Operator !=";
    test(test_prefix, ne(true), true);
    test(test_prefix, ne(0::uint8), 0::uint8);
    test(test_prefix, ne(0::uint16), 0::uint16);
    test(test_prefix, ne(0::uint32), 0::uint32);
    test(test_prefix, ne(0::uint64), 0::uint64);
    test(test_prefix, ne(0::int8), 0::int8);
    test(test_prefix, ne(0::int16), 0::int16);
    test(test_prefix, ne(0::int32), 0::int32);
    test(test_prefix, ne(0::int64), 0::int64);
    test(test_prefix, ne(0::float32), 0::float32);
    test(test_prefix, ne(0::float64), 0::float64);

    test_report();
}

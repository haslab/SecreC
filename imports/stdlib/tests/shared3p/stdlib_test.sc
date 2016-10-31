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
bool equal_shapes_test(T data){
    {
        pd_shared3p T[[2]] mat (5,5);
        pd_shared3p T[[2]] mat2 (5,5);
        T[[2]] mat3 = declassify(randomize(mat));
        T[[2]] mat4 = declassify(randomize(mat2));
        bool result = shapesAreEqual(mat3,mat4);
        if (!all(shape(mat3) == shape(mat4)))
            return false;
    }
    {
        pd_shared3p T[[2]] mat (4,6);
        pd_shared3p T[[2]] mat2 (24,3);
        T[[2]] mat3 = declassify(randomize(mat));
        T[[2]] mat4 = declassify(randomize(mat2));
        bool result = shapesAreEqual(mat3,mat4);
        if (all(shape(mat3) == shape(mat4)))
            return false;
    }

    return true;
}

void main(){
    string test_prefix = "Shapes are equal utility";
    test(test_prefix, equal_shapes_test(true), true);
    test(test_prefix, equal_shapes_test(0::uint8), 0::uint8);
    test(test_prefix, equal_shapes_test(0::uint16), 0::uint16);
    test(test_prefix, equal_shapes_test(0::uint32), 0::uint32);
    test(test_prefix, equal_shapes_test(0::uint64), 0::uint64);
    test(test_prefix, equal_shapes_test(0::int8), 0::int8);
    test(test_prefix, equal_shapes_test(0::int16), 0::int16);
    test(test_prefix, equal_shapes_test(0::int32), 0::int32);
    test(test_prefix, equal_shapes_test(0::int64), 0::int64);

    test_report();
}

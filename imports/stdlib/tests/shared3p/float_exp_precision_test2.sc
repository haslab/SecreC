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

module float_precision;

import stdlib;
import shared3p;
import test_utility;

domain pd_shared3p shared3p;

template<type T>
bool test_exp2(T data){
    pd_shared3p T[[1]] a (5) = 2.608711404814097;
    T[[1]] c (5);
    c = declassify(exp(a));

    return (c[0] == c[1]) && (c[0] == c[2]) && (c[0] == c[3]) && (c[0] == c[4]);
}

void main(){
    string test_prefix = "Float32/64 exp precision(2)";
    test(test_prefix, test_exp2(0::float32), 0::float32);
    test(test_prefix, test_exp2(0::float64), 0::float64);

    test_report();
}

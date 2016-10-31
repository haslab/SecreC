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

module test_utility;

import stdlib;

string var_prefix = "test";
uint all_tests = 0;
uint passed_tests = 0;
uint failed_tests = 0;

template<type T>
struct PrecisionTest {
    bool res;
    T max_abs_error;
    T max_rel_error;
}

template<type T>
string _precision_to_string(PrecisionTest<T> prec) {
    return "(max abs. error: " + tostring(prec.max_abs_error) + ", max rel. error: " + tostring(prec.max_rel_error) + ")";
}

template <dim N>
void test(string desc, bool [[N]] resvec) {
    bool res = all(resvec);
    publish(var_prefix + tostring(all_tests) + "_description", desc);
    publish(var_prefix + tostring(all_tests) + "_result", res);
    ++all_tests;
    res ? ++passed_tests : ++failed_tests;
}

template <domain D, type T, dim N, dim M>
void test(string desc, bool [[N]] resvec, D T [[M]] t) {
    bool res = all(resvec);
    publish(var_prefix + tostring(all_tests) + "_description", "[$T] " + desc);
    publish(var_prefix + tostring(all_tests) + "_result", res);
    ++all_tests;
    res ? ++passed_tests : ++failed_tests;
}

template <type T>
void test(string desc, PrecisionTest<T> p) {
    publish(var_prefix + tostring(all_tests) + "_description", "[$T] " + desc + " " + _precision_to_string(p));
    publish(var_prefix + tostring(all_tests) + "_result", p.res);
    ++all_tests;
    p.res ? ++passed_tests : ++failed_tests;
}

template <domain D, type T, type U, dim N, dim M, dim O>
void test(string desc, bool [[N]] resvec, D T [[M]] t, D U [[O]] u) {
    bool res = all(resvec);
    publish(var_prefix + tostring(all_tests) + "_description", "[$T,$U] " + desc);
    publish(var_prefix + tostring(all_tests) + "_result", res);
    ++all_tests;
    res ? ++passed_tests : ++failed_tests;
}

void test_report() {
    publish("test_count", all_tests);
    publish("passed_count", passed_tests);
}


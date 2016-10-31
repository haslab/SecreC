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

void main(){
    string test_prefix = "Addition with two private values";
    {
        pd_shared3p uint8[[1]] a(15) = 15, b(15) = 174, c(15) = 189;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175, b(15) = 45876, c(15) = 46051;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398, b(15) = 21798357, c(15) = 21800755;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953, b(15) = 1872698523698, c(15) = 1872701102651;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = -25, b(15) = 50, c(15) = 25;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = -2264, b(15) = 22468, c(15) = 20204;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = -12549, b(15) = 21485747, c(15) = 21473198;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 2954, b(15) = 93214654775807, c(15) = 93214654778761;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    test_prefix = "Addition with one private one public value";
    {
        pd_shared3p uint8[[1]] a(15) = 15; uint8[[1]] b(15) = 174; pd_shared3p uint8[[1]] c(15) = 189;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175; uint16[[1]] b(15) = 45876; pd_shared3p uint16[[1]] c(15) = 46051;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398; uint32[[1]] b(15) = 21798357; pd_shared3p uint32[[1]] c(15) = 21800755;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953; uint64[[1]] b(15) = 1872698523698; pd_shared3p uint64[[1]] c(15) = 1872701102651;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = -25; int8[[1]] b(15) = 50; pd_shared3p int8[[1]] c(15) = 25;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = -2264; int16[[1]] b(15) = 22468; pd_shared3p int16[[1]] c(15) = 20204;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = -12549; int32[[1]] b(15) = 21485747; pd_shared3p int32[[1]] c(15) = 21473198;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 2954; int64[[1]] b(15) = 93214654775807; pd_shared3p int64[[1]] c(15) = 93214654778761;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    test_prefix = "Addition with one private one public value(2)";
    {
        pd_shared3p uint8[[1]] a(15) = 15; uint8[[1]] b(15) = 174; pd_shared3p uint8[[1]] c(15) = 189;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175; uint16[[1]] b(15) = 45876; pd_shared3p uint16[[1]] c(15) = 46051;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398; uint32[[1]] b(15) = 21798357; pd_shared3p uint32[[1]] c(15) = 21800755;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953; uint64[[1]] b(15) = 1872698523698; pd_shared3p uint64[[1]] c(15) = 1872701102651;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = -25; int8[[1]] b(15) = 50; pd_shared3p int8[[1]] c(15) = 25;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = -2264; int16[[1]] b(15) = 22468; pd_shared3p int16[[1]] c(15) = 20204;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = -12549; int32[[1]] b(15) = 21485747; pd_shared3p int32[[1]] c(15) = 21473198;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 2954; int64[[1]] b(15) = 93214654775807; pd_shared3p int64[[1]] c(15) = 93214654778761;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    test_prefix = "Addition with two private values modulo (type_MAX + 1)";
    {
        pd_shared3p uint8[[1]] a(15) = 1, b(15) = UINT8_MAX, c(15) = 0;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 1, b(15) = UINT16_MAX, c(15) = 0;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 1, b(15) = UINT32_MAX, c(15) = 0;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 1, b(15) = UINT64_MAX, c(15) = 0;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = 1, b(15) = INT8_MAX, c(15) = INT8_MIN;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = 1, b(15) = INT16_MAX, c(15) = INT16_MIN;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = 1, b(15) = INT32_MAX, c(15) = INT32_MIN;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 1, b(15) = INT64_MAX, c(15) = INT64_MIN;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    test_prefix = "Addition with private values modulo (A + T_MAX+1 = A)";
    {
        pd_shared3p uint8[[1]] a(15) = 15, b(15) = UINT8_MAX, c(15) = a;
        test(test_prefix, declassify(a+b+1) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175, b(15) = UINT16_MAX, c(15) = a;
        test(test_prefix, declassify(a+b+1) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398, b(15) = UINT32_MAX, c(15) = a;
        test(test_prefix, declassify(a+b+1) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953, b(15) = UINT64_MAX, c(15) = a;
        test(test_prefix, declassify(a+b+1) == declassify(c), c);
    }
    test_prefix = "Subtraction with two private values";
    {
        pd_shared3p uint8[[1]] a(15) = 15, b(15) = 174, c(15) = 159;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175, b(15) = 45876, c(15) = 45701;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398, b(15) = 21798357, c(15) = 21795959;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953, b(15) = 1872698523698, c(15) = 1872695944745;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = 25, b(15) = 50, c(15) = 25;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = 42264, b(15) = 22468, c(15) = -19796;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = 12549, b(15) = 21485747, c(15) = 21473198;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 2954, b(15) = 93214654775807, c(15) = 93214654772853;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    test_prefix = "Subtraction with one private one public value";
    {
        pd_shared3p uint8[[1]] a(15) = 15; uint8[[1]] b(15) = 174; pd_shared3p uint8[[1]] c(15) = 159;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175; uint16[[1]] b(15) = 45876; pd_shared3p uint16[[1]] c(15) = 45701;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398; uint32[[1]] b(15) = 21798357; pd_shared3p uint32[[1]] c(15) = 21795959;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953; uint64[[1]] b(15) = 1872698523698; pd_shared3p uint64[[1]] c(15) = 1872695944745;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = 25; int8[[1]] b(15) = 50; pd_shared3p int8[[1]] c(15) = 25;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = 42264; int16[[1]] b(15) = 22468; pd_shared3p int16[[1]] c(15) = -19796;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = 12549; int32[[1]] b(15) = 21485747; pd_shared3p int32[[1]] c(15) = 21473198;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 2954; int64[[1]] b(15) = 93214654775807; pd_shared3p int64[[1]] c(15) = 93214654772853;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    test_prefix = "Subtraction with one private one public value(2)";
    {
        pd_shared3p uint8[[1]] a(15) = 174; uint8[[1]] b(15) = 15; pd_shared3p uint8[[1]] c(15) = 159;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 45876; uint16[[1]] b(15) = 175; pd_shared3p uint16[[1]] c(15) = 45701;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 21798357; uint32[[1]] b(15) = 2398; pd_shared3p uint32[[1]] c(15) = 21795959;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 1872698523698; uint64[[1]] b(15) = 2578953; pd_shared3p uint64[[1]] c(15) = 1872695944745;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = 50; int8[[1]] b(15) = 25; pd_shared3p int8[[1]] c(15) = 25;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = 22468; int16[[1]] b(15) = 42264; pd_shared3p int16[[1]] c(15) = -19796;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = 21485747; int32[[1]] b(15) =12549; pd_shared3p int32[[1]] c(15) = 21473198;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 93214654775807; int64[[1]] b(15) = 2954; pd_shared3p int64[[1]] c(15) = 93214654772853;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    test_prefix = "Subtraction with two private values modulo (type_MIN - 1)";
    {
        pd_shared3p uint8[[1]] a(15) = 1, b(15) = 0, c(15) = UINT8_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 1, b(15) = 0, c(15) = UINT16_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 1, b(15) = 0, c(15) = UINT32_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 1, b(15) = 0, c(15) = UINT64_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = 1, b(15) = INT8_MIN, c(15) = INT8_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = 1, b(15) = INT16_MIN, c(15) = INT16_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = 1, b(15) = INT32_MIN, c(15) = INT32_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 1, b(15) = INT64_MIN, c(15) = INT64_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    test_prefix = "Multiplication with two private values";
    {
        pd_shared3p uint8[[1]] a(15) = 15, b(15) = 12, c(15) = 180;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175, b(15) = 139, c(15) = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398, b(15) = 4051, c(15) = 9714298;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 248924, b(15) = 48265, c(15) = 12014316860;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = 25, b(15) = -4, c(15) = -100;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = 175, b(15) = 139, c(15) = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = -2398, b(15) = 4051, c(15) = -9714298;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 248924, b(15) = 48265, c(15) = 12014316860;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    test_prefix = "Multiplication with one private one public value";
    {
        pd_shared3p uint8[[1]] a(15) = 15; uint8[[1]] b(15) = 12; pd_shared3p uint8[[1]] c(15) = 180;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175; uint16[[1]] b(15) = 139; pd_shared3p uint16[[1]] c(15) = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398; uint32[[1]] b(15) = 4051; pd_shared3p uint32[[1]] c(15) = 9714298;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 248924; uint64[[1]] b(15) = 48265; pd_shared3p uint64[[1]] c(15) = 12014316860;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = 25; int8[[1]] b(15) = -4; pd_shared3p int8[[1]] c(15) = -100;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = 175; int16[[1]] b(15) = 139; pd_shared3p int16[[1]] c(15) = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = -2398; int32[[1]] b(15) = 4051; pd_shared3p int32[[1]] c(15) = -9714298;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 248924; int64[[1]] b(15) = 48265; pd_shared3p int64[[1]] c(15) = 12014316860;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    test_prefix = "Multiplication with one private one public value(2)";
    {
        pd_shared3p uint8[[1]] a(15) = 15; uint8[[1]] b(15) = 12; pd_shared3p uint8[[1]] c(15) = 180;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175; uint16[[1]] b(15) = 139; pd_shared3p uint16[[1]] c(15) = 24325;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398; uint32[[1]] b(15) = 4051; pd_shared3p uint32[[1]] c(15) = 9714298;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 248924; uint64[[1]] b(15) = 48265; pd_shared3p uint64[[1]] c(15) = 12014316860;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = 25; int8[[1]] b(15) = -4; pd_shared3p int8[[1]] c(15) = -100;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = 175; int16[[1]] b(15) = 139; pd_shared3p int16[[1]] c(15) = 24325;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = -2398; int32[[1]] b(15) = 4051; pd_shared3p int32[[1]] c(15) = -9714298;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = 248924; int64[[1]] b(15) = 48265; pd_shared3p int64[[1]] c(15) = 12014316860;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    test_prefix = "Multiplication with two private values modulo (type_MAX * 5)";
    {
        pd_shared3p uint8[[1]] a(15) = UINT8_MAX-1, b(15) = 5, c(15) = 246;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = UINT16_MAX-1, b(15) = 5, c(15) = 65526;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = UINT32_MAX-1, b(15) = 5, c(15) = 4294967286;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = UINT64_MAX-1, b(15) = 5, c(15) = 18446744073709551606;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int8[[1]] a(15) = INT8_MAX-1, b(15) = 5, c(15) = 118;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int16[[1]] a(15) = INT16_MAX-1, b(15) = 5, c(15) = 32758;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int32[[1]] a(15) = INT32_MAX-1, b(15) = 5, c(15) = 2147483638;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int64[[1]] a(15) = INT64_MAX-1, b(15) = 5, c(15) = 9223372036854775798;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }

    test_prefix = "Division with two private values";
    {
        pd_shared3p uint8[[1]] a(15) = 15, b(15) = 174, c(15) = 11;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175, b(15) = 45876, c(15) = 262;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398, b(15) = 21798357, c(15) = 9090;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953, b(15) = 1872698523698, c(15) = 726146;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    test_prefix = "Division with one private one public value";
    {
        pd_shared3p uint8[[1]] a(15) = 15; uint8[[1]] b(15) = 174; pd_shared3p uint8[[1]] c(15) = 11;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175; uint16[[1]] b(15) = 45876; pd_shared3p uint16[[1]] c(15) = 262;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398; uint32[[1]] b(15) = 21798357; pd_shared3p uint32[[1]] c(15) = 9090;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953; uint64[[1]] b(15) = 1872698523698; pd_shared3p uint64[[1]] c(15) = 726146;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    test_prefix = "Division with one private one public value(2)";
    {
        pd_shared3p uint8[[1]] a(15) = 15; uint8[[1]] b(15) = 174; pd_shared3p uint8[[1]] c(15) = 0;
//        test(test_prefix, declassify(a/b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175; uint16[[1]] b(15) = 45876; pd_shared3p uint16[[1]] c(15) = 0;
//        test(test_prefix, declassify(a/b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398; uint32[[1]] b(15) = 21798357; pd_shared3p uint32[[1]] c(15) = 0;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953; uint64[[1]] b(15) = 1872698523698; pd_shared3p uint64[[1]] c(15) = 0;
//        test(test_prefix, declassify(a/b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    test_prefix = "0 divided with random private values";
    {
        pd_shared3p uint8[[1]] a(15) = 15, b(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = 175, b(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = 2398, b(15) = 0, c(15) = 0;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = 2578953, b(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    test_prefix = "Division accuracy private";
    {
        pd_shared3p uint8[[1]] a(15) = UINT8_MAX, b(15) = UINT8_MAX -1, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16[[1]] a(15) = UINT16_MAX, b(15) = UINT16_MAX -1, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32[[1]] a(15) = UINT32_MAX, b(15) = UINT32_MAX -1, c(15) = 0;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] a(15) = UINT64_MAX, b(15) = UINT64_MAX-1, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int8[[1]] a(15) = INT8_MAX, b(15) = INT8_MAX-1, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int16[[1]] a(15) = INT16_MAX, b(15) = INT16_MAX-1, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int32[[1]] a(15) = INT32_MAX, b(15) = INT32_MAX-1, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int64[[1]] a(15) = INT64_MAX, b(15) = INT64_MAX-1, c(15) = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }

    test_prefix = "Modulo private values";
    {
        pd_shared3p uint8[[1]] b(15) = 15, a(15) = 174, c(15) = 9;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16[[1]] b(15) = 175, a(15) = 45876, c(15) = 26;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32[[1]] b(15) = 2398, a(15) = 21798357, c(15) = 537;
        test(test_prefix, declassify(a%b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] b(15) = 2578953, a(15) = 1872698523698, c(15) = 2118560;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int8[[1]] b(15) = -25, a(15) = 50, c(15) = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int16[[1]] b(15) = -2264, a(15) = 22468, c(15) = 2092;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int32[[1]] b(15) = -12549, a(15) = 21485747, c(15) = 1859;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int64[[1]] b(15) = 2954, a(15) = 93214654775807, c(15) = 257;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }

    test_prefix = "Modulo with private and public values";
    {
        pd_shared3p uint8[[1]] b(15) = 15; uint8[[1]] a(15) = 174; pd_shared3p uint8[[1]] c(15) = 9;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16[[1]] b(15) = 175; uint16[[1]] a(15) = 45876; pd_shared3p uint16[[1]] c(15) = 26;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32[[1]] b(15) = 2398; uint32[[1]] a(15) = 21798357; pd_shared3p uint32[[1]] c(15) = 537;
        test(test_prefix, declassify(a%b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] b(15) = 2578953; uint64[[1]] a(15) = 1872698523698; pd_shared3p uint64[[1]] c(15) = 2118560;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int8[[1]] b(15) = -25; int8[[1]] a(15) = 50; pd_shared3p int8[[1]] c(15) = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int16[[1]] b(15) = -2264; int16[[1]] a(15) = 22468; pd_shared3p int16[[1]] c(15) = 2092;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int32[[1]] b(15) = -12549; int32[[1]] a(15) = 21485747; pd_shared3p int32[[1]] c(15) = 1859;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int64[[1]] b(15) = 2954; int64[[1]] a(15) = 93214654775807; pd_shared3p int64[[1]] c(15) = 257;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }

    test_prefix = "Modulo with private and public values(2)";
    {
        pd_shared3p uint8[[1]] b(15) = 174; uint8[[1]] a(15) = 15; pd_shared3p uint8[[1]] c(15) = 9;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16[[1]] b(15) = 45876; uint16[[1]] a(15) = 175 ; pd_shared3p uint16[[1]] c(15) = 26;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32[[1]] b(15) = 21798357; uint32[[1]] a(15) = 2398 ; pd_shared3p uint32[[1]] c(15) = 537;
        test(test_prefix, declassify(b%a) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] b(15) = 1872698523698; uint64[[1]] a(15) = 2578953; pd_shared3p uint64[[1]] c(15) = 2118560;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int8[[1]] b(15) = 50; int8[[1]] a(15) = -25; pd_shared3p int8[[1]] c(15) = 0;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int16[[1]] b(15) = 22468; int16[[1]] a(15) = -2264; pd_shared3p int16[[1]] c(15) = 2092;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int32[[1]] b(15) = 21485747; int32[[1]] a(15) = -12549; pd_shared3p int32[[1]] c(15) = 1859;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int64[[1]] b(15) = 93214654775807; int64[[1]] a(15) = 2954; pd_shared3p int64[[1]] c(15) = 257;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }

    test_prefix = "Modulo with important private values";
    {
        pd_shared3p uint8[[1]] b(15) = 1, a(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = 1;  a = 1;  c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = UINT8_MAX;  a = UINT8_MAX;  c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16[[1]] b(15) = 1, a(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = 1;  a = 1; c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = UINT16_MAX;a = UINT16_MAX;c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32[[1]] b(15) = 1, a(15) = 0, c(15) = 0;
        test(test_prefix, declassify(a%b) == declassify(c), c);

        b = 1; a = 1; c = 0;
        test(test_prefix, declassify(a%b) == declassify(c), c);

        b = UINT32_MAX; a = UINT32_MAX; c = 0;
        test(test_prefix, declassify(a%b) == declassify(c), c);
    }
    {
        pd_shared3p uint64[[1]] b(15) = 1, a(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = 1; a = 1;c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = UINT64_MAX; a = UINT64_MAX;  c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int8[[1]] b(15) = 1, a(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = 1;  a = 1;  c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = INT8_MAX;  a = INT8_MAX;  c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int16[[1]] b(15) = 1, a(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = 1;a = 1;c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = INT16_MAX;a = INT16_MAX;c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int32[[1]] b(15) = 1, a(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = 1;a = 1;c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = INT32_MAX;a = INT32_MAX;c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int64[[1]] b(15) = 1, a(15) = 0, c(15) = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = 1;a = 1;c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);

        b = INT64_MAX;a = INT64_MAX;c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }

    test_report();
}

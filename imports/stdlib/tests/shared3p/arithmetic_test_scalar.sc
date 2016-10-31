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
        pd_shared3p uint8 a = 15, b = 174, c = 189;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 175, b = 45876, c = 46051;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 2398, b = 21798357, c = 21800755;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953, b = 1872698523698, c = 1872701102651;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = -25, b = 50, c = 25;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = -2264, b = 22468, c = 20204;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = -12549, b = 21485747, c = 21473198;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 2954, b = 93214654775807, c = 93214654778761;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    test_prefix = "Addition with one private one public value";
    {
        pd_shared3p uint8 a = 15; uint8 b = 174; pd_shared3p uint8 c = 189;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 175; uint16 b = 45876; pd_shared3p uint16 c = 46051;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 2398; uint32 b = 21798357; pd_shared3p uint32 c = 21800755;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953; uint64 b = 1872698523698; pd_shared3p uint64 c = 1872701102651;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = -25; int8 b = 50; pd_shared3p int8 c = 25;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = -2264; int16 b = 22468; pd_shared3p int16 c = 20204;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = -12549; int32 b = 21485747; pd_shared3p int32 c = 21473198;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 2954; int64 b = 93214654775807; pd_shared3p int64 c = 93214654778761;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    test_prefix = "Addition with one private one public value(2)";
    {
        pd_shared3p uint8 a = 15; uint8 b = 174; pd_shared3p uint8 c = 189;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 175; uint16 b = 45876; pd_shared3p uint16 c = 46051;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 2398; uint32 b = 21798357; pd_shared3p uint32 c = 21800755;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953; uint64 b = 1872698523698; pd_shared3p uint64 c = 1872701102651;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = -25; int8 b = 50; pd_shared3p int8 c = 25;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = -2264; int16 b = 22468; pd_shared3p int16 c = 20204;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = -12549; int32 b = 21485747; pd_shared3p int32 c = 21473198;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 2954; int64 b = 93214654775807; pd_shared3p int64 c = 93214654778761;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    test_prefix = "Addition with two private values modulo (type_MAX + 1)";
    {
        pd_shared3p uint8 a = 1, b = UINT8_MAX, c = 0;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 1, b = UINT16_MAX, c = 0;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 1, b = UINT32_MAX, c = 0;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 1, b = UINT64_MAX, c = 0;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = 1, b = INT8_MAX, c = INT8_MIN;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = 1, b = INT16_MAX, c = INT16_MIN;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = 1, b = INT32_MAX, c = INT32_MIN;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 1, b = INT64_MAX, c = INT64_MIN;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    test_prefix = "Addition with private values modulo (A + T_MAX+1 = A)";
    {
        pd_shared3p uint8 a = 15, b = UINT8_MAX, c = a;
        test(test_prefix, declassify(a+b+1) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 175, b = UINT16_MAX, c = a;
        test(test_prefix, declassify(a+b+1) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 2398, b = UINT32_MAX, c = a;
        test(test_prefix, declassify(a+b+1) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953, b = UINT64_MAX, c = a;
        test(test_prefix, declassify(a+b+1) == declassify(c), c);
    }
    test_prefix = "Subtraction with two private values";
    {
        pd_shared3p uint8 a = 15, b = 174, c = 159;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 175, b = 45876, c = 45701;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 2398, b = 21798357, c = 21795959;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953, b = 1872698523698, c = 1872695944745;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = 25, b = 50, c = 25;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = 42264, b = 22468, c = -19796;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = 12549, b = 21485747, c = 21473198;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 2954, b = 93214654775807, c = 93214654772853;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    test_prefix = "Subtraction with one private one public value";
    {
        pd_shared3p uint8 a = 15; uint8 b = 174; pd_shared3p uint8 c = 159;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 175; uint16 b = 45876; pd_shared3p uint16 c = 45701;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 2398; uint32 b = 21798357; pd_shared3p uint32 c = 21795959;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953; uint64 b = 1872698523698; pd_shared3p uint64 c = 1872695944745;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = 25; int8 b = 50; pd_shared3p int8 c = 25;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = 42264; int16 b = 22468; pd_shared3p int16 c = -19796;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = 12549; int32 b = 21485747; pd_shared3p int32 c = 21473198;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 2954; int64 b = 93214654775807; pd_shared3p int64 c = 93214654772853;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    test_prefix = "Subtraction with one private one public value(2)";
    {
        pd_shared3p uint8 a = 174; uint8 b = 15; pd_shared3p uint8 c = 159;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 45876; uint16 b = 175; pd_shared3p uint16 c = 45701;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 21798357; uint32 b = 2398; pd_shared3p uint32 c = 21795959;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 1872698523698; uint64 b = 2578953; pd_shared3p uint64 c = 1872695944745;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = 50; int8 b = 25; pd_shared3p int8 c = 25;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = 22468; int16 b = 42264; pd_shared3p int16 c = -19796;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = 21485747; int32 b =12549; pd_shared3p int32 c = 21473198;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 93214654775807; int64 b = 2954; pd_shared3p int64 c = 93214654772853;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    test_prefix = "Subtraction with two private values modulo (type_MIN - 1)";
    {
        pd_shared3p uint8 a = 1, b = 0, c = UINT8_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 1, b = 0, c = UINT16_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 1, b = 0, c = UINT32_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 1, b = 0, c = UINT64_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = 1, b = INT8_MIN, c = INT8_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = 1, b = INT16_MIN, c = INT16_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = 1, b = INT32_MIN, c = INT32_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 1, b = INT64_MIN, c = INT64_MAX;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    test_prefix = "Multiplication with two private values";
    {
        pd_shared3p uint8 a = 15, b = 12, c = 180;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 175, b = 139, c = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 2398, b = 4051, c = 9714298;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 248924, b = 48265, c = 12014316860;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = 25, b = -4, c = -100;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = 175, b = 139, c = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = -2398, b = 4051, c = -9714298;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 248924, b = 48265, c = 12014316860;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    test_prefix = "Multiplication with one private one public value";
    {
        pd_shared3p uint8 a = 15; uint8 b = 12; pd_shared3p uint8 c = 180;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 175; uint16 b = 139; pd_shared3p uint16 c = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 2398; uint32 b = 4051; pd_shared3p uint32 c = 9714298;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 248924; uint64 b = 48265; pd_shared3p uint64 c = 12014316860;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = 25; int8 b = -4; pd_shared3p int8 c = -100;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = 175; int16 b = 139; pd_shared3p int16 c = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = -2398; int32 b = 4051; pd_shared3p int32 c = -9714298;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 248924; int64 b = 48265; pd_shared3p int64 c = 12014316860;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    test_prefix = "Multiplication with one private one public value(2)";
    {
        pd_shared3p uint8 a = 15; uint8 b = 12; pd_shared3p uint8 c = 180;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = 175; uint16 b = 139; pd_shared3p uint16 c = 24325;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = 2398; uint32 b = 4051; pd_shared3p uint32 c = 9714298;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 248924; uint64 b = 48265; pd_shared3p uint64 c = 12014316860;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = 25; int8 b = -4; pd_shared3p int8 c = -100;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = 175; int16 b = 139; pd_shared3p int16 c = 24325;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = -2398; int32 b = 4051; pd_shared3p int32 c = -9714298;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = 248924; int64 b = 48265; pd_shared3p int64 c = 12014316860;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    test_prefix = "Multiplication with two private values modulo (type_MAX * 5)";
    {
        pd_shared3p uint8 a = UINT8_MAX-1, b = 5, c = 246;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint16 a = UINT16_MAX-1, b = 5, c = 65526;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint32 a = UINT32_MAX-1, b = 5, c = 4294967286;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = UINT64_MAX-1, b = 5, c = 18446744073709551606;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int8 a = INT8_MAX-1, b = 5, c = 118;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int16 a = INT16_MAX-1, b = 5, c = 32758;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int32 a = INT32_MAX-1, b = 5, c = 2147483638;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p int64 a = INT64_MAX-1, b = 5, c = 9223372036854775798;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }

    test_prefix = "Division with two private values";
    {
        pd_shared3p uint8 a = 15, b = 174, c = 11;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16 a = 175, b = 45876, c = 262;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32 a = 2398, b = 21798357, c = 9090;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953, b = 1872698523698, c = 726146;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    test_prefix = "Division with one private one public value";
    {
        pd_shared3p uint8 a = 15; uint8 b = 174; pd_shared3p uint8 c = 11;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16 a = 175; uint16 b = 45876; pd_shared3p uint16 c = 262;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32 a = 2398; uint32 b = 21798357; pd_shared3p uint32 c = 9090;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953; uint64 b = 1872698523698; pd_shared3p uint64 c = 726146;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    test_prefix = "Division with one private one public value(2)";
    {
        pd_shared3p uint8 a = 15; uint8 b = 174; pd_shared3p uint8 c = 0;
//        test(test_prefix, declassify(a/b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16 a = 175; uint16 b = 45876; pd_shared3p uint16 c = 0;
//        test(test_prefix, declassify(a/b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32 a = 2398; uint32 b = 21798357; pd_shared3p uint32 c = 0;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953; uint64 b = 1872698523698; pd_shared3p uint64 c = 0;
//        test(test_prefix, declassify(a/b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    test_prefix = "0 divided with random private values";
    {
        pd_shared3p uint8 a = 15, b = 0, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16 a = 175, b = 0, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32 a = 2398, b = 0, c = 0;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = 2578953, b = 0, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    test_prefix = "Division accuracy private";
    {
        pd_shared3p uint8 a = UINT8_MAX, b = UINT8_MAX -1, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16 a = UINT16_MAX, b = UINT16_MAX -1, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32 a = UINT32_MAX, b = UINT32_MAX -1, c = 0;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 a = UINT64_MAX, b = UINT64_MAX-1, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int8 a = INT8_MAX, b = INT8_MAX-1, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int16 a = INT16_MAX, b = INT16_MAX-1, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int32 a = INT32_MAX, b = INT32_MAX-1, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int64 a = INT64_MAX, b = INT64_MAX-1, c = 0;
//        test(test_prefix, declassify(b/a) == declassify(c), c);
        test(test_prefix, false, c);
    }

    test_prefix = "Modulo private values";
    {
        pd_shared3p uint8 b = 15, a = 174, c = 9;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16 b = 175, a = 45876, c = 26;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32 b = 2398, a = 21798357, c = 537;
        test(test_prefix, declassify(a%b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 b = 2578953, a = 1872698523698, c = 2118560;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int8 b = -25, a = 50, c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int16 b = -2264, a = 22468, c = 2092;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int32 b = -12549, a = 21485747, c = 1859;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int64 b = 2954, a = 93214654775807, c = 257;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }

    test_prefix = "Modulo with private and public values";
    {
        pd_shared3p uint8 b = 15; uint8 a = 174; pd_shared3p uint8 c = 9;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16 b = 175; uint16 a = 45876; pd_shared3p uint16 c = 26;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32 b = 2398; uint32 a = 21798357; pd_shared3p uint32 c = 537;
        test(test_prefix, declassify(a%b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 b = 2578953; uint64 a = 1872698523698; pd_shared3p uint64 c = 2118560;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int8 b = -25; int8 a = 50; pd_shared3p int8 c = 0;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int16 b = -2264; int16 a = 22468; pd_shared3p int16 c = 2092;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int32 b = -12549; int32 a = 21485747; pd_shared3p int32 c = 1859;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int64 b = 2954; int64 a = 93214654775807; pd_shared3p int64 c = 257;
//        test(test_prefix, declassify(a%b) == declassify(c), c);
        test(test_prefix, false, c);
    }

    test_prefix = "Modulo with private and public values(2)";
    {
        pd_shared3p uint8 b = 174; uint8 a = 15; pd_shared3p uint8 c = 9;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint16 b = 45876; uint16 a = 175 ; pd_shared3p uint16 c = 26;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p uint32 b = 21798357; uint32 a = 2398 ; pd_shared3p uint32 c = 537;
        test(test_prefix, declassify(b%a) == declassify(c), c);
    }
    {
        pd_shared3p uint64 b = 1872698523698; uint64 a = 2578953; pd_shared3p uint64 c = 2118560;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int8 b = 50; int8 a = -25; pd_shared3p int8 c = 0;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int16 b = 22468; int16 a = -2264; pd_shared3p int16 c = 2092;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int32 b = 21485747; int32 a = -12549; pd_shared3p int32 c = 1859;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }
    {
        pd_shared3p int64 b = 93214654775807; int64 a = 2954; pd_shared3p int64 c = 257;
//        test(test_prefix, declassify(b%a) == declassify(c), c);
        test(test_prefix, false, c);
    }

    test_prefix = "Modulo with important private values";
    {
        pd_shared3p uint8 b = 1, a = 0, c = 0;
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
        pd_shared3p uint16 b = 1, a = 0, c = 0;
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
        pd_shared3p uint32 b = 1, a = 0, c = 0;
        test(test_prefix, declassify(a%b) == declassify(c), c);

        b = 1; a = 1; c = 0;
        test(test_prefix, declassify(a%b) == declassify(c), c);

        b = UINT32_MAX; a = UINT32_MAX; c = 0;
        test(test_prefix, declassify(a%b) == declassify(c), c);
    }
    {
        pd_shared3p uint64 b = 1, a = 0, c = 0;
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
        pd_shared3p int8 b = 1, a = 0, c = 0;
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
        pd_shared3p int16 b = 1, a = 0, c = 0;
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
        pd_shared3p int32 b = 1, a = 0, c = 0;
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
        pd_shared3p int64 b = 1, a = 0, c = 0;
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

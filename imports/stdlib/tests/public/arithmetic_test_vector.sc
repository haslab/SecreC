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

void main(){
    // TODO Add tests for float32 and float64.

    string test_prefix = "Addition with two public values";
    {
        uint8 [[1]] a(15) = 15; uint8 [[1]] b(15) = 174; uint8 [[1]] c(15) = 189;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint16 [[1]] a(15) = 175; uint16 [[1]] b(15) = 45876; uint16 [[1]] c(15) = 46051;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint32 [[1]] a(15) = 2398; uint32 [[1]] b(15) = 21798357; uint32 [[1]] c(15) = 21800755;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint64 [[1]] a(15) = 2578953; uint64 [[1]] b(15) = 1872698523698; uint64 [[1]] c(15) = 1872701102651;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int8 [[1]] a(15) = -25; int8 [[1]] b(15) = 50; int8 [[1]] c(15) = 25;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int16 [[1]] a(15) = -2264; int16 [[1]] b(15) = 22468; int16 [[1]] c(15) = 20204;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int32 [[1]] a(15) = -12549; int32 [[1]] b(15) = 21485747; int32 [[1]] c(15) = 21473198;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int64 [[1]] a(15) = 2954; int64 [[1]] b(15) = 93214654775807; int64 [[1]] c(15) = 93214654778761;
        test(test_prefix, (a + b) == c, c);
    }
    test_prefix = "Addition with two public values modulo (T_MAX + 1)";
    {
        uint8 [[1]] a(15) = 1; uint8 [[1]] b(15) = UINT8_MAX; uint8 [[1]] c(15) = 0;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint16 [[1]] a(15) = 1; uint16 [[1]] b(15) = UINT16_MAX; uint16 [[1]] c(15) = 0;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint32 [[1]] a(15) = 1; uint32 [[1]] b(15) = UINT32_MAX; uint32 [[1]] c(15) = 0;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint64 [[1]] a(15) = 1; uint64 [[1]] b(15) = UINT64_MAX; uint64 [[1]] c(15) = 0;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int8 [[1]] a(15) = 1; int8 [[1]] b(15) = INT8_MAX; int8 [[1]] c(15) = INT8_MIN;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int16 [[1]] a(15) = 1; int16 [[1]] b(15) = INT16_MAX; int16 [[1]] c(15) = INT16_MIN;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int32 [[1]] a(15) = 1; int32 [[1]] b(15) = INT32_MAX; int32 [[1]] c(15) = INT32_MIN;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int64 [[1]] a(15) = 1; int64 [[1]] b(15) = INT64_MAX; int64 [[1]] c(15) = INT64_MIN;
        test(test_prefix, (a + b) == c, c);
    }
    test_prefix = "Addition with public values modulo (A + T_MAX + 1 = A)";
    {
        uint8 [[1]] a(15) = 15; uint8 [[1]] b(15) = UINT8_MAX + 1;
        test(test_prefix, (a + b) == a, a);
    }
    {
        uint16 [[1]] a(15) = 175; uint16 [[1]] b(15) = UINT16_MAX + 1;
        test(test_prefix, (a + b) == a, a);
    }
    {
        uint32 [[1]] a(15) = 2398; uint32 [[1]] b(15) = UINT32_MAX + 1;
        test(test_prefix, (a + b) == a, a);
    }
    {
        uint64 [[1]] a(15) = 2578953; uint64 [[1]] b(15) = UINT64_MAX + 1;
        test(test_prefix, (a + b) == a, a);
    }
    test_prefix = "Subtraction with two public values";
    {
        uint8 [[1]] a(15) = 15; uint8 [[1]] b(15) = 174; uint8 [[1]] c(15) = 159;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint16 [[1]] a(15) = 175; uint16 [[1]] b(15) = 45876; uint16 [[1]] c(15) = 45701;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint32 [[1]] a(15) = 2398; uint32 [[1]] b(15) = 21798357; uint32 [[1]] c(15) = 21795959;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint64 [[1]] a(15) = 2578953; uint64 [[1]] b(15) = 1872698523698; uint64 [[1]] c(15) = 1872695944745;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int8 [[1]] a(15) = 25; int8 [[1]] b(15) = 50; int8 [[1]] c(15) = 25;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int16 [[1]] a(15) = 42264; int16 [[1]] b(15) = 22468; int16 [[1]] c(15) = -19796;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int32 [[1]] a(15) = 12549; int32 [[1]] b(15) = 21485747; int32 [[1]] c(15) = 21473198;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int64 [[1]] a(15) = 2954; int64 [[1]] b(15) = 93214654775807; int64 [[1]] c(15) = 93214654772853;
        test(test_prefix, (b - a) == c, c);
    }
    test_prefix = "Subtraction with two public values modulo (T_MIN - 1)";
    {
        uint8 [[1]] a(15) = 1; uint8 [[1]] b(15) = 0; uint8 [[1]] c(15) = UINT8_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint16 [[1]] a(15) = 1; uint16 [[1]] b(15) = 0; uint16 [[1]] c(15) = UINT16_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint32 [[1]] a(15) = 1; uint32 [[1]] b(15) = 0; uint32 [[1]] c(15) = UINT32_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint64 [[1]] a(15) = 1; uint64 [[1]] b(15) = 0; uint64 [[1]] c(15) = UINT64_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int8 [[1]] a(15) = 1; int8 [[1]] b(15) = INT8_MIN; int8 [[1]] c(15) = INT8_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int16 [[1]] a(15) = 1; int16 [[1]] b(15) = INT16_MIN; int16 [[1]] c(15) = INT16_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int32 [[1]] a(15) = 1; int32 [[1]] b(15) = INT32_MIN; int32 [[1]] c(15) = INT32_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int64 [[1]] a(15) = 1; int64 [[1]] b(15) = INT64_MIN; int64 [[1]] c(15) = INT64_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    test_prefix = "Multiplication with two public values";
    {
        uint8 [[1]] a(15) = 15; uint8 [[1]] b(15) = 12; uint8 [[1]] c(15) = 180;
        test(test_prefix, (a * b) == c, c);
    }
    {
        uint16 [[1]] a(15) = 175; uint16 [[1]] b(15) = 139; uint16 [[1]] c(15) = 24325;
        test(test_prefix, (a * b) == c, c);
    }
    {
        uint32 [[1]] a(15) = 2398; uint32 [[1]] b(15) = 4051; uint32 [[1]] c(15) = 9714298;
        test(test_prefix, (a * b) == c, c);
    }
    {
        uint64 [[1]] a(15) = 248924; uint64 [[1]] b(15) = 48265; uint64 [[1]] c(15) = 12014316860;
        test(test_prefix, (a * b) == c, c);
    }
    {
        int8 [[1]] a(15) = 25; int8 [[1]] b(15) = -4; int8 [[1]] c(15) = -100;
        test(test_prefix, (a * b) == c, c);
    }
    {
        int16 [[1]] a(15) = 175; int16 [[1]] b(15) = 139; int16 [[1]] c(15) = 24325;
        test(test_prefix, (a * b) == c, c);
    }
    {
        int32 [[1]] a(15) = -2398; int32 [[1]] b(15) = 4051; int32 [[1]] c(15) = -9714298;
        test(test_prefix, (a * b) == c, c);
    }
    {
        int64 [[1]] a(15) = 248924; int64 [[1]] b(15) = 48265; int64 [[1]] c(15) = 12014316860;
        test(test_prefix, (a * b) == c, c);
    }
    test_prefix = "Multiplication with two public values modulo (type_MAX * 5)";
    {
        uint8 [[1]] a(15) = UINT8_MAX-1; uint8 [[1]] c(15) = 246;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        uint16 [[1]] a(15) = UINT16_MAX-1; uint16 [[1]] c(15) = 65526;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        uint32 [[1]] a(15) = UINT32_MAX-1; uint32 [[1]] c(15) = 4294967286;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        uint64 [[1]] a(15) = UINT64_MAX-1; uint64 [[1]] c(15) = 18446744073709551606;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        int8 [[1]] a(15) = INT8_MAX-1; int8 [[1]] c(15) = 118;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        int16 [[1]] a(15) = INT16_MAX-1; int16 [[1]] c(15) = 32758;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        int32 [[1]] a(15) = INT32_MAX-1; int32 [[1]] c(15) = 2147483638;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        int64 [[1]] a(15) = INT64_MAX-1; int64 [[1]] c(15) = 9223372036854775798;
        test(test_prefix, (a * 5) == c, c);
    }
    test_prefix = "Division with two public values";
    {
        uint8 [[1]] a(15) = 15; uint8 [[1]] b(15) = 174; uint8 [[1]] c(15) = 11;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint16 [[1]] a(15) = 175; uint16 [[1]] b(15) = 45876; uint16 [[1]] c(15) = 262;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint32 [[1]] a(15) = 2398; uint32 [[1]] b(15) = 21798357; uint32 [[1]] c(15) = 9090;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint64 [[1]] a(15) = 2578953; uint64 [[1]] b(15) = 1872698523698; uint64 [[1]] c(15) = 726146;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int8 [[1]] a(15) = 25; int8 [[1]] b(15) = 50; int8 [[1]] c(15) = 2;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int16 [[1]] a(15) = 42264; int16 [[1]] b(15) = 22468; int16 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int32 [[1]] a(15) = 12549; int32 [[1]] b(15) = 21485747; int32 [[1]] c(15) = 1712;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int64 [[1]] a(15) = 982175129826; int64 [[1]] b(15) = 93214654775807; int64 [[1]] c(15) = 94;
        test(test_prefix, (b / a) == c, c);
    }
    test_prefix = "0 divided with random public values";
    {
        uint8 [[1]] a(15) = 15; uint8 [[1]] b(15) = 0; uint8 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint16 [[1]] a(15) = 175; uint16 [[1]] b(15) = 0; uint16 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint32 [[1]] a(15) = 2398; uint32 [[1]] b(15) = 0; uint32 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint64 [[1]] a(15) = 2578953; uint64 [[1]] b(15) = 0; uint64 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int8 [[1]] a(15) = 25; int8 [[1]] b(15) = 0; int8 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int16 [[1]] a(15) = 42264; int16 [[1]] b(15) = 0; int16 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int32 [[1]] a(15) = 12549; int32 [[1]] b(15) = 0; int32 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int64 [[1]] a(15) = 982175129826; int64 [[1]] b(15) = 0; int64 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    test_prefix = "A / A = 1 with all public types";
    {
        uint8 [[1]] a(15) = 174; uint8 [[1]] b(15) = 174; uint8 [[1]] c(15) = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint16 [[1]] a(15) = 45876; uint16 [[1]] b(15) = 45876; uint16 [[1]] c(15) = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint32 [[1]] a(15) = 21798357; uint32 [[1]] b(15) = 21798357; uint32 [[1]] c(15) = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint64 [[1]] a(15) = 1872698523698; uint64 [[1]] b(15) = 1872698523698; uint64 [[1]] c(15) = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int8 [[1]] a(15) = 50; int8 [[1]] b(15) = 50; int8 [[1]] c(15) = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int16 [[1]] a(15) = 22468; int16 [[1]] b(15) = 22468; int16 [[1]] c(15) = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int32 [[1]] a(15) = 21485747; int32 [[1]] b(15) = 21485747; int32 [[1]] c(15) = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int64 [[1]] a(15) = 93214654775807; int64 [[1]] b(15) = 93214654775807; int64 [[1]] c(15) = 1;
        test(test_prefix, (b / a) == c, c);
    }
    test_prefix = "Division accuracy public";
    {
        uint8 [[1]] a(15) = UINT8_MAX; uint8 [[1]] b(15) = UINT8_MAX -1 ; uint8 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint16 [[1]] a(15) = UINT16_MAX; uint16 [[1]] b(15) = UINT16_MAX -1; uint16 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint32 [[1]] a(15) = UINT32_MAX; uint32 [[1]] b(15) = UINT32_MAX -1; uint32 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint64 [[1]] a(15) = UINT64_MAX; uint64 [[1]] b(15) = UINT64_MAX-1; uint64 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int8 [[1]] a(15) = INT8_MAX; int8 [[1]] b(15) = INT8_MAX-1; int8 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int16 [[1]] a(15) = INT16_MAX; int16 [[1]] b(15) = INT16_MAX-1; int16 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int32 [[1]] a(15) = INT32_MAX; int32 [[1]] b(15) = INT32_MAX-1; int32 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int64 [[1]] a(15) = INT64_MAX; int64 [[1]] b(15) = INT64_MAX-1; int64 [[1]] c(15) = 0;
        test(test_prefix, (b / a) == c, c);
    }
    test_prefix = "Modulus on public values";
    {
        uint8 [[1]] b(15) = 15; uint8 [[1]] a(15) = 174; uint8 [[1]] c(15) = 9;
        test(test_prefix, (a % b) == c, c);
    }
    {
        uint16 [[1]] b(15) = 175; uint16 [[1]] a(15) = 45876; uint16 [[1]] c(15) = 26;
        test(test_prefix, (a % b) == c, c);
    }
    {
        uint32 [[1]] b(15) = 2398; uint32 [[1]] a(15) = 21798357; uint32 [[1]] c(15) = 537;
        test(test_prefix, (a % b) == c, c);
    }
    {
        uint64 [[1]] b(15) = 2578953; uint64 [[1]] a(15) = 1872698523698; uint64 [[1]] c(15) = 2118560;
        test(test_prefix, (a % b) == c, c);
    }
    {
        int8 [[1]] b(15) = -25; int8 [[1]] a(15) = 50; int8 [[1]] c(15) = 0;
        test(test_prefix, (a % b) == c, c);
    }
    {
        int16 [[1]] b(15) = -2264; int16 [[1]] a(15) = 22468; int16 [[1]] c(15) = 2092;
        test(test_prefix, (a % b) == c, c);
    }
    {
        int32 [[1]] b(15) = -12549; int32 [[1]] a(15) = 21485747; int32 [[1]] c(15) = 1859;
        test(test_prefix, (a % b) == c, c);
    }
    {
        int64 [[1]] b(15) = 2954; int64 [[1]] a(15) = 93214654775807; int64 [[1]] c(15) = 257;
        test(test_prefix, (a % b) == c, c);
    }
    test_prefix = "Operation priorities : Multiplication over addition";
    {
        uint8 [[1]] a(15) = 5; uint8 [[1]] b(15) = 20; uint8 [[1]] c(15) = 45; uint8 [[1]] d(15) = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        uint16 [[1]] a(15) = 5; uint16 [[1]] b(15) = 20; uint16 [[1]] c(15) = 45; uint16 [[1]] d(15) = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        uint32 [[1]] a(15) = 5; uint32 [[1]] b(15) = 20; uint32 [[1]] c(15) = 45; uint32 [[1]] d(15) = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        uint64 [[1]] a(15) = 5; uint64 [[1]] b(15) = 20; uint64 [[1]] c(15) = 45; uint64 [[1]] d(15) = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        int8 [[1]] a(15) = 5; int8 [[1]] b(15) = 20; int8 [[1]] c(15) = 45; int8 [[1]] d(15) = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        int16 [[1]] a(15) = 5; int16 [[1]] b(15) = 20; int16 [[1]] c(15) = 45; int16 [[1]] d(15) = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        uint32 [[1]] a(15) = 5; uint32 [[1]] b(15) = 20; uint32 [[1]] c(15) = 45; uint32 [[1]] d(15) = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        int64 [[1]] a(15) = 5; int64 [[1]] b(15) = 20; int64 [[1]] c(15) = 45; int64 [[1]] d(15) = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    test_prefix = "Operation priorities : Parentheses over multiplication";
    {
        uint8 [[1]] a(15) = 5; uint8 [[1]] b(15) = 5; uint8 [[1]] c(15) = 20; uint8 [[1]] d(15) = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        uint16 [[1]] a(15) = 5; uint16 [[1]] b(15) = 5; uint16 [[1]] c(15) = 20; uint16 [[1]] d(15) = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        uint32 [[1]] a(15) = 5; uint32 [[1]] b(15) = 5; uint32 [[1]] c(15) = 20; uint32 [[1]] d(15) = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        uint64 [[1]] a(15) = 5; uint64 [[1]] b(15) = 5; uint64 [[1]] c(15) = 20; uint64 [[1]] d(15) = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        int8 [[1]] a(15) = 5; int8 [[1]] b(15) = 5; int8 [[1]] c(15) = 20; int8 [[1]] d(15) = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        int16 [[1]] a(15) = 5; int16 [[1]] b(15) = 5; int16 [[1]] c(15) = 20; int16 [[1]] d(15) = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        uint32 [[1]] a(15) = 5; uint32 [[1]] b(15) = 5; uint32 [[1]] c(15) = 20; uint32 [[1]] d(15) = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        int64 [[1]] a(15) = 5; int64 [[1]] b(15) = 5; int64 [[1]] c(15) = 20; int64 [[1]] d(15) = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    test_prefix = "Operation priorities : Division over addition and subtraction";
    {
        uint8 [[1]] a(15) = 5; uint8 [[1]] b(15) = 5; uint8 [[1]] c(15) = 20; uint8 [[1]] d(15) = 5; uint8 [[1]] e(15) = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        uint16 [[1]] a(15) = 5; uint16 [[1]] b(15) = 5; uint16 [[1]] c(15) = 20; uint16 [[1]] d(15) = 5; uint16 [[1]] e(15) = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        uint32 [[1]] a(15) = 5; uint32 [[1]] b(15) = 5; uint32 [[1]] c(15) = 20; uint32 [[1]] d(15) = 5; uint32 [[1]] e(15) = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        uint64 [[1]] a(15) = 5; uint64 [[1]] b(15) = 5; uint64 [[1]] c(15) = 20; uint64 [[1]] d(15) = 5; uint64 [[1]] e(15) = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        int8 [[1]] a(15) = 5; int8 [[1]] b(15) = 5; int8 [[1]] c(15) = 20; int8 [[1]] d(15) = 5; int8 [[1]] e(15) = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        int16 [[1]] a(15) = 5; int16 [[1]] b(15) = 5; int16 [[1]] c(15) = 20; int16 [[1]] d(15) = 5; int16 [[1]] e(15) = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        int32 [[1]] a(15) = 5; int32 [[1]] b(15) = 5; int32 [[1]] c(15) = 20; int32 [[1]] d(15) = 5; int32 [[1]] e(15) = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        int64 [[1]] a(15) = 5; int64 [[1]] b(15) = 5; int64 [[1]] c(15) = 20; int64 [[1]] d(15) = 5; int64 [[1]] e(15) = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }

    test_report();
}

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

void main() {
    // TODO Add tests for float32 and float64.

    string test_prefix = "Addition with two public values";
    {
        uint8 a = 15; uint8 b = 174; uint8 c = 189;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint16 a = 175; uint16 b = 45876; uint16 c = 46051;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint32 a = 2398; uint32 b = 21798357; uint32 c = 21800755;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint a = 2578953; uint b = 1872698523698; uint c = 1872701102651;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int8 a = -25; int8 b = 50; int8 c = 25;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int16 a = -2264; int16 b = 22468; int16 c = 20204;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int32 a = -12549; int32 b = 21485747; int32 c = 21473198;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int a = 2954; int b = 93214654775807; int c = 93214654778761;
        test(test_prefix, (a + b) == c, c);
    }
    test_prefix = "Addition with two public values modulo (T_MAX + 1)";
    {
        uint8 a = 1; uint8 b = UINT8_MAX; uint8 c = 0;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint16 a = 1; uint16 b = UINT16_MAX; uint16 c = 0;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint32 a = 1; uint32 b = UINT32_MAX; uint32 c = 0;
        test(test_prefix, (a + b) == c, c);
    }
    {
        uint a = 1; uint b = UINT64_MAX; uint c = 0;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int8 a = 1; int8 b = INT8_MAX; int8 c = INT8_MIN;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int16 a = 1; int16 b = INT16_MAX; int16 c = INT16_MIN;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int32 a = 1; int32 b = INT32_MAX; int32 c = INT32_MIN;
        test(test_prefix, (a + b) == c, c);
    }
    {
        int a = 1; int b = INT64_MAX; int c = INT64_MIN;
        test(test_prefix, (a + b) == c, c);
    }
    test_prefix = "Addition with public values modulo (A + T_MAX + 1 = A)";
    {
        uint8 a = 15; uint8 b = UINT8_MAX + 1;
        test(test_prefix, (a + b) == a, a);
    }
    {
        uint16 a = 175; uint16 b = UINT16_MAX + 1;
        test(test_prefix, (a + b) == a, a);
    }
    {
        uint32 a = 2398; uint32 b = UINT32_MAX + 1;
        test(test_prefix, (a + b) == a, a);
    }
    {
        uint a = 2578953; uint b = UINT64_MAX + 1;
        test(test_prefix, (a + b) == a, a);
    }
    test_prefix = "Subtraction with two public values";
    {
        uint8 a = 15; uint8 b = 174; uint8 c = 159;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint16 a = 175; uint16 b = 45876; uint16 c = 45701;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint32 a = 2398; uint32 b = 21798357; uint32 c = 21795959;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint a = 2578953; uint b = 1872698523698; uint c = 1872695944745;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int8 a = 25; int8 b = 50; int8 c = 25;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int16 a = 42264; int16 b = 22468; int16 c = -19796;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int32 a = 12549; int32 b = 21485747; int32 c = 21473198;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int a = 2954; int b = 93214654775807; int c = 93214654772853;
        test(test_prefix, (b - a) == c, c);
    }
    test_prefix = "Subtraction with two public values modulo (T_MIN - 1)";
    {
        uint8 a = 1; uint8 b = 0; uint8 c = UINT8_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint16 a = 1; uint16 b = 0; uint16 c = UINT16_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint32 a = 1; uint32 b = 0; uint32 c = UINT32_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        uint a = 1; uint b = 0; uint c = UINT64_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int8 a = 1; int8 b = INT8_MIN; int8 c = INT8_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int16 a = 1; int16 b = INT16_MIN; int16 c = INT16_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int32 a = 1; int32 b = INT32_MIN; int32 c = INT32_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    {
        int a = 1; int b = INT64_MIN; int c = INT64_MAX;
        test(test_prefix, (b - a) == c, c);
    }
    test_prefix = "Multiplication with two public values";
    {
        uint8 a = 15; uint8 b = 12; uint8 c = 180;
        test(test_prefix, (a * b) == c, c);
    }
    {
        uint16 a = 175; uint16 b = 139; uint16 c = 24325;
        test(test_prefix, (a * b) == c, c);
    }
    {
        uint32 a = 2398; uint32 b = 4051; uint32 c = 9714298;
        test(test_prefix, (a * b) == c, c);
    }
    {
        uint a = 248924; uint b = 48265; uint c = 12014316860;
        test(test_prefix, (a * b) == c, c);
    }
    {
        int8 a = 25; int8 b = -4; int8 c = -100;
        test(test_prefix, (a * b) == c, c);
    }
    {
        int16 a = 175; int16 b = 139; int16 c = 24325;
        test(test_prefix, (a * b) == c, c);
    }
    {
        int32 a = -2398; int32 b = 4051; int32 c = -9714298;
        test(test_prefix, (a * b) == c, c);
    }
    {
        int a = 248924; int b = 48265; int c = 12014316860;
        test(test_prefix, (a * b) == c, c);
    }
    test_prefix = "Multiplication with two public values modulo (type_MAX * 5)";
    {
        uint8 a = UINT8_MAX-1; uint8 c = 246;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        uint16 a = UINT16_MAX-1; uint16 c = 65526;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        uint32 a = UINT32_MAX-1; uint32 c = 4294967286;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        uint a = UINT64_MAX-1; uint c = 18446744073709551606;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        int8 a = INT8_MAX-1; int8 c = 118;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        int16 a = INT16_MAX-1; int16 c = 32758;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        int32 a = INT32_MAX-1; int32 c = 2147483638;
        test(test_prefix, (a * 5) == c, c);
    }
    {
        int a = INT64_MAX-1; int c = 9223372036854775798;
        test(test_prefix, (a * 5) == c, c);
    }
    test_prefix = "Division with two public values";
    {
        uint8 a = 15; uint8 b = 174; uint8 c = 11;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint16 a = 175; uint16 b = 45876; uint16 c = 262;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint32 a = 2398; uint32 b = 21798357; uint32 c = 9090;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint a = 2578953; uint b = 1872698523698; uint c = 726146;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int8 a = 25; int8 b = 50; int8 c = 2;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int16 a = 42264; int16 b = 22468; int16 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int32 a = 12549; int32 b = 21485747; int32 c = 1712;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int a = 982175129826; int b = 93214654775807; int c = 94;
        test(test_prefix, (b / a) == c, c);
    }
    test_prefix = "0 divided with random public values";
    {
        uint8 a = 15; uint8 b = 0; uint8 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint16 a = 175; uint16 b = 0; uint16 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint32 a = 2398; uint32 b = 0; uint32 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint a = 2578953; uint b = 0; uint c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int8 a = 25; int8 b = 0; int8 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int16 a = 42264; int16 b = 0; int16 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int32 a = 12549; int32 b = 0; int32 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int a = 982175129826; int b = 0; int c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    test_prefix = "A / A = 1 with all public types";
    {
        uint8 a = 174; uint8 b = 174; uint8 c = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint16 a = 45876; uint16 b = 45876; uint16 c = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint32 a = 21798357; uint32 b = 21798357; uint32 c = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint a = 1872698523698; uint b = 1872698523698; uint c = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int8 a = 50; int8 b = 50; int8 c = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int16 a = 22468; int16 b = 22468; int16 c = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int32 a = 21485747; int32 b = 21485747; int32 c = 1;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int a = 93214654775807; int b = 93214654775807; int c = 1;
        test(test_prefix, (b / a) == c, c);
    }
    test_prefix = "Division accuracy public";
    {
        uint8 a = UINT8_MAX; uint8 b = UINT8_MAX -1 ; uint8 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint16 a = UINT16_MAX; uint16 b = UINT16_MAX -1; uint16 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint32 a = UINT32_MAX; uint32 b = UINT32_MAX -1; uint32 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        uint a = UINT64_MAX; uint b = UINT64_MAX-1; uint c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int8 a = INT8_MAX; int8 b = INT8_MAX-1; int8 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int16 a = INT16_MAX; int16 b = INT16_MAX-1; int16 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int32 a = INT32_MAX; int32 b = INT32_MAX-1; int32 c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    {
        int a = INT64_MAX; int b = INT64_MAX-1; int c = 0;
        test(test_prefix, (b / a) == c, c);
    }
    test_prefix = "Modulus on public values";
    {
        uint8 b = 15; uint8 a = 174; uint8 c = 9;
        test(test_prefix, (a % b) == c, c);
    }
    {
        uint16 b = 175; uint16 a = 45876; uint16 c = 26;
        test(test_prefix, (a % b) == c, c);
    }
    {
        uint32 b = 2398; uint32 a = 21798357; uint32 c = 537;
        test(test_prefix, (a % b) == c, c);
    }
    {
        uint b = 2578953; uint a = 1872698523698; uint c = 2118560;
        test(test_prefix, (a % b) == c, c);
    }
    {
        int8 b = -25; int8 a = 50; int8 c = 0;
        test(test_prefix, (a % b) == c, c);
    }
    {
        int16 b = -2264; int16 a = 22468; int16 c = 2092;
        test(test_prefix, (a % b) == c, c);
    }
    {
        int32 b = -12549; int32 a = 21485747; int32 c = 1859;
        test(test_prefix, (a % b) == c, c);
    }
    {
        int b = 2954; int a = 93214654775807; int c = 257;
        test(test_prefix, (a % b) == c, c);
    }
    test_prefix = "Operation priorities : Multiplication over addition";
    {
        uint8 a = 5; uint8 b = 20; uint8 c = 45; uint8 d = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        uint16 a = 5; uint16 b = 20; uint16 c = 45; uint16 d = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        uint32 a = 5; uint32 b = 20; uint32 c = 45; uint32 d = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        uint a = 5; uint b = 20; uint c = 45; uint d = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        int8 a = 5; int8 b = 20; int8 c = 45; int8 d = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        int16 a = 5; int16 b = 20; int16 c = 45; int16 d = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        uint32 a = 5; uint32 b = 20; uint32 c = 45; uint32 d = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    {
        int a = 5; int b = 20; int c = 45; int d = 145;
        test(test_prefix, (c + b * a) == d, d);
    }
    test_prefix = "Operation priorities : Parentheses over multiplication";
    {
        uint8 a = 5; uint8 b = 5; uint8 c = 20; uint8 d = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        uint16 a = 5; uint16 b = 5; uint16 c = 20; uint16 d = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        uint32 a = 5; uint32 b = 5; uint32 c = 20; uint32 d = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        uint a = 5; uint b = 5; uint c = 20; uint d = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        int8 a = 5; int8 b = 5; int8 c = 20; int8 d = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        int16 a = 5; int16 b = 5; int16 c = 20; int16 d = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        uint32 a = 5; uint32 b = 5; uint32 c = 20; uint32 d = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    {
        int a = 5; int b = 5; int c = 20; int d = 125;
        test(test_prefix, ((c + b) * a) == d, d);
    }
    test_prefix = "Operation priorities : Division over addition and subtraction";
    {
        uint8 a = 5; uint8 b = 5; uint8 c = 20; uint8 d = 5; uint8 e = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        uint16 a = 5; uint16 b = 5; uint16 c = 20; uint16 d = 5; uint16 e = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        uint32 a = 5; uint32 b = 5; uint32 c = 20; uint32 d = 5; uint32 e = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        uint a = 5; uint b = 5; uint c = 20; uint d = 5; uint e = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        int8 a = 5; int8 b = 5; int8 c = 20; int8 d = 5; int8 e = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        int16 a = 5; int16 b = 5; int16 c = 20; int16 d = 5; int16 e = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        int32 a = 5; int32 b = 5; int32 c = 20; int32 d = 5; int32 e = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }
    {
        int a = 5; int b = 5; int c = 20; int d = 5; int e = 16;
        test(test_prefix, (c - a + b / d) == e, e);
    }

    test_report();
}

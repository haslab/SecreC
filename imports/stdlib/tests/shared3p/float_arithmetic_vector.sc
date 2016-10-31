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

void main() {
    string test_prefix = "Addition with two private vectors";
    {
        pd_shared3p float32[[1]] a (15)= 15, b (15)= 174, c (15) = 189;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 175, b (15)= 45876, c (15) = 46051;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }

    test_prefix = "Addition with one private one public vector";
    {
        pd_shared3p float32[[1]] a (15)= 15; float32[[1]] b (15)= 174; pd_shared3p float32[[1]] c (15) = 189;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 175; float64[[1]] b (15)= 45876; pd_shared3p float64[[1]] c (15) = 46051;
        test(test_prefix, declassify(a+b) == declassify(c), c);
    }

    test_prefix = "Addition with one private one public vector(2)";
    {
        pd_shared3p float32[[1]] a (15)= 15; float32[[1]] b (15)= 174; pd_shared3p float32[[1]] c (15) = 189;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 175; float64[[1]] b (15)= 45876; pd_shared3p float64[[1]] c (15) = 46051;
        test(test_prefix, declassify(b+a) == declassify(c), c);
    }

    test_prefix = "Subtraction with two private vectors";
    {
        pd_shared3p float32[[1]] a (15)= 15, b (15)= 174, c (15) = 159;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 175, b (15)= 45876, c (15) = 45701;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }

    test_prefix = "Subtraction with one private one public vector";
    {
        pd_shared3p float32[[1]] a (15)= 15; float32[[1]] b (15)= 174; pd_shared3p float32[[1]] c (15) = 159;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 175; float64[[1]] b (15)= 45876; pd_shared3p float64[[1]] c (15) = 45701;
        test(test_prefix, declassify(b-a) == declassify(c), c);
    }

    test_prefix = "Subtraction with one private one public value(2)";
    {
        pd_shared3p float32[[1]] a (15)= 174; float32[[1]] b (15)= 15; pd_shared3p float32[[1]] c (15) = 159;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 45876; float64[[1]] b (15)= 175; pd_shared3p float64[[1]] c (15) = 45701;
        test(test_prefix, declassify(a-b) == declassify(c), c);
    }

    test_prefix = "Multiplication with two private vectors";
    {
        pd_shared3p float32[[1]] a (15)= 15, b (15)= 12, c (15) = 180;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 175, b (15)= 139, c (15) = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }

    test_prefix = "Multiplication with one private one public vector";
    {
        pd_shared3p float32[[1]] a (15)= 15; float32[[1]] b (15)= 12; pd_shared3p float32[[1]] c (15) = 180;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 175; float64[[1]] b (15)= 139; pd_shared3p float64[[1]] c (15) = 24325;
        test(test_prefix, declassify(a*b) == declassify(c), c);
    }

    test_prefix = "Multiplication with one private one public value(2)";
    {
        pd_shared3p float32[[1]] a (15)= 15; float32[[1]] b (15)= 12; pd_shared3p float32[[1]] c (15) = 180;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 175; float64[[1]] b (15)= 139; pd_shared3p float64[[1]] c (15) = 24325;
        test(test_prefix, declassify(b*a) == declassify(c), c);
    }

    test_prefix = "Division with two private values";
    {
        pd_shared3p float32[[1]] a (15)= 15, b (15)= 174, c (15) = 11.6;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 180, b (15)= 45900, c (15) = 255;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }

    test_prefix = "Division with one private one public value";
    {
        pd_shared3p float32[[1]] a (15)= 15; float32[[1]] b (15)= 174; pd_shared3p float32[[1]] c (15) = 11.6;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 180; float64[[1]] b (15)= 45900; pd_shared3p float64[[1]] c (15) = 255;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }

    test_prefix = "Division with one private one public value(2)";
    {
        pd_shared3p float32[[1]] a (15)= 174; float32[[1]] b (15)= 15; pd_shared3p float32[[1]] c (15) = 11.6;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 45900; float64[[1]] b (15)= 180; pd_shared3p float64[[1]] c (15) = 255;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }

    test_prefix = "0 divided with random private vectors";
    {
        pd_shared3p float32[[1]] a (15)= 15; float32[[1]] b (15)= 0; pd_shared3p float32[[1]] c (15) = 0;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 180; float64[[1]] b (15)= 0; pd_shared3p float64[[1]] c (15) = 0;
        test(test_prefix, declassify(b/a) == declassify(c), c);
    }

    test_prefix = "Division accuracy private";
    {
        pd_shared3p float32[[1]] a (15)= 645, b (15)= 40, c (15) = 16.125;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }
    {
        pd_shared3p float64[[1]] a (15)= 645, b (15)= 40, c (15) = 16.125;
        test(test_prefix, declassify(a/b) == declassify(c), c);
    }

    test_report();
}

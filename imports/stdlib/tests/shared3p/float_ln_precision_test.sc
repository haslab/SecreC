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

template<type T>
PrecisionTest<T> test_ln(T data){
    T max_absolute = 0, max_relative = 0;
    pd_shared3p T[[1]] a (6) = {
        51.35752137315483,
        2.608711404814097,
        8.850954516109905,
        5.192202509740625,
        24.36159839949806,
        0.2756185651367633
    };

    T[[1]] b (6) = {
        3.938811398348680089804643433376430680367653668588343000906230,
        0.958856384786789770072515166290468948953628611903734246556797,
        2.180525308131586498592170766819923549287755820600765970199695,
        1.647157982828476806467086708358951537473793664301911313654868,
        3.193008056432019284572330551494423539275983811534468092220874,
        -1.28873737949614117662681428728923733958919670534871008889074
    };

    pd_shared3p T[[1]] c (6);

    c = ln(a);
    T[[1]] d (6);
    T[[1]] temp(6) = b;

    d = declassify(c) - b;

    for(uint i = 0; i < 6;++i){
        if(d[i] < 0){d[i] = -d[i];}
        if(temp[i] < 0){temp[i] = -temp[i];}
    }
    max_absolute = max(d);
    max_relative = max(d / temp);

    public PrecisionTest<T> rv;
    rv.res = true;
    rv.max_abs_error = max_absolute;
    rv.max_rel_error = max_relative;

    return rv;
}

void main(){
    string test_prefix = "Float32/64 ln precision";
    {
        PrecisionTest<float32> rv = test_ln(0::float32);
        test(test_prefix, rv);
    }
    {
        PrecisionTest<float64> rv = test_ln(0::float64);
        test(test_prefix, rv);
    }

    test_report();
}

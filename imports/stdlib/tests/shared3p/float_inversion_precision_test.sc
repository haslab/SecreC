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
PrecisionTest<T> test_inversion(T data){
    T max_absolute = 0, max_relative = 0;
    pd_shared3p T[[1]] a (8) = {
        10.49934588656477,
        58.83904325241103,
        6.459133708592741,
        12.30305849067902,
        5.672880010454444,
        0.5154542504192215,
        -33.07334086055091,
        -8.146960136185919
    };
    T[[1]] b (8) = {
        0.095244028609403699186052996064777215723445856946584784926884,
        0.016995517682198601980202808696548131280981723968423205692767,
        0.154819523037536122962576052147431363914115676938109787699726,
        0.081280601954190079255736827142709095552187175689689325695726,
        0.176277305029741292975640471523912602826018007231098313451172,
        1.940036383804566626673218567731497610520720266582510220379170,
        -0.03023583266705227484615820064040857182654732612020244551028,
        -0.12274516915313642586555771859977852412995381036589904796001
    };
    pd_shared3p T[[1]] c (8);

    c = inv(a);
    T[[1]] d (8);
    T[[1]] temp(8) = b;

    d = declassify(c) - b;

    for(uint i = 0; i < 8;++i){
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
    string test_prefix = "Float32/64 inversion precision";
    {
        PrecisionTest<float32> rv = test_inversion(0::float32);
        test(test_prefix, rv);
    }
    {
        PrecisionTest<float64> rv = test_inversion(0::float64);
        test(test_prefix, rv);
    }

    test_report();
}

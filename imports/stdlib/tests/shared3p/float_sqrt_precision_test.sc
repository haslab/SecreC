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
PrecisionTest<T> test_sqrt(T data){
    T max_absolute = 0, max_relative = 0;
    pd_shared3p T[[1]] a (8) = {
        14.1566418266453,
        2.353240445436502,
        1.101880541351803,
        26.80217700594072,
        2.461238153504522,
        0.6487119793399101,
        3.497798862860427,
        1.757030089475017
    };
    T[[1]] b (8) = {
        3.7625313057362459638668630134746153084776989341461835,
        1.534027524341236192801048418712285670612360413934362466077706,
        1.049704978244746155686088076871481282485641505974230593725993,
        5.177081900640622471086424463319686255349670851106896530423644,
        1.568833373403473336501112685959116159596509349282887846858288,
        0.805426582215852930437182611153055291564735094770495012808766,
        1.870240322220763959112005305796522349151384344661816065940105,
        1.325530116396838793454662999150389473000883666573902051199777
    };
    pd_shared3p T[[1]] c (8);
    c = sqrt(a);

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
    string test_prefix = "Float32/64 sqrt precision";
    {
        PrecisionTest<float32> rv = test_sqrt(0::float32);
        test(test_prefix, rv);
    }
    {
        PrecisionTest<float64> rv = test_sqrt(0::float64);
        test(test_prefix, rv);
    }

    test_report();
}

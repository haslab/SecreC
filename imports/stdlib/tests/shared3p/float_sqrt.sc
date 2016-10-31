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
    pd_shared3p T[[1]] a (20) = {
        0.1,
        0.2,
        0.3,
        0.4,
        0.5,
        0.6,
        0.7,
        0.8,
        0.9,
        1,
        2,
        3,
        4,
        5,
        10,
        50,
        100,
        500,
        1000,
        10000
    };


    T[[1]] b (20) = {
        0.316227766016837933199889354443271853371955513932521682685750,
        0.447213595499957939281834733746255247088123671922305144854179,
        0.547722557505166113456969782800802133952744694997983254226894,
        0.632455532033675866399778708886543706743911027865043365371500,
        0.707106781186547524400844362104849039284835937688474036588339,
        0.774596669241483377035853079956479922166584341058318165317514,
        0.836660026534075547978172025785187489392815369298672199811191,
        0.894427190999915878563669467492510494176247343844610289708358,
        0.948683298050513799599668063329815560115866541797565048057251,
        1,
        1.414213562373095048801688724209698078569671875376948073176679,
        1.732050807568877293527446341505872366942805253810380628055806,
        2,
        2.236067977499789696409173668731276235440618359611525724270897,
        3.162277660168379331998893544432718533719555139325216826857504,
        7.071067811865475244008443621048490392848359376884740365883398,
        10,
        22.36067977499789696409173668731276235440618359611525724270897,
        31.62277660168379331998893544432718533719555139325216826857504,
        100

    };

    pd_shared3p T[[1]] c (20);

    c = sqrt(a);
    T[[1]] d (20);
    T[[1]] temp(20) = b;

    d = declassify(c) - b;

    for(uint i = 0; i < 20;++i){
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

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
PrecisionTest<T> test_erf(T data){
    T max_absolute = 0, max_relative = 0;
    pd_shared3p T[[1]] a (12) = {
        -1,
        -0.8,
        -0.6,
        -0.4,
        -0.2,
        -0.1,
        0.1,
        0.2,
        0.4,
        0.6,
        0.8,
        1
    };

    T[[1]] b (12) = {
        -0.84270079294971486934122063508260925929606699796630290845993,
        -0.74210096470766048616711058650294587731768957991470872688213,
        -0.60385609084792592256262243605672320656427336480009790555297,
        -0.42839235504666845510360384532017244412186292852259038349508,
        -0.22270258921047845414013900680014381638826903843022760562093,
        -0.11246291601828489220327507174396838322169629915970254753449,
        0.112462916018284892203275071743968383221696299159702547534494,
        0.222702589210478454140139006800143816388269038430227605620935,
        0.428392355046668455103603845320172444121862928522590383495086,
        0.603856090847925922562622436056723206564273364800097905552970,
        0.742100964707660486167110586502945877317689579914708726882135,
        0.842700792949714869341220635082609259296066997966302908459937
    };

    pd_shared3p T[[1]] c (12);

    c = erf(a);
    T[[1]] d (12);
    T[[1]] temp(12) = b;

    d = declassify(c) - b;

    for(uint i = 0; i < 10;++i){
        if(d[i] < 0){d[i] = -d[i];}
        if (temp[i] < 0){temp[i] = -temp[i];}
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
    string test_prefix = "Float32/64 erf precision";
    {
        PrecisionTest<float32> rv = test_erf(0::float32);
        test(test_prefix, rv);
    }
    {
        PrecisionTest<float64> rv = test_erf(0::float64);
        test(test_prefix, rv);
    }

    test_report();
}

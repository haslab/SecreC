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
PrecisionTest<T> test_exp(T data){
    T max_absolute = 0, max_relative = 0;
    pd_shared3p T[[1]] a (6) = {
        0.04346448502744411,
        2.608711404814097,
        8.850954516109905,
        5.192202509740625,
        3.804402936143337,
        0.2756185651367633
    };

    T[[1]] b (6) = {
        1.044422901002680287666610221323863320666399833403446910102462,
        13.58153846598169954780858281673407681819654520434165372046665,
        6981.049314932058041420422097243561596289098118645520226253906,
        179.8642697929510613535505964744523805752291131740651211153791,
        44.89843487592044416223236789050014681296169646353990257754926,
        1.317345286763859603539286625646646394800720727417483790997921
    };

    pd_shared3p T[[1]] c (6);

    c = exp(a);
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
    string test_prefix = "Float32/64 exp precision";
    {
        PrecisionTest<float32> rv = test_exp(0::float32);
        test(test_prefix, rv);
    }
    {
        PrecisionTest<float64> rv = test_exp(0::float64);
        test(test_prefix, rv);
    }

    test_report();
}

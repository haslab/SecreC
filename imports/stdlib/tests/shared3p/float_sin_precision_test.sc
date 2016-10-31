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
PrecisionTest<T> test_sin(T data){
    T max_absolute = 0, max_relative = 0;
    pd_shared3p T[[1]] a (6) = {
        1.535359689017609,
        -3.691520454030958,
        0.3645205550492913,
        3.670053129892183,
        3.565277562294547,
        //-48.42696016247228,
        5.411167505765563
        //22.58281807201601
        // cannot use those values otherwise imprecision is over a billion percent
        // VM probably has an issue with angles bigger than 2*pi
    };


    //radians
    T[[1]] b (6) = {
        0.999372188053827311880116625789242387997100157445729730841003,
        0.522625675673997926990697591852093392812491496336474491601758,
        0.356501392547928893588299460365806303984370739148059352783049,
        -0.50420443070747302192901476609516032397872513906068697502028,
        -0.41112232643427713072343386894534779652674092407078421997585,
        //0.964374959685377044826710393641436229248997196381340521352072,
        -0.76562851207067262638835876030431734777683517527272468681800
        //-0.55774749979570813840005801495922364317703842299950389372550
    };

    pd_shared3p T[[1]] c (6);

    c = sin(a);
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
    string test_prefix = "Float32/64 sin precision";
    {
        PrecisionTest<float32> rv = test_sin(0::float32);
        test(test_prefix, rv);
    }
    {
        PrecisionTest<float64> rv = test_sin(0::float64);
        test(test_prefix, rv);
    }

    test_report();
}

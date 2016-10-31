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
    pd_shared3p T[[1]] a (20) = {
        -10,
        -8,
        -6,
        -4,
        -2,
        -1,
        -0.8,
        -0.6,
        -0.4,
        -0.2,
        0.2,
        0.4,
        0.6,
        0.8,
        1,
        2,
        4,
        6,
        8,
        10
    };


    T[[1]] b (20) = {
        0.000045399929762484851535591515560550610237918088866564969259,
        0.000335462627902511838821389125780861019310900133720319360544,
        0.002478752176666358423045167430816667891506479585533945050878,
        0.018315638888734180293718021273241242211912067553475594769599,
        0.135335283236612691893999494972484403407631545909575881468158,
        0.367879441171442321595523770161460867445811131031767834507836,
        0.449328964117221591430102385015562795934214941272184490897989,
        0.548811636094026432628458917232567875332311956690628066980712,
        0.670320046035639300744432925147826071936980925210812199888910,
        0.818730753077981858669935508619039424358591256269015672478028,
        1.221402758160169833921071994639674170307580941520503641273425,
        1.491824697641270317824852952837222280643282773937425281595633,
        1.822118800390508974875367668162864513382238808546435386320547,
        2.225540928492467604579537531395076757053634135048484596118583,
        2.718281828459045235360287471352662497757247093699959574966967,
        7.389056098930650227230427460575007813180315570551847324087127,
        54.59815003314423907811026120286087840279073703861406872582659,
        403.4287934927351226083871805433882796058998973571292026139671,
        2980.957987041728274743592099452888673755967939132835702208963,
        22026.46579480671651695790064528424436635351261855678107423542
    };

    pd_shared3p T[[1]] c (20);

    c = exp(a);
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

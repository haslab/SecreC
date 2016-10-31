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
    pd_shared3p T[[1]] a (20) = {-6,-5,-4,-3,-2,-1,-0.8,-0.6,-0.4,-0.2,0.2,0.4,0.6,0.8,1,2,3,4,5,6};


    T[[1]] b (20) = {
        0.279415498198925872811555446611894759627994864318204318483351,
        0.958924274663138468893154406155993973352461543964601778131672,
        0.756802495307928251372639094511829094135912887336472571485416,
        -0.14112000805986722210074480280811027984693326425226558415188,
        -0.90929742682568169539601986591174484270225497144789026837897,
        -0.84147098480789650665250232163029899962256306079837106567275,
        -0.71735609089952276162717461058138536619278523779142282098968,
        -0.56464247339503535720094544565865790710988808499415177102426,
        -0.38941834230865049166631175679570526459306018344395889511584,
        -0.19866933079506121545941262711838975037020672954020540398639,
        0.198669330795061215459412627118389750370206729540205403986395,
        0.389418342308650491666311756795705264593060183443958895115848,
        0.564642473395035357200945445658657907109888084994151771024265,
        0.717356090899522761627174610581385366192785237791422820989682,
        0.841470984807896506652502321630298999622563060798371065672751,
        0.909297426825681695396019865911744842702254971447890268378973,
        0.141120008059867222100744802808110279846933264252265584151882,
        -0.75680249530792825137263909451182909413591288733647257148541,
        -0.95892427466313846889315440615599397335246154396460177813167,
        -0.27941549819892587281155544661189475962799486431820431848335
    };

    pd_shared3p T[[1]] c (20);

    c = sin(a);
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

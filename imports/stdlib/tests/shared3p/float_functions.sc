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

module float_shared3p;

import stdlib;
import shared3p;
import test_utility;

domain pd_shared3p shared3p;

template<type T>
bool test_inv(T data){
    pd_shared3p T temp = 71.504533269388;
    pd_shared3p T result = inv(temp);
    pd_shared3p T scalar = 0.013985127295811784800214762835242144289506641965459514772424;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 0.7164111850802378;
    result = inv(temp);
    scalar = 1.395846436830826912300169456980548765643135686459277164156807;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = -30.40014777649985;
    result = inv(temp);
    scalar = -0.03289457693929460080651200035097043130322734092728779416961;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 29.14530926682408;
    result = inv(temp);
    scalar = 0.034310838524478916201483940525109990585888448227179674751609;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = -3.490183819544366;
    result = inv(temp);
    scalar = -0.28651786029153824876652907594949790036880450793466800071530;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    return true;
}

template<type T>
bool test_sqrt(T data){
    pd_shared3p T temp = 2;
    pd_shared3p T result = sqrt(temp);
    pd_shared3p T scalar = 1.414213562373095048801688724209698078569671875376948073176679;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 0.1;
    result = sqrt(temp);
    scalar = 0.31622776601683793319988935444327185337195551393252168268575048527925;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 0.2520680438028037;
    result = sqrt(temp);
    scalar = 0.5020637845959452;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 1.612666674980346;
    result = sqrt(temp);
    scalar = 1.269908136433634;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 10.74761750718821;
    result = sqrt(temp);
    scalar = 3.278355915270368;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 20.04875104760001;
    result = sqrt(temp);
    scalar = 4.477583170372161;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 7.058176148791843;
    result = sqrt(temp);
    scalar = 2.656722821220129;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    return true;
}

template<type T>
bool test_sin(T data){
    pd_shared3p T temp = 2;
    pd_shared3p T result = sin(temp);
    pd_shared3p T scalar = 0.909297426825681695396019865911744842702254971447890268378973;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = -2.591158833266627;
    result = sin(temp);
    scalar = -0.52305702219783894117435782687190587225808918400896283367238;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 2.025973655340153;
    result = sin(temp);
    scalar = 0.898183084843072890962281088679208335666350830433122388024890;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 0.05077053980093406;
    result = sin(temp);
    scalar = 0.050748731184247275247749273261571169824032377058418668001890;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 0.1560146834375741;
    result = sin(temp);
    scalar = 0.155382538582007151395195349866599909099990588265240553195932;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    return true;
}

template<type T>
bool test_ln(T data){
    pd_shared3p T temp = 2;
    pd_shared3p T result = ln(temp);
    pd_shared3p T scalar = 0.693147180559945309417232121458176568075500134360255254120680;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 19.37143870633351;
    result = ln(temp);
    scalar = 2.963799749639153065081482086356157440864483133716907784025809;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 8.01355095537729;
    result = ln(temp);
    scalar = 2.081133978123145341432434262591867363796748211946731326304016;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    return true;
}

template<type T>
bool test_exp(T data){
    pd_shared3p T temp = 4.730296322569438;
    pd_shared3p T result = exp(temp);
    pd_shared3p T scalar = 113.3291393553677043956554206064549029386122262400736381482935;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 2.217653729055856;
    result = exp(temp);
    scalar = 9.185753296309464529002373228208324050320999152365389053363533;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = -4.943499161180602;
    result = exp(temp);
    scalar = 0.007129607029295815232567517484547170649184452431423495644665;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 0.5891664913460597;
    result = exp(temp);
    scalar = 1.802485401916403216424300563519871037244366347890180754747299;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = -3.374143516929145;
    result = exp(temp);
    scalar = 0.034247438104877426515655546479021676807903158395020214273423;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    return true;
}

template<type T>
bool test_erf(T data){
    pd_shared3p T temp = 4.730296322569438;
    pd_shared3p T result = erf(temp);
    pd_shared3p T scalar = 0.99999999997762938171481719714979256601818505390828472741213;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 2.217653729055856;
    result = erf(temp);
    scalar = 0.998288685557728913422078693320809998053921317555840630675942;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = -4.943499161180602;
    result = erf(temp);
    scalar = -0.9999999999972738428825420423541876431404271162216781611631;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = 0.5891664913460597;
    result = erf(temp);
    scalar = 0.595272141363452952222309063225099090494893694719914124265248;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    temp = -3.374143516929145;
    result = erf(temp);
    scalar = -0.99999817376529374239271282956126531878392026171113368123543;
    if (!declassify(isNegligible(scalar - result)))
        return false;

    return true;
}

void main(){
    string test_prefix = "Inversion";
    test(test_prefix, test_inv(0::float32), 0::float32);
    test(test_prefix, test_inv(0::float64), 0::float64);

    test_prefix = "Square root";
    test(test_prefix, test_sqrt(0::float32), 0::float32);
    test(test_prefix, test_sqrt(0::float64), 0::float64);

    test_prefix = "Sin test";
    test(test_prefix, test_sin(0::float32), 0::float32);
    test(test_prefix, test_sin(0::float64), 0::float64);

    test_prefix = "Ln test";
    test(test_prefix, test_ln(0::float32), 0::float32);
    test(test_prefix, test_ln(0::float64), 0::float64);

    test_prefix = "Exp test";
    test(test_prefix, test_exp(0::float32), 0::float32);
    test(test_prefix, test_exp(0::float64), 0::float64);

    test_prefix = "Erf test";
    test(test_prefix, test_erf(0::float32), 0::float32);
    test(test_prefix, test_erf(0::float64), 0::float64);

    test_report();
}

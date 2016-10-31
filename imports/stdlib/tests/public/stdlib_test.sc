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
import test_utility;
import test_utility_random;

template<type T>
bool test_flattening(T data) {
    bool result = true;
    T[[2]] temp (6,6);
    temp = randomize(temp);
    T[[2]] object = temp;
    T[[1]] vec = flatten(object);
    for (uint i = 0; i < shape(object)[0];++i) {
        for (uint j = 0; j < shape(object)[1];++j) {
            if (object[i,j] != vec[(6*i + j)]) {
                result = false;
                break;
            }
        }
        if (!result) {
            break;
        }
    }

    return result;
}

bool test_any() {
    bool result = true;
    bool[[1]] vec (6) = {true,false,true,true,false,false};
    bool[[1]] vec2 (6) = {true,false,false,false,false,false};
    bool[[1]] vec3 (6) = true;
    bool[[1]] vec4 (6) = false;
    bool control = any(vec);
    if (control != true) {result = false;}

    control = any(vec2);
    if (control != true) {result = false;}

    control = any(vec3);
    if (control != true) {result = false;}

    control = any(vec4);
    if (control != false) {result = false;}

    return result;
}

bool test_any2() {
    bool result = true;
    bool[[1]] vec (6) = {true,false,true,true,false,false};
    bool[[1]] vec2 (6) = {true,false,false,false,false,true};
    bool[[1]] vec3 (6) = true;
    bool[[1]] vec4 (6) = false;
    bool[[1]] control = any(vec,2::uint);
    if (all(control) != true) {result = false;}

    control = any(vec2,2::uint);
    if (all(control) != true) {result = false;}

    control = any(vec3,2::uint);
    if (all(control) != true) {result = false;}

    control = any(vec4,2::uint);
    if (all(control) != false) {result = false;}

    return result;
}



bool test_all() {
    bool result = true;
    bool[[1]] vec (6) = {true,false,true,true,false,false};
    bool[[1]] vec2 (6) = {true,true,true,false,true,true};
    bool[[1]] vec3 (6) = true;
    bool[[1]] vec4 (6) = false;
    bool control = all(vec);
    if (control == true) {result = false;}

    control = all(vec2);
    if (control == true) {result = false;}

    control = all(vec3);
    if (control != true) {result = false;}

    control = all(vec4);
    if (control == true) {result = false;}

    return result;
}

bool test_all2() {
    bool result = true;
    bool[[1]] vec (6) = {true,false,true,true,false,false};
    bool[[1]] vec2 (6) = {false,true,true,false,true,true};
    bool[[1]] vec3 (6) = true;
    bool[[1]] vec4 (6) = false;
    bool[[1]] control = all(vec,2::uint);
    if (any(control) == true) {result = false;}

    control = all(vec2,2::uint);
    if (any(control) == true) {result = false;}

    control = all(vec3,2::uint);
    if (any(control) == false) {result = false;}

    control = all(vec4,2::uint);
    if (any(control) == true) {result = false;}

    return result;
}

template<type T>
bool test_sum(T data) {
    T[[1]] temp (10);
    T[[1]] vec = randomize(temp);
    T result = sum(vec);
    T control = 0;
    for (uint i = 0; i < size(vec);++i) {
        control += vec[i];
    }

    return all(control == result);
}

bool test_sum(bool data) {
    bool[[1]] temp (10);
    bool[[1]] vec = randomize(temp);
    uint result = sum(vec);
    uint control = 0;
    for (uint i = 0; i < size(vec);++i) {
        control += (uint)vec[i];
    }

    return all(control == result);
}

template<type T>
bool test_sum2(T data) {
    T[[1]] temp (10);
    T[[1]] vec = randomize(temp);
    T[[1]] result = sum(vec,2::uint);
    uint startingIndex = 0;
    uint endIndex = size(vec) / 2;
    T[[1]] control (2)= 0;
    for (uint i = 0;i < 2;++i) {
        for (uint j = startingIndex;j < endIndex;++j) {
            control[i] += vec[j];
        }
        startingIndex = 5;
        endIndex = 10;
    }

    return all(control == result);
}

bool test_sum2(bool data) {
    bool[[1]] temp (10);
    bool[[1]] vec = randomize(temp);
    uint[[1]] result = sum(vec,2::uint);
    uint startingIndex = 0;
    uint endIndex = size(vec) / 2;
    uint[[1]] control (2)= 0;
    for (uint i = 0;i < 2;++i) {
        for (uint j = startingIndex;j < endIndex;++j) {
            control[i] += (uint)vec[j];
        }
        startingIndex = 5;
        endIndex = 10;
    }

    return all(control == result);
}

template<type T>
bool test_product(T data) {
    T[[1]] temp (10);
    T[[1]] vec = randomize(temp);
    T result = product(vec);
    T control = 1;
    for (uint i = 0; i < size(vec);++i) {
        control *= vec[i];
    }

    return control == result;
}

template<type T>
bool test_product2(T data) {
    T[[1]] temp (10);
    T[[1]] vec = randomize(temp);
    T[[1]] result = product(vec,2::uint);
    T[[1]] control (2)= 1;
    uint startingIndex = 0;
    uint endIndex = size(vec) / 2;
    for (uint i = 0; i < 2;++i) {
        for (uint j = startingIndex; j < endIndex; ++j) {
            control[i] *= vec[j];
        }
        startingIndex += size(vec) / 2;
        endIndex += size(vec) / 2;
    }

    return all(control == result);
}

template<type T>
bool test_min(T data) {
    T[[1]] temp (25);
    T[[1]] vec = randomize(temp);
    T result = min(vec);
    T control = 0;
    for (uint i = 0; i < size(vec);++i) {
        if (i == 0) {
            control = vec[i];
        } else {
            if (vec[i] < control) {
                control = vec[i];
            }
        }
    }

    return control == result;
}

template<type T>
bool test_min2(T data) {
    T[[1]] temp (25);
    T[[1]] vec = randomize(temp);
    T[[1]] vec2 = randomize(temp);
    T[[1]] result = min(vec,vec2);
    T[[1]] control (25);
    for (uint i = 0; i < size(vec);++i) {
        if (vec[i] < vec2[i]) {
            control[i] = vec[i];
        } else {
            control[i] = vec2[i];
        }
    }

    return all(control == result);
}

template<type T>
bool test_min3(T data) {
    T[[1]] temp (20);
    T[[1]] vec = randomize(temp);
    T[[1]] result = min(vec,2::uint);
    T[[1]] control (2);
    uint startingIndex = 0;
    uint endIndex = 10;
    for (uint j = 0; j < 2;++j) {
        for (uint i = startingIndex; i < endIndex;++i) {
            if (i == startingIndex) {
                control[j] = vec[i];
            } else {
                if (vec[i] < control[j]) {
                    control[j] = vec[i];
                }
            }
        }
        startingIndex += 10;
        endIndex += 10;
    }

    return all(control == result);
}

template<type T>
bool test_max(T data) {
    T[[1]] temp (25);
    T[[1]] vec = randomize(temp);
    T result = max(vec);
    T control = 0;
    for (uint i = 0; i < size(vec);++i) {
        if (vec[i] > control) {
            control = vec[i];
        }
    }

    return control == result;
}

template<type T>
bool test_max2(T data) {
    T[[1]] temp (25);
    T[[1]] vec = randomize(temp);
    T[[1]] vec2 = randomize(temp);
    T[[1]] result = max(vec,vec2);
    T[[1]] control (25);
    for (uint i = 0; i < size(vec);++i) {
        if (vec[i] > vec2[i]) {
            control[i] = vec[i];
        } else {
            control[i] = vec2[i];
        }
    }

    return all(control == result);
}

template<type T>
bool test_max3(T data) {
    T[[1]] temp (20);
    T[[1]] vec = randomize(temp);
    T[[1]] result = max(vec,2::uint);
    T[[1]] control (2);
    uint startingIndex = 0;
    uint endIndex = 10;
    for (uint j = 0; j < 2;++j) {
        for (uint i = startingIndex; i < endIndex;++i) {
            if (i == startingIndex) {
                control[j] = vec[i];
            } else {
                if (vec[i] > control[j]) {
                    control[j] = vec[i];
                }
            }
        }
        startingIndex += 10;
        endIndex += 10;
    }

    return all(control == result);
}

void main() {
    string test_prefix = "Flattening utility";
    test(test_prefix, test_flattening(false), false);
    test(test_prefix, test_flattening(0::uint8), 0::uint8);
    test(test_prefix, test_flattening(0::uint16), 0::uint16);
    test(test_prefix, test_flattening(0::uint32), 0::uint32);
    test(test_prefix, test_flattening(0::uint64), 0::uint64);
    test(test_prefix, test_flattening(0::int8), 0::uint8);
    test(test_prefix, test_flattening(0::int16), 0::int16);
    test(test_prefix, test_flattening(0::int32), 0::int32);
    test(test_prefix, test_flattening(0::int64), 0::int64);

    test_prefix = "All and Any functions";
    test(test_prefix, test_any());
    test(test_prefix, test_all());

    test_prefix = "All(parts) and Any(parts) functions";
    test(test_prefix, test_any2());
    test(test_prefix, test_all2());

    test_prefix = "Sum";
    test(test_prefix, test_sum(false), false);
    test(test_prefix, test_sum(0::uint8), 0::uint8);
    test(test_prefix, test_sum(0::uint16), 0::uint16);
    test(test_prefix, test_sum(0::uint32), 0::uint32);
    test(test_prefix, test_sum(0::uint64), 0::uint64);
    test(test_prefix, test_sum(0::int8), 0::uint8);
    test(test_prefix, test_sum(0::int16), 0::int16);
    test(test_prefix, test_sum(0::int32), 0::int32);
    test(test_prefix, test_sum(0::int64), 0::int64);

    test_prefix = "Sum (2)";
    test(test_prefix, test_sum2(false), false);
    test(test_prefix, test_sum2(0::uint8), 0::uint8);
    test(test_prefix, test_sum2(0::uint16), 0::uint16);
    test(test_prefix, test_sum2(0::uint32), 0::uint32);
    test(test_prefix, test_sum2(0::uint64), 0::uint64);
    test(test_prefix, test_sum2(0::int8), 0::uint8);
    test(test_prefix, test_sum2(0::int16), 0::int16);
    test(test_prefix, test_sum2(0::int32), 0::int32);
    test(test_prefix, test_sum2(0::int64), 0::int64);

    test_prefix = "Product";
    test(test_prefix, test_product(0::uint8), 0::uint8);
    test(test_prefix, test_product(0::uint16), 0::uint16);
    test(test_prefix, test_product(0::uint32), 0::uint32);
    test(test_prefix, test_product(0::uint64), 0::uint64);
    test(test_prefix, test_product(0::int8), 0::uint8);
    test(test_prefix, test_product(0::int16), 0::int16);
    test(test_prefix, test_product(0::int32), 0::int32);
    test(test_prefix, test_product(0::int64), 0::int64);

    test_prefix = "Product (2)";
    test(test_prefix, test_product2(0::uint8), 0::uint8);
    test(test_prefix, test_product2(0::uint16), 0::uint16);
    test(test_prefix, test_product2(0::uint32), 0::uint32);
    test(test_prefix, test_product2(0::uint64), 0::uint64);
    test(test_prefix, test_product2(0::int8), 0::uint8);
    test(test_prefix, test_product2(0::int16), 0::int16);
    test(test_prefix, test_product2(0::int32), 0::int32);
    test(test_prefix, test_product2(0::int64), 0::int64);

    test_prefix = "Max";
    test(test_prefix, test_max(0::uint8), 0::uint8);
    test(test_prefix, test_max(0::uint16), 0::uint16);
    test(test_prefix, test_max(0::uint32), 0::uint32);
    test(test_prefix, test_max(0::uint64), 0::uint64);
    test(test_prefix, test_max(0::int8), 0::uint8);
    test(test_prefix, test_max(0::int16), 0::int16);
    test(test_prefix, test_max(0::int32), 0::int32);
    test(test_prefix, test_max(0::int64), 0::int64);

    test_prefix = "Max pointwise";
    test(test_prefix, test_max2(0::uint8), 0::uint8);
    test(test_prefix, test_max2(0::uint16), 0::uint16);
    test(test_prefix, test_max2(0::uint32), 0::uint32);
    test(test_prefix, test_max2(0::uint64), 0::uint64);
    test(test_prefix, test_max2(0::int8), 0::uint8);
    test(test_prefix, test_max2(0::int16), 0::int16);
    test(test_prefix, test_max2(0::int32), 0::int32);
    test(test_prefix, test_max2(0::int64), 0::int64);

    test_prefix = "Max (parts)";
    test(test_prefix, test_max3(0::uint8), 0::uint8);
    test(test_prefix, test_max3(0::uint16), 0::uint16);
    test(test_prefix, test_max3(0::uint32), 0::uint32);
    test(test_prefix, test_max3(0::uint64), 0::uint64);
    test(test_prefix, test_max3(0::int8), 0::uint8);
    test(test_prefix, test_max3(0::int16), 0::int16);
    test(test_prefix, test_max3(0::int32), 0::int32);
    test(test_prefix, test_max3(0::int64), 0::int64);

    test_prefix = "Min";
    test(test_prefix, test_min(0::uint8), 0::uint8);
    test(test_prefix, test_min(0::uint16), 0::uint16);
    test(test_prefix, test_min(0::uint32), 0::uint32);
    test(test_prefix, test_min(0::uint64), 0::uint64);
    test(test_prefix, test_min(0::int8), 0::uint8);
    test(test_prefix, test_min(0::int16), 0::int16);
    test(test_prefix, test_min(0::int32), 0::int32);
    test(test_prefix, test_min(0::int64), 0::int64);

    test_prefix = "Min pointwise";
    test(test_prefix, test_min2(0::uint8), 0::uint8);
    test(test_prefix, test_min2(0::uint16), 0::uint16);
    test(test_prefix, test_min2(0::uint32), 0::uint32);
    test(test_prefix, test_min2(0::uint64), 0::uint64);
    test(test_prefix, test_min2(0::int8), 0::uint8);
    test(test_prefix, test_min2(0::int16), 0::int16);
    test(test_prefix, test_min2(0::int32), 0::int32);
    test(test_prefix, test_min2(0::int64), 0::int64);

    test_prefix = "Min (parts)";
    test(test_prefix, test_min3(0::uint8), 0::uint8);
    test(test_prefix, test_min3(0::uint16), 0::uint16);
    test(test_prefix, test_min3(0::uint32), 0::uint32);
    test(test_prefix, test_min3(0::uint64), 0::uint64);
    test(test_prefix, test_min3(0::int8), 0::uint8);
    test(test_prefix, test_min3(0::int16), 0::int16);
    test(test_prefix, test_min3(0::int32), 0::int32);
    test(test_prefix, test_min3(0::int64), 0::int64);

    test_report();
}

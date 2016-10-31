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
import matrix;
import test_utility;
import test_utility_random;

bool test_unit_matrix() {
    bool [[1]] result(10) = true;
    for (uint i = 1; i < 10;++i) {
        uint[[2]] mat = unitMatrix(i);
        for (uint j = 0; j < shape(mat)[0];++j) {
            for (uint k = 0; k < shape(mat)[0];++k) {
                if (j == k) {
                    if (mat[j,k] != 1) {
                        result[i] = false;
                    }
                } else {
                    if (mat[j,k] != 0) {
                        result[i] = false;
                    }
                }
            }
        }
    }

    return all(result);
}

template<type T>
bool row_sum_test(T data) {
    T[[2]] mat (5,5);
    T[[1]] control (5);
    mat = randomize(mat);
    T[[1]] row_sums = rowSums(mat);
    for (uint i = 0; i < 5;++i) {
        control[i] = sum(mat[i,:]);
    }

    return all(row_sums == control);
}

template<type T>
bool dot_product(T data) {
    T[[1]] vec (15);
    T[[1]] vec2 (15);
    vec = randomize(vec); vec2 = randomize(vec2);
    T scalar = dotProduct(vec, vec2);
    T control = sum(vec * vec2);

    return scalar == control;
}

template<type T>
bool dot_product_matrix(T data) {
    T[[2]] mat (10,10);
    T[[2]] mat2 (10,10);
    mat = randomize(mat); mat2 = randomize(mat2);
    T[[1]] vec = dotProduct(mat, mat2);
    T[[1]] control = rowSums(mat * mat2);

    return all(vec == control);
}

template<type T>
bool cross_product(T data) {
    T[[1]] vec (3);
    T[[1]] vec2 (3);
    vec = randomize(vec); vec2 = randomize(vec2);
    T[[1]] x = vec;
    T[[1]] y = vec2;
    T[[1]] vec3 = crossProduct(vec,vec2);
    T[[1]] control (3);
    control[0] = x[1] * y[2] - x[2] * y[1];
    control[1] = x[2] * y[0] - x[0] * y[2];
    control[2] = x[0] * y[1] - x[1] * y[0];

    return all(vec3 == control);
}

template<type T>
bool cross_product_matrix(T data) {
    T[[2]] mat (3,3);
    T[[2]] mat2 (3,3);
    mat = randomize(mat); mat2 = randomize(mat2);
    T[[2]] x = mat;
    T[[2]] y = mat2;
    T[[2]] mat3 = crossProduct(mat,mat2);
    T[[2]] control (3,3);

    for (uint i = 0; i < 3; ++i) {
        control[i,:] = crossProduct(x[i,:], y[i,:]);
    }

    return all(mat3 == control);
}

template<type T>
bool mat_multiplication(T data) {
    bool [[1]] result(9) = true;
    uint i = 0;
    for (uint k = 3; k < 6;++k) {
        for (uint l = 5; l > 2;--l) {
            T[[2]] mat (k,l);
            T[[2]] mat2 (l,k);
            mat = randomize(mat); mat2 = randomize(mat2);
            T[[2]] mat3 (k,k) = matrixMultiplication(mat,mat2);
            T[[2]] control (k,k);
            for (uint i = 0; i < shape(mat3)[0];++i) {
                for (uint j = 0; j < shape(mat3)[1];++j) {
                    control[i,j] = sum(mat[i,:] * mat2[:,j]);
                }
            }

            result[i++] = all(mat3 == control);
        }
    }

    return all(result);
}

void main() {
    string test_prefix = "Unit matrix";
    test(test_prefix, test_unit_matrix());

    test_prefix = "Matrix row sums";
    test(test_prefix, row_sum_test(0::uint8), 0::uint8);
    test(test_prefix, row_sum_test(0::uint16), 0::uint16);
    test(test_prefix, row_sum_test(0::uint32), 0::uint32);
    test(test_prefix, row_sum_test(0::uint64), 0::uint64);
    test(test_prefix, row_sum_test(0::int8), 0::int8);
    test(test_prefix, row_sum_test(0::int16), 0::int16);
    test(test_prefix, row_sum_test(0::int32), 0::int32);
    test(test_prefix, row_sum_test(0::int64), 0::int64);

    // NOTE: Testing matrix colSums is useless because colSums consists of 2
    // functions: transpose and rowSums which have already been tested

    test_prefix = "Dot product for vectors";
    test(test_prefix, dot_product(0::uint8), 0::uint8);
    test(test_prefix, dot_product(0::uint16), 0::uint16);
    test(test_prefix, dot_product(0::uint32), 0::uint32);
    test(test_prefix, dot_product(0::uint64), 0::uint64);
    test(test_prefix, dot_product(0::int8), 0::int8);
    test(test_prefix, dot_product(0::int16), 0::int16);
    test(test_prefix, dot_product(0::int32), 0::int32);
    test(test_prefix, dot_product(0::int64), 0::int64);

    test_prefix = "Dot product for matrices";
    test(test_prefix, dot_product_matrix(0::uint8), 0::uint8);
    test(test_prefix, dot_product_matrix(0::uint16), 0::uint16);
    test(test_prefix, dot_product_matrix(0::uint32), 0::uint32);
    test(test_prefix, dot_product_matrix(0::uint64), 0::uint64);
    test(test_prefix, dot_product_matrix(0::int8), 0::int8);
    test(test_prefix, dot_product_matrix(0::int16), 0::int16);
    test(test_prefix, dot_product_matrix(0::int32), 0::int32);
    test(test_prefix, dot_product_matrix(0::int64), 0::int64);

    test_prefix = "cross product for vectors";
    test(test_prefix, cross_product(0::int8), 0::int8);
    test(test_prefix, cross_product(0::int16), 0::int16);
    test(test_prefix, cross_product(0::int32), 0::int32);
    test(test_prefix, cross_product(0::int64), 0::int64);

    test_prefix = "cross product for matrices";
    test(test_prefix, cross_product_matrix(0::int8), 0::int8);
    test(test_prefix, cross_product_matrix(0::int16), 0::int16);
    test(test_prefix, cross_product_matrix(0::int32), 0::int32);
    test(test_prefix, cross_product_matrix(0::int64), 0::int64);

    test_prefix = "Matrix multiplication";
    test(test_prefix, mat_multiplication(0::uint8), 0::uint8);
    test(test_prefix, mat_multiplication(0::uint16), 0::uint16);
    test(test_prefix, mat_multiplication(0::uint32), 0::uint32);
    test(test_prefix, mat_multiplication(0::uint64), 0::uint64);
    test(test_prefix, mat_multiplication(0::int8), 0::int8);
    test(test_prefix, mat_multiplication(0::int16), 0::int16);
    test(test_prefix, mat_multiplication(0::int32), 0::int32);
    test(test_prefix, mat_multiplication(0::int64), 0::int64);

    test_report();
}

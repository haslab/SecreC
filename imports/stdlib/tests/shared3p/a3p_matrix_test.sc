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

import matrix;
import stdlib;
import shared3p;
import shared3p_matrix;
import shared3p_random;
import test_utility;

domain pd_shared3p shared3p;

template<type T>
bool row_sum_test(T data){
    pd_shared3p T[[2]] mat (5,5);
    T[[1]] control (5);
    mat = randomize(mat);
    pd_shared3p T[[1]] row_sums = rowSums(mat);
    for(uint i = 0; i < 5;++i){
        control[i] = sum(declassify(mat[i,:]));
    }

    return all(declassify(row_sums) == control);
}

template<type T>
bool dot_product(T data){
    pd_shared3p T[[1]] vec (15);
    pd_shared3p T[[1]] vec2 (15);
    vec = randomize(vec); vec2 = randomize(vec2);
    pd_shared3p T scalar = dotProduct(vec,vec2);
    T control = sum(declassify(vec) * declassify(vec2));

    return declassify(scalar) == control;
}

template<type T>
bool dot_product_matrix(T data){
    pd_shared3p T[[2]] mat (10,10);
    pd_shared3p T[[2]] mat2 (10,10);
    mat = randomize(mat); mat2 = randomize(mat2);
    pd_shared3p T[[1]] vec = dotProduct(mat,mat2);
    T[[1]] control = rowSums(declassify(mat) * declassify(mat2));

    return all(declassify(vec) == control);
}

template<type T>
bool cross_product(T data){
    pd_shared3p T[[1]] vec (3);
    pd_shared3p T[[1]] vec2 (3);
    vec = randomize(vec); vec2 = randomize(vec2);
    T[[1]] x = declassify(vec);
    T[[1]] y = declassify(vec2);
    pd_shared3p T[[1]] vec3 = crossProduct(vec,vec2);
    T[[1]] control (3);
    control[0] = x[1] * y[2] - x[2] * y[1];
    control[1] = x[2] * y[0] - x[0] * y[2];
    control[2] = x[0] * y[1] - x[1] * y[0];

    return all(declassify(vec3) == control);
}

template<type T>
bool cross_product_matrix(T data){
    pd_shared3p T[[2]] mat (3,3);
    pd_shared3p T[[2]] mat2 (3,3);
    mat = randomize(mat); mat2 = randomize(mat2);
    T[[2]] x = declassify(mat);
    T[[2]] y = declassify(mat2);
    pd_shared3p T[[2]] mat3 = crossProduct(mat,mat2);
    T[[2]] control (3,3);

    for (uint i = 0; i < 3; ++i){
        control[i,:] = crossProduct(x[i,:], y[i,:]);
    }

    return all(declassify(mat3) == control);
}

template<type T>
bool mat_multiplication(T data){
    bool [[1]] result (9); uint i = 0;
    for(uint k = 3; k < 6;++k){
        for(uint l = 5; l > 2;--l){
            pd_shared3p T[[2]] mat (k,l);
            pd_shared3p T[[2]] mat2 (l,k);
            mat = randomize(mat); mat2 = randomize(mat2);
            pd_shared3p T[[2]] mat3 (k,k) = matrixMultiplication(mat,mat2);
            T[[2]] control (k,k);
            T[[2]] matb = declassify(mat);
            T[[2]] mat2b = declassify(mat2);
            for(uint i = 0; i < shape(declassify(mat3))[0];++i){
                for(uint j = 0; j < shape(declassify(mat3))[1];++j){
                    control[i,j] = sum(matb[i,:] * mat2b[:,j]);
                }
            }
            result[i++] = all(declassify(mat3) == control);
        }
    }

    return all(result);
}

template<type T>
bool diag_mat_multiplication(T data){
    bool [[1]] result(9); uint i = 0;
    for(uint k = 3; k < 6;++k){
        for(uint l = 5; l > 2;--l){
            pd_shared3p T[[2]] mat (k,l);
            pd_shared3p T[[2]] mat2 (l,l);
            mat = randomize(mat); mat2 = randomize(mat2);
            for(uint i = 0; i < shape(declassify(mat2))[0]; ++i){
                for(uint j = 0; j < shape(declassify(mat2))[1]; ++j){
                    if(i != j){
                        mat2[i,j] = 0;
                    }
                }
            }
            T[[2]] matb = declassify(mat);
            T[[2]] mat2b = declassify(mat2);
            pd_shared3p T[[2]] mat3 (k,l) = diagMatrixMultiplication(mat,mat2);
            T[[2]] control (k,l);
            for(uint i = 0; i < k;++i){
                for(uint j = 0; j < l;++j){
                    control[i,j] = matb[i,j] * mat2b[j,j];
                }

            }
            result[i++] = all(control == declassify(mat3));
        }
    }

    return all(result);
}

template<type T>
bool mat3D_multiplication(T data){
    bool [[1]] result(9); uint i = 0;
    for(uint k = 3; k < 6;++k){
        for(uint l = 5; l > 2;--l){
            pd_shared3p T[[3]] mat (3,k,l);
            pd_shared3p T[[3]] mat2 (3,l,k);
            mat = randomize(mat); mat2 = randomize(mat2);
            pd_shared3p T[[3]] mat3 (3,k,k) = matrixMultiplication(mat,mat2);
            T[[3]] control (3,k,k);
            T[[3]] matb = declassify(mat);
            T[[3]] mat2b = declassify(mat2);
            for(uint h = 0; h < shape(mat3)[0];++h){
                for(uint i = 0; i < shape(declassify(mat3))[1];++i){
                    for(uint j = 0; j < shape(declassify(mat3))[2];++j){
                        control[h,i,j] = sum(matb[h,i,:] * mat2b[h,:,j]);
                    }
                }
            }
            result[i++] = all(declassify(mat3) == control);
        }
    }

    return all(result);
}

template<type T>
bool diag3D_mat_multiplication(T data){
    bool [[1]] result(9); uint i = 0;
    for(uint k = 3; k < 6;++k){
        for(uint l = 5; l > 2;--l){
            pd_shared3p T[[3]] mat (3,k,l);
            pd_shared3p T[[3]] mat2 (3,l,l);
            mat = randomize(mat); mat2 = randomize(mat2);
            for(uint h = 0; h < shape(declassify(mat2))[0];++h){
                for(uint i = 0; i < shape(declassify(mat2))[1]; ++i){
                    for(uint j = 0; j < shape(declassify(mat2))[2]; ++j){
                        if(i != j){
                            mat2[h,i,j] = 0;
                        }
                    }
                }
            }
            pd_shared3p T[[3]] mat3 (3,k,l) = diagMatrixMultiplication(mat,mat2);
            T[[3]] control (3,k,l);
            T[[3]] matb = declassify(mat);
            T[[3]] mat2b = declassify(mat2);
            for(uint h = 0; h < shape(declassify(mat))[0];++h){
                for(uint i = 0; i < shape(declassify(mat))[1];++i){
                    for(uint j = 0; j < shape(declassify(mat))[2];++j){
                        control[h,i,j] = matb[h,i,j] * mat2b[h,j,j];
                    }
                }
            }
            result[i++] = all(control == declassify(mat3));
        }
    }

    return all(result);
}

void main(){
    string test_prefix = "Matrix row sums";
    test(test_prefix, row_sum_test(0::uint8), 0::uint8);
    test(test_prefix, row_sum_test(0::uint16), 0::uint16);
    test(test_prefix, row_sum_test(0::uint32), 0::uint32);
    test(test_prefix, row_sum_test(0::uint64), 0::uint64);
    test(test_prefix, row_sum_test(0::int8), 0::int8);
    test(test_prefix, row_sum_test(0::int16), 0::int16);
    test(test_prefix, row_sum_test(0::int32), 0::int32);
    test(test_prefix, row_sum_test(0::int64), 0::int64);

    test_prefix = "Matrix dotproduct for vectors";
    test(test_prefix, dot_product(0::uint8), 0::uint8);
    test(test_prefix, dot_product(0::uint16), 0::uint16);
    test(test_prefix, dot_product(0::uint32), 0::uint32);
    test(test_prefix, dot_product(0::uint64), 0::uint64);
    test(test_prefix, dot_product(0::int8), 0::int8);
    test(test_prefix, dot_product(0::int16), 0::int16);
    test(test_prefix, dot_product(0::int32), 0::int32);
    test(test_prefix, dot_product(0::int64), 0::int64);

    test_prefix = "Matrix dotproduct for matrices";
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

    test_prefix = "2D Matrix multiplication";
    test(test_prefix, mat_multiplication(0::uint8), 0::uint8);
    test(test_prefix, mat_multiplication(0::uint16), 0::uint16);
    test(test_prefix, mat_multiplication(0::uint32), 0::uint32);
    test(test_prefix, mat_multiplication(0::uint64), 0::uint64);
    test(test_prefix, mat_multiplication(0::int8), 0::int8);
    test(test_prefix, mat_multiplication(0::int16), 0::int16);
    test(test_prefix, mat_multiplication(0::int32), 0::int32);
    test(test_prefix, mat_multiplication(0::int64), 0::int64);

    test_prefix = "2D Diagonal matrix multiplication";
    test(test_prefix, diag_mat_multiplication(0::uint8), 0::uint8);
    test(test_prefix, diag_mat_multiplication(0::uint16), 0::uint16);
    test(test_prefix, diag_mat_multiplication(0::uint32), 0::uint32);
    test(test_prefix, diag_mat_multiplication(0::uint64), 0::uint64);
    test(test_prefix, diag_mat_multiplication(0::int8), 0::int8);
    test(test_prefix, diag_mat_multiplication(0::int16), 0::int16);
    test(test_prefix, diag_mat_multiplication(0::int32), 0::int32);
    test(test_prefix, diag_mat_multiplication(0::int64), 0::int64);

    test_prefix = "3D Matrix multiplication";
    test(test_prefix, mat3D_multiplication(0::uint8), 0::uint8);
    test(test_prefix, mat3D_multiplication(0::uint16), 0::uint16);
    test(test_prefix, mat3D_multiplication(0::uint32), 0::uint32);
    test(test_prefix, mat3D_multiplication(0::uint64), 0::uint64);
    test(test_prefix, mat3D_multiplication(0::int8), 0::int8);
    test(test_prefix, mat3D_multiplication(0::int16), 0::int16);
    test(test_prefix, mat3D_multiplication(0::int32), 0::int32);
    test(test_prefix, mat3D_multiplication(0::int64), 0::int64);

    test_prefix = "3D Diagonal matrix multiplication";
    test(test_prefix, diag3D_mat_multiplication(0::uint8), 0::uint8);
    test(test_prefix, diag3D_mat_multiplication(0::uint16), 0::uint16);
    test(test_prefix, diag3D_mat_multiplication(0::uint32), 0::uint32);
    test(test_prefix, diag3D_mat_multiplication(0::uint64), 0::uint64);
    test(test_prefix, diag3D_mat_multiplication(0::int8), 0::int8);
    test(test_prefix, diag3D_mat_multiplication(0::int16), 0::int16);
    test(test_prefix, diag3D_mat_multiplication(0::int32), 0::int32);
    test(test_prefix, diag3D_mat_multiplication(0::int64), 0::int64);

    test_report();
}

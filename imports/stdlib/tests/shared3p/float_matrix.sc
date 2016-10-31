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
T random_float(T data){
    T rand = 1;
    pd_shared3p uint32 temp;
    pd_shared3p int8 temp2;
    T scalar;
    T scalar2;
    for(uint i = 0; i < 2; ++i){
        scalar = 0;
        while(scalar == 0 || scalar2 == 0){
            scalar = (T) declassify(randomize(temp));
            scalar2 = (T) declassify(randomize(temp2));
        }
        if((i % 2) == 0){
            rand *= scalar;
            rand *= scalar2;
        }
        else{
            rand /= scalar;
            rand /= scalar2;
        }
    }
    return rand;
}

template<domain D:shared3p,type T>
D T[[1]] random(D T[[1]] data){
    uint x_shape = size(data);
    T[[1]] rand (x_shape) = 1;
    pd_shared3p uint32[[1]] temp (x_shape);
    pd_shared3p int8[[1]] temp2 (x_shape);
    T[[1]] scalar (x_shape);
    T[[1]] scalar2 (x_shape);
    for(uint i = 0; i < 2; ++i){
        scalar[0] = 0;
        while(any(scalar == 0) || any(scalar2 == 0)){
            scalar = (T) declassify(randomize(temp));
            scalar2 = (T) declassify(randomize(temp2));
        }
        if((i % 2) == 0){
            rand *= scalar;
            rand *= scalar2;
        }
        else{
            rand /= scalar;
            rand /= scalar2;
        }
    }
    pd_shared3p T[[1]] result = rand;
    return result;
}

template<domain D:shared3p,type T>
D T[[2]] random(D T[[2]] data){
    uint x_shape = shape(data)[0];
    uint y_shape = shape(data)[1];
    T[[2]] rand (x_shape,y_shape) = 1;
    pd_shared3p uint32[[2]] temp (x_shape,y_shape);
    pd_shared3p int8[[2]] temp2 (x_shape,y_shape);
    T[[2]] scalar (x_shape,y_shape);
    T[[2]] scalar2 (x_shape,y_shape);
    for(uint i = 0; i < 2; ++i){
        scalar[0,0] = 0;
        while(any(scalar == 0) || any(scalar2 == 0)){
            scalar = (T) declassify(randomize(temp));
            scalar2 = (T) declassify(randomize(temp2));
        }
        if((i % 2) == 0){
            rand *= scalar;
            rand *= scalar2;
        }
        else{
            rand /= scalar;
            rand /= scalar2;
        }
    }
    pd_shared3p T[[2]] result = rand;
    return result;
}

template<domain D:shared3p,type T>
D T[[3]] random(D T[[3]] data){
    uint x_shape = shape(data)[0];
    uint y_shape = shape(data)[1];
    uint z_shape = shape(data)[2];
    T[[3]] rand (x_shape,y_shape,z_shape) = 1;
    pd_shared3p uint32[[3]] temp (x_shape,y_shape,z_shape);
    pd_shared3p int8[[3]] temp2 (x_shape,y_shape,z_shape);
    T[[3]] scalar (x_shape,y_shape,z_shape);
    T[[3]] scalar2 (x_shape,y_shape,z_shape);
    for(uint i = 0; i < 2; ++i){
        scalar[0,0,0] = 0;
        while(any(scalar == 0) || any(scalar2 == 0)){
            scalar = (T) declassify(randomize(temp));
            scalar2 = (T) declassify(randomize(temp2));
        }
        if((i % 2) == 0){
            rand *= scalar;
            rand *= scalar2;
        }
        else{
            rand /= scalar;
            rand /= scalar2;
        }
    }
    pd_shared3p T[[3]] result = rand;
    return result;
}

template<type T>
bool test_transpose(T data){
    bool result = true;
    pd_shared3p T[[2]] mat (3,3);
    mat = random(mat);
    pd_shared3p T[[2]] mat2 = transpose(mat);
    for(uint i = 0; i < 3; ++i){
        if(!all(declassify(mat[:,i]) == declassify(mat2[i,:]))){
            result = false;
        }
    }

    return result;
}

template<type T>
bool test_transpose2(T data){
    bool result = true;
    pd_shared3p T[[3]] mat (2,2,2);
    mat = random(mat);
    pd_shared3p T[[3]] mat2 = transpose(mat);
    for(uint i = 0; i < 2; ++i){
        if(!all(declassify(mat[:,i,:]) == declassify(mat2[:,:,i]))){
            result = false;
        }
    }

    return result;
}

template<type T>
bool row_sum_test(T data){
    pd_shared3p T[[2]] mat (3,3);
    T[[1]] control (3);
    mat = random(mat);
    T[[1]] row_sums = rowSums(declassify(mat));
    for(uint i = 0; i < 3;++i){
        control[i] = sum(declassify(mat[i,:]));
    }

    return all(row_sums == control);
}

template<type T>
bool dot_product(T data){
    pd_shared3p T[[1]] vec (6);
    pd_shared3p T[[1]] vec2 (6);
    vec = random(vec); vec2 = random(vec2);
    T scalar = dotProduct(declassify(vec),declassify(vec2));
    T control = sum(declassify(vec) * declassify(vec2));

    return scalar == control;
}

template<type T>
bool dot_product_matrix(T data){
    pd_shared3p T[[2]] mat (3,3);
    pd_shared3p T[[2]] mat2 (3,3);
    mat = random(mat); mat2 = random(mat2);
    T[[1]] vec = dotProduct(declassify(mat),declassify(mat2));
    T[[1]] control = rowSums(declassify(mat) * declassify(mat2));

    return all(vec == control);
}

template<type T>
bool cross_product(T data){
    pd_shared3p T[[1]] vec (3);
    pd_shared3p T[[1]] vec2 (3);
    vec = random(vec); vec2 = random(vec2);
    T[[1]] x = declassify(vec);
    T[[1]] y = declassify(vec2);
    T[[1]] vec3 = crossProduct(declassify(vec),declassify(vec2));
    T[[1]] control (3);
    control[0] = x[1] * y[2] - x[2] * y[1];
    control[1] = x[2] * y[0] - x[0] * y[2];
    control[2] = x[0] * y[1] - x[1] * y[0];

    return all(vec3 == control);
}

template<type T>
bool cross_product_matrix(T data){
    pd_shared3p T[[2]] mat (3,3);
    pd_shared3p T[[2]] mat2 (3,3);
    mat = random(mat); mat2 = random(mat2);
    T[[2]] x = declassify(mat);
    T[[2]] y = declassify(mat2);
    T[[2]] mat3 = crossProduct(declassify(mat),declassify(mat2));
    T[[2]] control (3,3);

    for (uint i = 0; i < 3; ++i){
        control[i,:] = crossProduct(x[i,:], y[i,:]);
    }

    return all(mat3 == control);
}

template<type T>
bool mat_multiplication(T data){
    pd_shared3p T[[2]] mat (3,4);
    pd_shared3p T[[2]] mat2 (4,3);
    mat = random(mat); mat2 = random(mat2);
    T[[2]] mat3 (3,3) = matrixMultiplication(declassify(mat),declassify(mat2));
    T[[2]] control (3,3);
    for(uint i = 0; i < 3;++i){
        for(uint j = 0; j < 3;++j){
            control[i,j] = sum(declassify(mat[i,:]) * declassify(mat2[:,j]));
        }
    }

    return all(mat3 == control);
}

template<type T>
bool shared3p_row_sum_test(T data){
    pd_shared3p T[[2]] mat (3,3);
    T[[1]] control (3);
    mat = random(mat);
    pd_shared3p T[[1]] row_sums = rowSums(mat);
    for(uint i = 0; i < 3;++i){
        control[i] = sum(declassify(mat[i,:]));
    }

    return all((declassify(row_sums) / control) >= 0.99) || all((declassify(row_sums) / control) <= 1.01);
}

template<type T>
bool shared3p_dot_product(T data){
    pd_shared3p T[[1]] vec (6);
    pd_shared3p T[[1]] vec2 (6);
    vec = random(vec); vec2 = random(vec2);
    pd_shared3p T scalar = dotProduct(vec,vec2);
    T control = sum(declassify(vec) * declassify(vec2));

    return (declassify(scalar) / control) >= 0.99 && (declassify(scalar) / control) <= 1.01;
}

template<type T>
bool shared3p_dot_product_matrix(T data){
    pd_shared3p T[[2]] mat (3,3);
    pd_shared3p T[[2]] mat2 (3,3);
    mat = random(mat); mat2 = random(mat2);
    pd_shared3p T[[1]] vec = dotProduct(mat,mat2);
    T[[1]] control = rowSums(declassify(mat) * declassify(mat2));

    return all((declassify(vec) / control) >= 0.99) && all((declassify(vec) / control) <= 1.01);
}

template<type T>
bool shared3p_cross_product(T data){
    pd_shared3p T[[1]] vec (3);
    pd_shared3p T[[1]] vec2 (3);
    vec = random(vec); vec2 = random(vec2);
    T[[1]] x = declassify(vec);
    T[[1]] y = declassify(vec2);
    pd_shared3p T[[1]] vec3 = crossProduct(vec,vec2);
    T[[1]] control (3);
    control[0] = x[1] * y[2] - x[2] * y[1];
    control[1] = x[2] * y[0] - x[0] * y[2];
    control[2] = x[0] * y[1] - x[1] * y[0];

    return all((declassify(vec3) / control) >= 0.99) && all((declassify(vec3) / control) <= 1.01);
}

template<type T>
bool shared3p_cross_product_matrix(T data){
    pd_shared3p T[[2]] mat (3,3);
    pd_shared3p T[[2]] mat2 (3,3);
    mat = random(mat); mat2 = random(mat2);
    T[[2]] x = declassify(mat);
    T[[2]] y = declassify(mat2);
    pd_shared3p T[[2]] mat3 = crossProduct(mat,mat2);
    T[[2]] control (3,3);

    for (uint i = 0; i < 3; ++i){
        control[i,:] = crossProduct(x[i,:], y[i,:]);
    }

    return all((declassify(mat3) / control) >= 0.99) && all((declassify(mat3) / control) <= 1.01);
}

template<type T>
bool shared3p_mat_multiplication(T data){
    pd_shared3p T[[2]] mat (3,4);
    pd_shared3p T[[2]] mat2 (4,3);
    mat = random(mat); mat2 = random(mat2);
    pd_shared3p T[[2]] mat3 (3,3) = matrixMultiplication(mat,mat2);
    T[[2]] control (3,3);
    T[[2]] matb = declassify(mat);
    T[[2]] mat2b = declassify(mat2);
    for(uint i = 0; i < shape(declassify(mat3))[0];++i){
        for(uint j = 0; j < shape(declassify(mat3))[1];++j){
            control[i,j] = sum(matb[i,:] * mat2b[:,j]);
        }
    }

    return all((declassify(mat3) / control) >= 0.99) && all((declassify(mat3) / control) <= 1.01);
}

template<type T>
bool shared3p_diag_mat_multiplication(T data){
    pd_shared3p T[[2]] mat (3,4);
    pd_shared3p T[[2]] mat2 (4,4);
    mat = random(mat); mat2 = random(mat2);
    for(uint i = 0; i < shape(declassify(mat2))[0]; ++i){
        for(uint j = 0; j < shape(declassify(mat2))[1]; ++j){
            if(i != j){
                mat2[i,j] = 0;
            }
        }
    }
    T[[2]] matb = declassify(mat);
    T[[2]] mat2b = declassify(mat2);
    pd_shared3p T[[2]] mat3 (3,4) = diagMatrixMultiplication(mat,mat2);
    T[[2]] control (3,4);
    for(uint i = 0; i < 3;++i){
        for(uint j = 0; j < 4;++j){
            control[i,j] = matb[i,j] * mat2b[j,j];
        }

    }

    return all((declassify(mat3) / control) >= 0.99) && all((declassify(mat3) / control) <= 1.01);
}

template<type T>
bool shared3p_mat3D_multiplication(T data){
    pd_shared3p T[[3]] mat (2,2,2);
    pd_shared3p T[[3]] mat2 (2,2,2);
    mat = random(mat); mat2 = random(mat2);
    pd_shared3p T[[3]] mat3 (2,2,2) = matrixMultiplication(mat,mat2);
    T[[3]] control (2,2,2);
    T[[3]] matb = declassify(mat);
    T[[3]] mat2b = declassify(mat2);
    for(uint h = 0; h < shape(mat3)[0];++h){
        for(uint i = 0; i < shape(declassify(mat3))[1];++i){
            for(uint j = 0; j < shape(declassify(mat3))[2];++j){
                control[h,i,j] = sum(matb[h,i,:] * mat2b[h,:,j]);
            }
        }
    }

    return all((declassify(mat3) / control) >= 0.99) && all((declassify(mat3) / control) <= 1.01);
}

template<type T>
bool shared3p_diag3D_mat_multiplication(T data){
    pd_shared3p T[[3]] mat (2,2,2);
    pd_shared3p T[[3]] mat2 (2,2,2);
    mat = random(mat); mat2 = random(mat2);
    for(uint h = 0; h < shape(declassify(mat2))[0];++h){
        for(uint i = 0; i < shape(declassify(mat2))[1]; ++i){
            for(uint j = 0; j < shape(declassify(mat2))[2]; ++j){
                if(i != j){
                    mat2[h,i,j] = 0;
                }
            }
        }
    }
    pd_shared3p T[[3]] mat3 (2,2,2) = diagMatrixMultiplication(mat,mat2);
    T[[3]] control (2,2,2);
    T[[3]] matb = declassify(mat);
    T[[3]] mat2b = declassify(mat2);
    for(uint h = 0; h < shape(declassify(mat))[0];++h){
        for(uint i = 0; i < shape(declassify(mat))[1];++i){
            for(uint j = 0; j < shape(declassify(mat))[2];++j){
                control[h,i,j] = matb[h,i,j] * mat2b[h,j,j];
            }
        }
    }

    return all((declassify(mat3) / control) >= 0.99) && all((declassify(mat3) / control) <= 1.01);
}

template<type T>
bool shared3p_vec_length(T data){
    pd_shared3p T[[1]] vec (3);
    vec = random(vec);
    T[[1]] vec2 = declassify(vec);
    T length = declassify(vecLength(vec));
    pd_shared3p T temp = (vec2[0]*vec2[0]) + (vec2[1]*vec2[1]) + (vec2[2]*vec2[2]);
    T control = declassify(sqrt(temp));

    return (length / control) >= 0.99 && (length / control) <= 1.01;
}

template<type T>
bool shared3p_unit_vec(T data){
    pd_shared3p T[[1]] vec (3);
    vec = random(vec);
    T[[1]] vec2 = declassify(vec);
    T[[1]] unit_vec = declassify(unitVector(vec));
    pd_shared3p T temp2 = (vec2[0]*vec2[0]) + (vec2[1]*vec2[1]) + (vec2[2]*vec2[2]);
    T temp = declassify(sqrt(temp2));
    T[[1]] control = (vec2 / temp);

    return all((unit_vec / control) >= 0.99) && all((unit_vec / control) <= 1.01);
}

template<type T>
bool shared3p_vec_length2D(T data){
    pd_shared3p T[[2]] vec (3,3);
    vec = random(vec);
    T[[2]] vec2 = declassify(vec);
    T[[1]] unit_vec = declassify(vecLength(vec));
    pd_shared3p T[[1]] temp2 (3);
    temp2[0] = (vec2[0,0]*vec2[0,0]) + (vec2[0,1]*vec2[0,1]) + (vec2[0,2]*vec2[0,2]);
    temp2[1] = (vec2[1,0]*vec2[1,0]) + (vec2[1,1]*vec2[1,1]) + (vec2[1,2]*vec2[1,2]);
    temp2[2] = (vec2[2,0]*vec2[2,0]) + (vec2[2,1]*vec2[2,1]) + (vec2[2,2]*vec2[2,2]);
    T[[1]] control = declassify(sqrt(temp2));

    return all((unit_vec / control) >= 0.99) && all((unit_vec / control) <= 1.01);
}

template<type T>
bool shared3p_unit_vec2D(T data){
    pd_shared3p T[[2]] vec (3,3);
    vec = random(vec);
    T[[2]] vec2 = declassify(vec);

    T[[1]] unit_vec = flatten(declassify(unitVector(vec)));

    pd_shared3p T[[1]] temp3 (3);
    temp3[0] = (vec2[0,0]*vec2[0,0]) + (vec2[0,1]*vec2[0,1]) + (vec2[0,2]*vec2[0,2]);
    temp3[1] = (vec2[1,0]*vec2[1,0]) + (vec2[1,1]*vec2[1,1]) + (vec2[1,2]*vec2[1,2]);
    temp3[2] = (vec2[2,0]*vec2[2,0]) + (vec2[2,1]*vec2[2,1]) + (vec2[2,2]*vec2[2,2]);
    T[[1]] temp2 = declassify(sqrt(temp3));
    T[[2]] temp (3,3);
    temp[0,:] = (vec2[0,:] / temp2[0]);
    temp[1,:] = (vec2[1,:] / temp2[1]);
    temp[2,:] = (vec2[2,:] / temp2[2]);
    T[[1]] control = flatten(temp);

    return all((unit_vec / control) >= 0.99) && all((unit_vec / control) <= 1.01);
}

template<type T>
bool determinant_test(T data){
    T[[2]] mat (3,3);
    T[[1]] vec1 (3) = {1,2,3};
    T[[1]] vec2 (3) = {4,5,6};
    T[[1]] vec3 (3) = {7,8,9};
    mat[0,:] = vec1;
    mat[1,:] = vec2;
    mat[2,:] = vec3;
    if ((determinant(mat) + (0)) > 0.01)
        return false;

    vec1 = {3,6,2};
    vec2 = {5,1,9};
    vec3 = {5,2,1};
    mat[0,:] = vec1;
    mat[1,:] = vec2;
    mat[2,:] = vec3;
    if ((determinant(mat) - (199)) > 0.01)
        return false;

    vec1 = {4.650, 6.450, 1.760};
    vec2 = {5.980, 2.540, 8.090};
    vec3 = {3.280, 7.910, 9.010};
    mat[0,:] = vec1;
    mat[1,:] = vec2;
    mat[2,:] = vec3;
    if ((determinant(mat) - (-298.930)) > 0.01)
        return false;

    return true;
}

void main(){
    string test_prefix = "Matrix transpose 2D and 3D";
    test(test_prefix, test_transpose(0::float32), 0::float32);
    test(test_prefix, test_transpose2(0::float32), 0::float32);
    test(test_prefix, test_transpose(0::float64), 0::float64);
    test(test_prefix, test_transpose2(0::float64), 0::float64);

    test_prefix = "Matrix row sums";
    test(test_prefix, row_sum_test(0::float32), 0::float32);
    test(test_prefix, row_sum_test(0::float64), 0::float64);

    test_prefix = "Dot product for vectors";
    test(test_prefix, dot_product(0::float32), 0::float32);
    test(test_prefix, dot_product(0::float64), 0::float64);

    test_prefix = "Dot product for matrices";
    test(test_prefix, dot_product_matrix(0::float32), 0::float32);
    test(test_prefix, dot_product_matrix(0::float64), 0::float64);

    test_prefix = "cross product for vectors";
    test(test_prefix, cross_product(0::float32), 0::float32);
    test(test_prefix, cross_product(0::float64), 0::float64);

    test_prefix = "cross product for matrices";
    test(test_prefix, cross_product_matrix(0::float32), 0::float32);
    test(test_prefix, cross_product_matrix(0::float64), 0::float64);

    test_prefix = "Matrix multiplication";
    test(test_prefix, mat_multiplication(0::float32), 0::float32);
    test(test_prefix, mat_multiplication(0::float64), 0::float64);

    test_prefix = "shared3p Matrix row sums";
    test(test_prefix, shared3p_row_sum_test(0::float32), 0::float32);
    test(test_prefix, shared3p_row_sum_test(0::float64), 0::float64);

    test_prefix = "shared3p Matrix dotproduct for vectors";
    test(test_prefix, shared3p_dot_product(0::float32), 0::float32);
    test(test_prefix, shared3p_dot_product(0::float64), 0::float64);

    test_prefix = "shared3p Matrix dotproduct for matrices";
    test(test_prefix, shared3p_dot_product_matrix(0::float32), 0::float32);
    test(test_prefix, shared3p_dot_product_matrix(0::float64), 0::float64);

    test_prefix = "shared3p cross product for vectors";
    test(test_prefix, shared3p_cross_product(0::float32), 0::float32);
    test(test_prefix, shared3p_cross_product(0::float64), 0::float64);

    test_prefix = "shared3p cross product for matrices";
    test(test_prefix, shared3p_cross_product_matrix(0::float32), 0::float32);
    test(test_prefix, shared3p_cross_product_matrix(0::float64), 0::float64);

    test_prefix = "shared3p 2D Matrix multiplication";
    test(test_prefix, shared3p_mat_multiplication(0::float32), 0::float32);
    test(test_prefix, shared3p_mat_multiplication(0::float64), 0::float64);

    test_prefix = "shared3p 2D Diagonal matrix multiplication";
    test(test_prefix, shared3p_diag_mat_multiplication(0::float32), 0::float32);
    test(test_prefix, shared3p_diag_mat_multiplication(0::float64), 0::float64);

    test_prefix = "shared3p 3D Matrix multiplication";
    test(test_prefix, shared3p_mat3D_multiplication(0::float32), 0::float32);
    test(test_prefix, shared3p_mat3D_multiplication(0::float64), 0::float64);

    test_prefix = "shared3p 3D Diagonal matrix multiplication";
    test(test_prefix, shared3p_diag3D_mat_multiplication(0::float32), 0::float32);
    test(test_prefix, shared3p_diag3D_mat_multiplication(0::float64), 0::float64);

    test_prefix = "shared3p vector length";
    test(test_prefix, shared3p_vec_length(0::float32), 0::float32);
    test(test_prefix, shared3p_vec_length(0::float64), 0::float64);

    test_prefix = "shared3p unit vector";
    test(test_prefix, shared3p_unit_vec(0::float32), 0::float32);
    test(test_prefix, shared3p_unit_vec(0::float64), 0::float64);

    test_prefix = "shared3p vector length 2D";
    test(test_prefix, shared3p_vec_length2D(0::float32), 0::float32);
    test(test_prefix, shared3p_vec_length2D(0::float64), 0::float64);

    test_prefix = "shared3p unit vector 2D";
    test(test_prefix, shared3p_unit_vec2D(0::float32), 0::float32);
    test(test_prefix, shared3p_unit_vec2D(0::float64), 0::float64);

    test_prefix = "Determinant";
    test(test_prefix, determinant_test(0::float32), 0::float32);
    test(test_prefix, determinant_test(0::float64), 0::float64);

    test_report();
}

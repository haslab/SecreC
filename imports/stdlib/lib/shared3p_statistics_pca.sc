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

/** \cond */
module shared3p_statistics_pca;

import matrix;
import shared3p;
import shared3p_matrix;
import stdlib;
/** \endcond */

/**
 * @file
 * \defgroup shared3p_statistics_pca shared3p_statistics_pca.sc
 * \defgroup shared3p_pca_result PCAResult
 * \defgroup shared3p_pca_return_values constants
 * \defgroup shared3p_gspca gspca
 */

/**
 * \addtogroup shared3p_statistics_pca
 * @{
 * @brief Module for performing principal component analysis
 */

/**
 * \addtogroup shared3p_pca_result
 * @{

 * @brief Structure containing the results of the analysis. Note that
 * each field only has a reasonable value if it was requested when
 * calling gspca. See also \ref shared3p_pca_return_values "return value constants".
 */
/** \cond */
template<domain D : shared3p, type T>
struct PCAResult {
    D T[[2]] residual;
    D T[[2]] loads;
    D T[[2]] scores;
}
/** \endcond */
/** @} */

/**
 * \addtogroup shared3p_pca_return_values
 * @{
 * @brief Constants used to specify which result values are needed
 * from the analysis.
 *
 * @note PCA_RETURN_RESIDUAL - residual matrix.
 * @note PCA_RETURN_LOADS - loads. The columns are eigenvectors of the
 * covariance matrix. Can be used to project data to the principal
 * component space.
 * @note PCA_RETURN_SCORES - transformed input values.
 */
uint8 PCA_RETURN_RESIDUAL = 1;
uint8 PCA_RETURN_LOADS    = 2;
uint8 PCA_RETURN_SCORES   = 4;
/** @} */

/** \cond */
template<domain D : shared3p, dim N>
D uint32[[N]] _mulFix(D uint32[[N]] x, D uint32[[N]] y) {
    D uint32[[N]] res = x;
    __syscall("shared3p::mul_fix32_vec", __domainid (D), x, y, res);
    return res;
}

template<domain D : shared3p, dim N>
D uint64[[N]] _mulFix(D uint64[[N]] x, D uint64[[N]] y) {
    D uint64[[N]] res = x;
    __syscall("shared3p::mul_fix64_vec", __domainid (D), x, y, res);
    return res;
}

template<domain D : shared3p>
D uint32[[2]] _toFix(D float32[[2]] x) {
    D uint32[[2]] res(shape(x)[0], shape(x)[1]);
    __syscall("shared3p::float32_to_fix32", __domainid (D), x, res, 16 :: uint);
    return res;
}

template<domain D : shared3p>
D uint64[[2]] _toFix(D float64[[2]] x) {
    D uint64[[2]] res(shape(x)[0], shape(x)[1]);
    __syscall("shared3p::float64_to_fix64", __domainid (D), x, res, 32 :: uint);
    return res;
}

template<domain D : shared3p>
D float32[[2]] _fromFix(D uint32[[2]] x) {
    D float32[[2]] res(shape(x)[0], shape(x)[1]);
    __syscall("shared3p::fix32_to_float32", __domainid (D), x, res, 16 :: uint);
    return res;
}

template<domain D : shared3p>
D float64[[2]] _fromFix(D uint64[[2]] x) {
    D float64[[2]] res(shape(x)[0], shape(x)[1]);
    __syscall("shared3p::fix64_to_float64", __domainid (D), x, res, 32 :: uint);
    return res;
}

template <domain D : shared3p, type Fix>
D Fix[[2]] _fixMatrixMultiplication(D Fix[[2]] x, D Fix[[2]] y) {
	// For parallelisation
	uint [[1]] xShape = shape (x);
	uint [[1]] yShape = shape (y);

	// no. of columns of x must equal no. of rows of y
	assert (xShape[1] == yShape[0]);

	uint commonDim = xShape[1];

	D Fix[[1]] mulVec1 (xShape[0] * yShape[1] * commonDim),
				  mulVec2 (xShape[0] * yShape[1] * commonDim),
				  product (xShape[0] * yShape[1] * commonDim);

	// At the moment our matrices are kept in memory in row major order
	// We only take the column we need from memory once
	// This is also why our cycles run first over y and then over x
	D Fix[[1]] yColumn (commonDim);
	for (uint i = 0; i < yShape[1]; i++) {
		yColumn = y[:, i];
		for (uint j = 0; j < xShape[0]; j++) {
			mulVec1[((xShape[0] * i + j) * commonDim) : ((xShape[0] * i + j + 1) * commonDim)] = x[j, :];
			mulVec2[((xShape[0] * i + j) * commonDim) : ((xShape[0] * i + j + 1) * commonDim)] = yColumn;
		}
	}

	product = _mulFix (mulVec1, mulVec2);

	D Fix[[2]] result (xShape[0], yShape[1]);
	D Fix[[1]] resultVec (xShape[0] * yShape[1]);

	resultVec = sum (product, (xShape[0] * yShape[1]));

	for (uint i = 0; i < yShape[1]; i++){
		result[:, i] = resultVec [i * xShape[0] : (i + 1) * xShape[0]];
	}

	return result;
}

template<domain D : shared3p, type Fix>
D Fix _invSqrtFix(D Fix x) {
    D Fix x1;
    __syscall("shared3p::sqrt_fix64_vec", __domainid (D), x, x1);
    D Fix x2;
    __syscall("shared3p::inv_fix64_vec", __domainid (D), x1, x2);
    return x2;
}

template <type T, dim N, domain D>
D T[[N]] _power(D T[[N]] x, uint e) {
    if (e == 0) {
        D T[[N]] one = 1;
        return one;
    }

    D T[[N]] pow = x;
    while (e > 1) {
        pow = pow * x;
        e--;
    }

    return pow;
}

uint64 pubDoubleToFix(float64 x, uint radix_point) {
    return (uint64) round(x * (float64) _power(2, radix_point));
}

uint _getRadix(uint64 x) {
    return 32;
}

uint _getRadix(uint32 x) {
    return 16;
}

/*
 * GS-PCA algorithm from "Parallel GPU Implementation of Iterative PCA
 * Algorithms".
 */
template<domain D : shared3p, type Fix>
PCAResult<D, Fix> _gspca(D Fix[[2]] X, uint n_components,
                         uint iterations, uint8 returnValues)
{
    bool wantResidual = (bool) (returnValues & PCA_RETURN_RESIDUAL);
    bool wantLoads = (bool) (returnValues & PCA_RETURN_LOADS);
    bool wantScores = (bool) (returnValues & PCA_RETURN_SCORES);

    assert (wantResidual || wantLoads || wantScores);
    assert (n_components >= 1);
    assert (iterations >= 1);

    D Fix[[2]] R = X;
    D Fix[[2]] P(shape(X)[1], n_components);
    D Fix[[2]] T(shape(X)[0], n_components);
    D Fix[[2]] V(shape(X)[0], n_components);
    D Fix[[2]] pDivisor(shape(X)[1], 1);
    D Fix[[2]] vDivisor(shape(X)[0], 1);

    Fix proxy;
    uint radix = _getRadix(proxy);

    // This is 1/2^12 as a fixed point number. They are used to
    // shorten vectors before normalizing to avoid overflow.
    pDivisor = 1 << (radix - 12);
    vDivisor = 1 << (radix - 12);

    // todo: optimize, use k sum
    // Center
    uint64 invRows = pubDoubleToFix(1.0 / (float64) shape(R)[0], radix);
    D uint64 invRowsPriv = invRows;
    for (uint i = 0; i < shape(R)[1]; ++i) {
        D uint64 mu = _mulFix(sum(R[:, i]), invRowsPriv);
        R[:, i] -= mu;
    }

    for (uint k = 0; k < n_components; ++k) {
        D Fix[[2]] t(shape(X)[0], 1);
        D Fix[[2]] v = reshape(R[:, k], shape(X)[0], 1);
        D Fix[[2]] Rtrans = transpose(R);
        D Fix[[2]] p(shape(X)[1], 1);

        for (uint i = 0; i < iterations; ++i) {
            p = _fixMatrixMultiplication(Rtrans, v);
            p = _mulFix(p, pDivisor);

            if (k > 0) {
                // Orthogonality correction
                D uint64[[2]] A = _fixMatrixMultiplication(transpose(P[:, 0:k]), p);
                p = p - _fixMatrixMultiplication(P[:, 0:k], A);
            }

            {
                D Fix invSqrt = _invSqrtFix(sum((_mulFix(p, p))[:, 0]));
                D Fix[[2]] invSqrtMat(shape(X)[1], 1) = invSqrt;
                p = _mulFix(p, invSqrtMat);
                v = _fixMatrixMultiplication(R, p);
            }

            if (k > 0) {
                // Orthogonality correction
                D Fix[[2]] B = _fixMatrixMultiplication(transpose(V[:, 0:k]), v);
                v = v - _fixMatrixMultiplication(V[:, 0:k], B);
            }

            if (i == iterations - 1) {
                t = v;
                if (wantScores)
                    T[:, k] = t[:, 0];
            }

            {
                v = _mulFix(v, vDivisor);
                D Fix invSqrt = _invSqrtFix(sum((_mulFix(v, v))[:, 0]));
                D Fix[[2]] invSqrtMat(shape(X)[0], 1) = invSqrt;
                v = _mulFix(v, invSqrtMat);
            }
        }

        if (k == n_components - 1) {
            if (wantResidual)
                R = R - _fixMatrixMultiplication(t, transpose(p));
            if (wantLoads)
                P[:, k] = p[:, 0];
        } else {
            R = R - _fixMatrixMultiplication(t, transpose(p));
            P[:, k] = p[:, 0];
            V[:, k] = v[:, 0];
        }
    }

    PCAResult<D, Fix> res;
    if (wantResidual)
        res.residual = R;
    if (wantScores)
        res.scores = T;
    if (wantLoads)
        res.loads = P;

    return res;
}
/** \endcond */

/**
 * \addtogroup shared3p_gspca
 * @{
 * @brief Principle component analysis. Note that this method is
 * relatively efficient and precise when a low number of components is
 * required. It uses fixed point numbers internally so it may fail on
 * large inputs due to overflow.
 * @note **D** - shared3p protection domain
 * @note Supported types - \ref float32 "float32" / \ref float64 "float64"
 * @param X - data matrix where the columns are variables
 * @param n_components - how many components to compute
 * @param iterations - how many iterations to run the algorithm
 * @param returnValues - indicates which results to return. Use
 * bitwise or if you want multiple results.
 */
template<domain D : shared3p>
PCAResult<D, float32> gspca(D float32[[2]] X, uint n_components,
                            uint iterations, uint8 returnValues)
{
    D uint32[[2]] fixX = _toFix(X);
    PCAResult<D, uint32> resFix = _gspca(fixX, n_components, iterations, returnValues);
    PCAResult<D, float32> res;

    res.residual = _fromFix(resFix.residual);
    res.scores = _fromFix(resFix.scores);
    res.loads = _fromFix(resFix.loads);

    return res;
}

template<domain D : shared3p>
PCAResult<D, float64> gspca(D float64[[2]] X, uint n_components,
                            uint iterations, uint8 returnValues)
{
    D uint64[[2]] fixX = _toFix(X);
    PCAResult<D, uint64> resFix = _gspca(fixX, n_components, iterations, returnValues);
    PCAResult<D, float64> res;

    res.residual = _fromFix(resFix.residual);
    res.scores = _fromFix(resFix.scores);
    res.loads = _fromFix(resFix.loads);

    return res;
}
/** @} */

/** @} */

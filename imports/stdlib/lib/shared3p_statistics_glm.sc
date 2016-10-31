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
module shared3p_statistics_glm;

import shared3p_matrix;
import shared3p_oblivious;
import shared3p_statistics_common;
import shared3p_statistics_regression;
import shared3p;
import matrix;
import oblivious;
import stdlib;
/** \endcond */

/**
 * @file
 * \defgroup shared3p_statistics_glm shared3p_statistics_glm.sc
 * \defgroup shared3p_glm_constants constants
 * \defgroup shared3p_generalized_linear_model generalizedLinearModel
 * \defgroup shared3p_generalized_linear_model_method generalizedLinearModel(with method parameter)
 */

/**
 * \addtogroup shared3p_statistics_glm
 * @{
 * @brief Module for performing regression analysis of generalized
 * linear models.
 */

/**
 * \addtogroup shared3p_glm_constants
 * @{
 * @brief constants
 * @note The "family" constants are used to specify the distribution
 * of the dependent variable. The "SOLE method" constants specify the
 * algorithm used to solve systems of linear equations.
 */
int64 GLM_FAMILY_GAUSSIAN        = 0;
int64 GLM_FAMILY_BINOMIAL_LOGIT  = 1;

int64 GLM_SOLE_METHOD_INVERT             = 0;
int64 GLM_SOLE_METHOD_LU_DECOMPOSITION   = 1;
int64 GLM_SOLE_METHOD_GAUSS              = 2;
int64 GLM_SOLE_METHOD_CONJUGATE_GRADIENT = 3;
/** @} */

/** \cond */

/*
 * Fitting of generalized linear models. Read "Generalized Linear
 * Models" by McCullagh and Nelder.
 */
template<domain D : shared3p, type FT>
D FT[[1]] _glm(D FT[[1]] dependent,
               D FT[[2]] vars,
               int64 family,
               uint iterations,
               int64 SOLEmethod,
               uint SOLEiterations)
{
    assert(family == GLM_FAMILY_GAUSSIAN ||
           family == GLM_FAMILY_BINOMIAL_LOGIT);

    assert(SOLEmethod == GLM_SOLE_METHOD_INVERT ||
           SOLEmethod == GLM_SOLE_METHOD_LU_DECOMPOSITION ||
           SOLEmethod == GLM_SOLE_METHOD_GAUSS ||
           SOLEmethod == GLM_SOLE_METHOD_CONJUGATE_GRADIENT);

    // Add a variable with all observations set to one. The parameter
    // for this variable is the intercept.
    D FT[[2]] ones(shape(vars)[0], 1) = 1;
    vars = cat(vars, ones, 1);

    D FT[[2]] z;
    uint varCount = shape(vars)[1];
    uint observationCount = size(dependent);
    D FT[[2]] y = _toCol(dependent);
    D FT[[2]] p(varCount, 1);
    D FT[[2]] mu = _initialmu(y, family);
    // Calculate initial eta from mu
    D FT[[2]] eta = _link(mu, family);
    D FT[[2]] varsTransposed = transpose(vars);

    uint iteration = 1;
    while (true) {
        // Calculate the derivative of the inverse of the link function at the current eta
        D FT[[2]] derivative = _derivative(eta, family);

        // Calculate weights
        D FT[[2]] variance = _variance(mu, family);
        D FT[[2]] weight = derivative * derivative / variance;

        // Calculate z
        D FT[[2]] z = eta + (y - mu) / derivative;

        // Solve X^T * W * X * p = X^T * W * z to find new estimation
        // of parameters
        D FT[[2]] varsTransWeight;
        D FT[[2]] mulR(varCount, observationCount);

        for (uint i = 0; i < varCount; i++)
            mulR[i, :] = weight[:, 0];

        varsTransWeight = varsTransposed * mulR;

        D FT[[2]] varsSOLE = matrixMultiplication(varsTransWeight, vars);
        D FT[[2]] dependentSOLE = matrixMultiplication(varsTransWeight, z);

        if (SOLEmethod == GLM_SOLE_METHOD_INVERT) {
            assert(varCount <= 4);

            if (varCount == 1) {
                p = matrixMultiplication(inv(varsSOLE), dependentSOLE);
            } else if (varCount == 2) {
                p = matrixMultiplication(_invert2by2(varsSOLE), dependentSOLE);
            } else if (varCount == 3) {
                p = matrixMultiplication(_invert3by3(varsSOLE), dependentSOLE);
            } else if (varCount == 4) {
                p = matrixMultiplication(_invert4by4(varsSOLE), dependentSOLE);
            } else {
                assert(false); // Can't use method INVERT with more than 4 variables!
            }
        } else if (SOLEmethod == GLM_SOLE_METHOD_GAUSS) {
            p[:, 0] = _gaussianElimination(varsSOLE, dependentSOLE[:, 0]);
        } else if (SOLEmethod == GLM_SOLE_METHOD_LU_DECOMPOSITION) {
            p[:, 0] = _solveLU(varsSOLE, dependentSOLE[:, 0]);
        } else if (SOLEmethod == GLM_SOLE_METHOD_CONJUGATE_GRADIENT) {
            p[:, 0] = _conjugateGradient(varsSOLE, dependentSOLE[:, 0], SOLEiterations);
        }

        if (!(iteration < iterations))
            break;

        // Update eta
        eta = matrixMultiplication(vars, p);

        // Update mu
        mu = _linkInverse(eta, family);

        iteration++;
    }

    return p[:, 0];
}

template<domain D, type FT>
D FT[[2]] _initialmu(D FT[[2]] y, int64 family) {
    D FT[[2]] res(shape(y)[0], 1);

    if (family == GLM_FAMILY_GAUSSIAN)
        res = y;
    else if (family == GLM_FAMILY_BINOMIAL_LOGIT)
        res = (y + 0.5) / 2;

    return res;
}

template<domain D, type FT>
D FT[[2]] _link(D FT[[2]] mu, int64 family) {
    D FT[[2]] res(size(mu), 1);

    if (family == GLM_FAMILY_GAUSSIAN) {
        // Link is id
        res = mu;
    } else if (family == GLM_FAMILY_BINOMIAL_LOGIT) {
        // Link is ln(mu / (1 - mu))
        res = ln(mu / (1 - mu));
    }

    return res;
}

template<domain D, type FT>
D FT[[2]] _linkInverse(D FT[[2]] eta, int64 family) {
    D FT[[2]] res(size(eta), 1);

    if (family == GLM_FAMILY_GAUSSIAN) {
        // id^-1
        res = eta;
    } else if (family == GLM_FAMILY_BINOMIAL_LOGIT) {
        // exp(eta) / (exp(eta) + 1)
        D FT[[2]] x = exp(eta);
        res = x / (x + 1);
    }

    return res;
}

// mu = g^-1(eta). This is d(mu) / d(eta) evaluated at the given eta.
template<domain D, type FT>
D FT[[2]] _derivative(D FT[[2]] eta, int64 family) {
    D FT[[2]] res(size(eta), 1);

    if (family == GLM_FAMILY_GAUSSIAN) {
        // d(eta) / d(eta) = 1
        res = 1;
    } else if (family == GLM_FAMILY_BINOMIAL_LOGIT) {
        // exp(eta) / (exp(eta) + 1)^2
        D FT[[2]] x = exp(eta);
        D FT[[2]] xp1 = x + 1;
        res = x / (xp1 * xp1);
    }

    return res;
}

template<domain D, type FT>
D FT[[2]] _variance(D FT[[2]] mu, int64 family) {
   D FT[[2]] res(size(mu), 1);

    if (family == GLM_FAMILY_GAUSSIAN) {
        res = 1;
    } else if (family == GLM_FAMILY_BINOMIAL_LOGIT) {
        res = mu * (1 - mu);
    }

    return res;
}

template<domain D, type T>
D T[[2]] _toCol(D T[[1]] vec) {
    return reshape(vec, size(vec), 1);
}

template<domain D : shared3p, type T>
D T[[1]] _dispatch(D T[[1]] dependent,
                   D T[[2]] variables,
                   int64 family,
                   uint iterations)
{
    uint varCount = shape(variables)[1];

    if (varCount < 4) {
        return _glm(dependent, variables, family, iterations, GLM_SOLE_METHOD_INVERT, 0 :: uint);
    } else {
        return _glm(dependent, variables, family, iterations, GLM_SOLE_METHOD_LU_DECOMPOSITION, 0 :: uint);
    }
}
/** \endcond */

/**
 * \addtogroup shared3p_generalized_linear_model
 * @{
 * @brief Fitting of generalized linear models
 * @note **D** - shared3p protection domain
 * @note Supported types - \ref int32 "int32" / \ref int64 "int64" /
 * \ref float32 "float32" / \ref float64 "float64"
 * @param dependent - sample vector of the dependent variable
 * @param variables - a matrix where each column is a sample of an
 * explanatory variable
 * @param family - indicates the distribution of the dependent
 * variable
 * @param iterations - number of iterations of the GLM algorithm
 */
template<domain D : shared3p>
D float32[[1]] generalizedLinearModel(D int32[[1]] dependent, D int32[[2]] variables, int64 family, uint iterations) {
    return _dispatch((float32) dependent, (float32) variables, family, iterations);
}

template<domain D : shared3p>
D float64[[1]] generalizedLinearModel(D int64[[1]] dependent, D int64[[2]] variables, int64 family, uint iterations) {
    return _dispatch((float64) dependent, (float64) variables, family, iterations);
}

template<domain D : shared3p>
D float32[[1]] generalizedLinearModel(D float32[[1]] dependent, D float32[[2]] variables, int64 family, uint iterations) {
    return _dispatch(dependent, variables, family, iterations);
}

template<domain D : shared3p>
D float64[[1]] generalizedLinearModel(D float64[[1]] dependent, D float64[[2]] variables, int64 family, uint iterations) {
    return _dispatch(dependent, variables, family, iterations);
}
/** @} */

/**
 * \addtogroup shared3p_generalized_linear_model_method
 * @{
 * @brief Fitting of generalized linear models
 * @note **D** - shared3p protection domain
 * @note Supported types - \ref int32 "int32" / \ref int64 "int64" /
 * \ref float32 "float32" / \ref float64 "float64"
 * @param dependent - sample vector of the dependent variable
 * @param variables - a matrix where each column is a sample of an
 * explanatory variable
 * @param family - indicates the distribution of the dependent
 * variable
 * @param iterations - number of iterations of the GLM algorithm
 * @param SOLEmethod - method to use for solving systems of linear equations
 * @param SOLEiterations - if the conjugate gradient method is used
 * for solving systems of linear equations, this parameter is the
 * number of iterations to use
 */
template<domain D : shared3p>
D float32[[1]] generalizedLinearModel(D int32[[1]] dependent, D int32[[2]] variables, int64 family, uint iterations, int64 SOLEmethod, uint SOLEiterations) {
    return _glm((float32) dependent, (float32) variables, family, iterations, SOLEmethod, SOLEiterations);
}

template<domain D : shared3p>
D float64[[1]] generalizedLinearModel(D int64[[1]] dependent, D int64[[2]] variables, int64 family, uint iterations, int64 SOLEmethod, uint SOLEiterations) {
    return _glm((float64) dependent, (float64) variables, family, iterations, SOLEmethod, SOLEiterations);
}

template<domain D : shared3p>
D float32[[1]] generalizedLinearModel(D float32[[1]] dependent, D float32[[2]] variables, int64 family, uint iterations, int64 SOLEmethod, uint SOLEiterations) {
    return _glm(dependent, variables, family, iterations, SOLEmethod, SOLEiterations);
}

template<domain D : shared3p>
D float64[[1]] generalizedLinearModel(D float64[[1]] dependent, D float64[[2]] variables, int64 family, uint iterations, int64 SOLEmethod, uint SOLEiterations) {
    return _glm(dependent, variables, family, iterations, SOLEmethod, SOLEiterations);
}
/** @} */

/** @} */

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

/**
 * \cond
 */
module shared3p_statistics_testing;

import shared3p_matrix;
import shared3p_oblivious;
import shared3p_random;
import shared3p_sort;
import shared3p_statistics_common;
import shared3p_statistics_summary;
import shared3p;
import stdlib;
/**
 * \endcond
 */

/**
 * @file
 * \defgroup shared3p_statistics_testing shared3p_statistics_testing.sc
 * \defgroup t_test tTest
 * \defgroup t_test_samples tTest(two sample vectors)
 * \defgroup combined_df combinedDegreesOfFreedom
 * \defgroup paired_t_test pairedTTest
 * \defgroup chisq chiSquared
 * \defgroup chisq_cb chiSquared(with codebook)
 * \defgroup wilcoxon_rank_sum wilcoxonRankSum
 * \defgroup wilcoxon_signed_rank wilcoxonSignedRank
 * \defgroup hypothesis_testing_constants constants
 * \defgroup multiple_testing multipleTesting
 * \defgroup mann_whitney_u mannWhitneyU
 */

/**
 * \addtogroup shared3p_statistics_testing
 * @{
 * @brief Module with statistical hypothesis tests.
 */

/** \cond */
template<domain D : shared3p, type T, type FT>
D FT _tTest (D T[[1]] data, D bool[[1]] cases, D bool[[1]] controls, bool variancesEqual) {

    assert (size (data) == size (cases) && size (data) == size (controls));
    uint sizeData = size (data);
    D T[[1]] dataCases (sizeData), dataControls (sizeData);
    D uint32 countCases, countControls;
    D FT varCases, varControls, meanCases, meanControls;
    D FT[[1]] varAndMean (2);

    D T[[1]] mulAPar (sizeData * 2), mulBPar (sizeData * 2), mulRes (sizeData * 2);
    mulAPar[0 : sizeData] = data;
    mulAPar[sizeData : sizeData * 2] = data;
    mulBPar[0 : sizeData] = (T)cases;
    mulBPar[sizeData : sizeData * 2] = (T)controls;

    mulRes = mulAPar * mulBPar;
    dataCases = mulRes[0 : sizeData];
    dataControls = mulRes[sizeData : sizeData * 2];

    countCases = sum ((uint32) cases);
    countControls = sum ((uint32) controls);

    // TODO: many variances and means in parallel?
    meanCases = mean (dataCases, cases);
    varCases = _variance (dataCases, cases, meanCases);

    meanControls = mean (dataControls, controls);
    varControls = _variance (dataControls, controls, meanControls);

    D FT commonStDev, subMean;
    D FT result;

    subMean = meanCases - meanControls;

    if (variancesEqual) {
        D FT[[1]] mulA2 (2), mulB2 (2), mulRes2 (2);
        mulA2[0] = (FT) (countCases - 1);
        mulA2[1] = (FT) (countControls - 1);
        mulB2[0] = varCases;
        mulB2[1] = varControls;
        mulRes2 = mulA2 * mulB2;

        D FT[[1]] invPar (2), resInvPar (2);
        invPar[0] = (FT) countCases;
        invPar[1] = (FT) countControls;
        resInvPar = inv (invPar);

        D FT[[1]] sqrtPar (2), resSqrtPar (2);
        sqrtPar[0] = (mulRes2[0] + mulRes2[1]) / (FT) (countCases + countControls - 2);
        sqrtPar[1] = resInvPar[0] + resInvPar[1];
        resSqrtPar = sqrt (sqrtPar);

        result = subMean / (resSqrtPar[0] * resSqrtPar[1]);

    } else {
        D FT[[1]] divAPar (2), divBPar (2), resDivPar (2);
        divAPar[0] = varCases;
        divAPar[1] = varControls;
        divBPar[0] = (FT) countCases;
        divBPar[1] = (FT) countControls;

        resDivPar = divAPar / divBPar;

        commonStDev = sqrt (resDivPar[0] + resDivPar[1]);
        result = subMean / commonStDev;
    }

    return result;
}

template<domain D : shared3p, type T, type FT, type UT>
D FT _tTest (D T[[1]] data1,
             D bool[[1]] ia1,
             D T[[1]] data2,
             D bool[[1]] ia2,
             bool variancesEqual,
             UT proxy)
{
    assert (size (data1) == size (ia1));
    assert (size (data2) == size (ia2));

    uint size1 = size (data1);
    uint size2 = size (data2);

    D T[[1]] datas (size1 + size2);
    D bool[[1]] ias (size1 + size2);
    datas[:size1] = data1;
    datas[size1:] = data2;
    ias[:size1] = ia1;
    ias[size1:] = ia2;

    datas = datas * (T) ias;
    data1 = datas[:size1];
    data2 = datas[size1:];

    D FT[[1]] meanVar = _parallelMeanVar (data1, ia1, data2, ia2, proxy);
    D FT mean1 = meanVar[0];
    D FT mean2 = meanVar[1];
    D FT var1 = meanVar[2];
    D FT var2 = meanVar[3];
    D uint32 count1 = sum ((uint32) ia1);
    D uint32 count2 = sum ((uint32) ia2);

    if (variancesEqual) {
        D FT[[1]] mulL = {(FT) count1 - 1, (FT) count2 - 1};
        D FT[[1]] mulR = {var1, var2};
        D FT[[1]] mulRes = mulL * mulR;

        D FT[[1]] inversed = {(FT) count1, (FT) count2};
        inversed = inv (inversed);

        D FT[[1]] roots = {(mulRes[0] + mulRes[1]) / (FT) (count1 + count2 - 2),
                           inversed[0] + inversed[1]};
        roots = sqrt (roots);

        return (mean1 - mean2) / (roots[0] * roots[1]);
    } else {
        D FT[[1]] divL = {var1, var2};
        D FT[[1]] divR = {(FT) count1, (FT) count2};
        D FT[[1]] divRes = divL / divR;
        D FT commonStDev = sqrt (divRes[0] + divRes[1]);

        return (mean1 - mean2) / commonStDev;
    }
}

// Returns {mean1, mean2, variance1, variance2}
template<domain D, type IT, type UT, type FT>
D FT[[1]] _parallelMeanVar (D IT[[1]] data1,
                            D bool[[1]] ia1,
                            D IT[[1]] data2,
                            D bool[[1]] ia2,
                            UT proxy)
{
    assert (size (data1) == size (ia1));
    assert (size (data2) == size (ia2));

    // Shuffle and cut both samples
    D IT[[2]] mat (max (size (data1), size (data2)), 4);
    mat[: size (data1), 0] = data1;
    mat[: size (ia1), 1] = (IT) ia1;
    mat[: size (data2), 2] = data2;
    mat[: size (ia2), 3] = (IT) ia2;

    mat = shuffleRows (mat);

    IT[[1]] pubIA1 = declassify (mat[:, 1]);
    IT[[1]] pubIA2 = declassify (mat[:, 3]);

    UT n1 = sum ((UT) pubIA1);
    UT n2 = sum ((UT) pubIA2);

    D IT[[1]] data1Cut ((uint) n1);
    D IT[[1]] data2Cut ((uint) n2);

    uint idx = 0;
    for (uint i = 0; i < size (pubIA1); i++) {
        if (pubIA1[i] == 1) {
            data1Cut[idx] = mat[i, 0];
            idx++;
        }
    }

    idx = 0;
    for (uint i = 0; i < size (pubIA2); i++) {
        if (pubIA2[i] == 1) {
            data2Cut[idx] = mat[i, 2];
            idx++;
        }
    }

    D IT[[2]] cutMat ((uint) max (n1, n2) , 2);
    cutMat[: (uint) n1, 0] = data1Cut;
    cutMat[: (uint) n2, 1] = data2Cut;

    D IT[[1]] sums = colSums (cutMat);
    UT[[1]] ns = {n1, n2};

    D FT[[1]] means = (FT) sums / (FT) ns;
    D FT[[2]] meanMat ((uint) max (n1, n2), 2);
    meanMat[:, 0] = means[0];
    meanMat[:, 1] = means[1];
    D FT[[2]] diffs = (FT) cutMat - meanMat;
    diffs = diffs * diffs;
    D FT[[1]] diffSum = colSums (diffs);
    D FT[[1]] variances = diffSum / (FT) ns;

    return cat(means, variances);
}

template<domain D, type IT, type UT, type FT>
D FT _combinedDegreesOfFreedom (D IT[[1]] data1,
                                D bool[[1]] ia1,
                                D IT[[1]] data2,
                                D bool[[1]] ia2,
                                UT proxy)
{
    /*
     * Welch's t-test uses the following formula for approximating
     * degrees of freedom:
     *
     * df = (variance1^2 / size1 + variance2^2 / size)^2 /
     *      (variance1^4 / (size1^2 * df1) + variance2^4 / (size2^2 * df2))
     */

    D FT[[1]] meanVar = _parallelMeanVar (data1, ia1, data2, ia2, proxy);

    // These are already declassified in _parallelMeanVar
    UT n1 = declassify (sum ((UT) ia1));
    UT n2 = declassify (sum ((UT) ia2));

    D FT var1 = meanVar[2];
    D FT var2 = meanVar[3];

    UT df1 = n1 - 1;
    UT df2 = n2 - 1;
    D FT[[1]] sqr = {var1, var2};
    sqr = sqr * sqr;

    D FT var1Sqr = sqr[0];
    D FT var2Sqr = sqr[1];

    sqr = sqr * sqr;

    D FT var1Quad = sqr[0];
    D FT var2Quad = sqr[1];

    D UT[[1]] nSqr = {n1, n2};
    nSqr = nSqr * nSqr;

    D UT[[1]] nSqrMulDf = {df1, df2};
    nSqrMulDf = nSqr * nSqrMulDf;

    D FT[[1]] divA = {var1Sqr, var2Sqr, var1Quad, var2Quad};
    D FT[[1]] divB = {(FT) n1, (FT) n2,
                      (FT) nSqrMulDf[0], (FT) nSqrMulDf[1]};
    D FT[[1]] divRes = divA / divB;

    D FT dividend = divRes[0] + divRes[1];
    dividend = dividend * dividend;

    return dividend / (divRes[2] + divRes[3]);
}
/** \endcond */

/**
 * \addtogroup hypothesis_testing_constants
 * @{
 * @brief Constants used for specifying the alternative hypothesis.
 */
int64 ALTERNATIVE_LESS      = 0;
int64 ALTERNATIVE_GREATER   = 1;
int64 ALTERNATIVE_TWO_SIDED = 2;
/** @} */


/** \addtogroup t_test
 *  @{
 *  @brief Perform t-tests
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @param data - input vector
 *  @param cases - vector indicating which elements of the input
 *  vector belong to the first sample
 *  @param controls - vector indicating which elements of the input
 *  vector belong to the second sample
 *  @param variancesEqual - indicates if the variances of the two
 *  samples should be treated as equal
 *  @return returns the test statistic
 */
template<domain D : shared3p>
D float32 tTest (D int32[[1]] data, D bool[[1]] cases, D bool[[1]] controls, bool variancesEqual) {
    return _tTest (data, cases, controls, variancesEqual);
}

template<domain D : shared3p>
D float64 tTest (D int64[[1]] data, D bool[[1]] cases, D bool[[1]] controls, bool variancesEqual) {
    return _tTest (data, cases, controls, variancesEqual);
}
/** @} */

/** \addtogroup t_test_samples
 *  @{
 *  @brief Perform t-tests
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @param data1 - first sample
 *  @param ia1 - vector indicating which elements of the first sample are available
 *  @param data2 - second sample
 *  @param ia2 - vector indicating which elements of the second sample are available
 *  @param variancesEqual - indicates if the variances of the two
 *  samples should be treated as equal
 *  @return returns the test statistic
 */
template<domain D : shared3p>
D float32 tTest (D int32[[1]] data1,
                 D bool[[1]] ia1,
                 D int32[[1]] data2,
                 D bool[[1]] ia2,
                 bool variancesEqual)
{
    uint32 proxy;
    return _tTest (data1, ia1, data2, ia2, variancesEqual, proxy);
}

template<domain D : shared3p>
D float64 tTest (D int64[[1]] data1,
                 D bool[[1]] ia1,
                 D int64[[1]] data2,
                 D bool[[1]] ia2,
                 bool variancesEqual)
{
    uint64 proxy;
    return _tTest (data1, ia1, data2, ia2, variancesEqual, proxy);
}
/** @} */

/** \addtogroup combined_df
 *  @{
 *  @brief Approximate the degrees of freedom of a linear combination
 *  of independent sample variances
 *  @note Uses the Welch-Satterthwaite equation. It's useful for
 *  calculating the degrees of freedom when performing a t-test on
 *  samples with unequal variances (Welch's t-test).
 *  @note **D** - any protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @param data1 - first sample
 *  @param ia1 - vector indicating which elements of the first sample
 *  are available
 *  @param data2 - second sample
 *  @param ia2 - vector indicating which elements of the second sample
 *  are available
 *  @return returns the approximated number of degrees of freedom
 */
template<domain D>
D float32 combinedDegreesOfFreedom (D int32[[1]] data1,
                                    D bool[[1]] ia1,
                                    D int32[[1]] data2,
                                    D bool[[1]] ia2)
{
    uint32 proxy;
    return _combinedDegreesOfFreedom (data1, ia1, data2, ia2, proxy);
}

template<domain D>
D float64 combinedDegreesOfFreedom (D int64[[1]] data1,
                                    D bool[[1]] ia1,
                                    D int64[[1]] data2,
                                    D bool[[1]] ia2)
{
    uint64 proxy;
    return _combinedDegreesOfFreedom (data1, ia1, data2, ia2, proxy);
}
/** @} */

/** \cond */
template <domain D : shared3p, type T, type FT>
D FT _pairedTTest (D T[[1]] sample1, D T[[1]] sample2, D bool[[1]] filter, FT constant) {

    assert (size (sample1) == size (filter) && size (sample1) == size (sample2));
    uint sizeData = size (sample1);

    D T[[1]] differences = sample1 - sample2;

    D uint32 count = sum ((uint32) filter);
    D T[[1]] filteredData (sizeData);
    filteredData = differences * (T) filter;

    D FT mean = mean (filteredData, filter);
    D FT var = _variance (filteredData, filter, mean);
    D FT stDev = sqrt (var);
    D FT sqrtN = sqrt ((FT) count);

    D FT result;
    if (constant == 0) {
        result = (mean * sqrtN) / stDev;
    } else {
        result = ((mean - constant) * sqrtN) / stDev;
    }

    return result;
}
/** \endcond */


/** \addtogroup paired_t_test
 *  @{
 *  @brief Perform paired t-tests
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @param sample1 - first sample
 *  @param sample2 - second sample
 *  @param filter - vector indicating which elements of the sample to
 *  include in computing the t value
 *  @param constant - hypothesized difference of means (set to 0 if
 *  testing for equal means)
 *  @return returns the t-value
 */
template <domain D : shared3p>
D float32 pairedTTest (D int32[[1]] sample1, D int32[[1]] sample2, D bool[[1]] filter, float32 constant) {
    return _pairedTTest (sample1, sample2, filter, constant);
}

template <domain D : shared3p>
D float64 pairedTTest (D int64[[1]] sample1, D int64[[1]] sample2, D bool[[1]] filter, float64 constant) {
    return _pairedTTest (sample1, sample2, filter, constant);
}
/** @} */


/** \cond */
template <domain D, type T, type FT, type UT>
D FT _chiSquared2Classes (D UT[[2]] contTable, T dummy)
{
    D FT result;
    D UT a, b, c, d;

    a = contTable[0, 0];
    b = contTable[0, 1];
    c = contTable[1, 0];
    d = contTable[1, 1];

    D T x1;
    D UT y1;

    x1 = (T) (a * d) - (T) (b * c);
    x1 = x1 * x1;
    x1 = x1 * (T) (a + b + c + d);

    y1 = (a + b) * (c + d) * (a + c) * (b + d);

    result = (FT) x1 / (FT) y1;

    return result;
}

// For reference, see Test 43 in the book "100 Statistical Tests"
template <domain D, type T, type FT, type UT>
D FT _chiSquaredXClasses (D UT[[2]] contTable, T dummy) {

    // Calculate expected frequencies as {(row subtotal x column subtotal) / total}
    uint[[1]] shapeContingency = shape (contTable);
    uint k = shapeContingency[0];

    D UT[[1]] colSums (k), rowSums (2);
    colSums = contTable[: , 0] + contTable[: , 1];
    rowSums[0] = sum (contTable [: , 0]);
    rowSums[1] = sum (contTable [: , 1]);
    D UT total = rowSums[0] + rowSums[1];
    D UT[[1]] mulParA (2 * k), mulParB (2 * k), mulParRes (2 * k);

    mulParA [0 : k] = colSums;
    mulParA [k : 2 * k] = colSums;
    mulParB [0 : k] = rowSums[0];
    mulParB [k : 2 * k] = rowSums[1];
    mulParRes = mulParA * mulParB;

    D FT[[1]] totals (k * 2) = (FT) total;
    D FT[[1]] expectedFreq = (FT) mulParRes / totals;

    D FT[[1]] flatFreq (k * 2);

    flatFreq[0:k] = (FT)contTable [:, 0];
    flatFreq[k:k * 2] = (FT)contTable [:, 1];

    // Calculate sum ((realFreq - expectedFreq)**2 / expectedFreq) in parallel as much as possible
    D FT[[1]] diffs (k * 2), squares (k * 2), quotients (k * 2);

    diffs = flatFreq - expectedFreq;
    squares = diffs * diffs;
    quotients = squares / expectedFreq;

    return sum (quotients);
}
/** \endcond */

/** \addtogroup chisq
 *  @{
 *  @brief Perform Pearson's chi-squared test of independence
 *  @note **D** - any protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @note This version does not do continuity correction so the R
 *  equivalent is chisq.test(contingencyTable, correct=FALSE)
 *  @param contTable - contingency table in the format
 *  <table>
 *  <tr><td></td><td>Cases</td><td>Controls</td></tr>
 *  <tr><td>Option 1</td><td>c1</td><td>d1</td></tr>
 *  <tr><td>Option 2</td><td>c2</td><td>d2</td></tr>
 *  <tr><td>Option 3</td><td>c3</td><td>d3</td></tr>
 *  <tr><td>…</td><td>…</td><td>…</td></tr>
 *  </table>
 *  @return returns the test statistic
 */
template <domain D>
D float32 chiSquared (D uint32[[2]] contTable) {
    uint[[1]] tableShape = shape (contTable);
    assert (tableShape[0] >= 2 && tableShape[1] == 2);

    int32 i;

    if (shape(contTable)[0] == 2)
        return _chiSquared2Classes (contTable, i);
    else
        return _chiSquaredXClasses (contTable, i);
}

template <domain D>
D float64 chiSquared (D uint64[[2]] contTable) {
    uint[[1]] tableShape = shape (contTable);
    assert (tableShape[0] >= 2);
    assert (tableShape[1] == 2);

    int64 i;

    if (shape(contTable)[0] == 2)
        return _chiSquared2Classes (contTable, i);
    else
        return _chiSquaredXClasses (contTable, i);
}
/** @} */


/** \addtogroup chisq_cb
 *  @{
 *  @brief Perform Pearson's chi-squared test of independence
 *  @note **D** - any protection domain
 *  @note Supported types - \ref uint32 "uint32" / \ref uint64 "uint64"
 *  @note This version does not do continuity correction so the R
 *  equivalent is chisq.test(contingencyTable, correct=FALSE)
 *  @param data - input vector
 *  @param cases - vector indicating which elements of the input
 *  vector belong to the first sample
 *  @param controls - vector indicating which elements of the input
 *  vector belong to the second sample
 *  @param codeBook - matrix used for creating the contingency
 *  table. The first row contains expected values of the input vector
 *  and the second row contains the classes that these values will be
 *  put into. The classes should begin with 1.
 *  @return returns the test statistic
 */
template <domain D>
D float32 chiSquared (D uint32[[1]] data,
                      D bool[[1]] cases,
                      D bool[[1]] controls,
                      uint32[[2]] codeBook)
{

    D uint32[[2]] contTable = contingencyTable (data, cases, controls, codeBook);
    return chiSquared (contTable);
}

template <domain D>
D float64 chiSquared (D uint64[[1]] data,
                      D bool[[1]] cases,
                      D bool[[1]] controls,
                      uint64[[2]] codeBook)
{
    D uint64[[2]] contTable = contingencyTable (data, cases, controls, codeBook);
    return chiSquared (contTable);
}
/** @} */


/** \cond */
template <domain D : shared3p, type T, type FT>
D FT[[1]] _rank (D T[[1]] data) {
    uint N = size(data);
    D T[[2]] matA (N, N);
    D T[[2]] matB (N, N);
    T[[1]] ranks(N);

    // On row i of matA, we want a filter indicating which values of
    // the data vector equal data[i]
    for (uint i = 0; i < N; i++) {
        matA[i, :] = data;
        matB[i, :] = data[i];
        ranks[i] = (T) (i + 1);
    }
    matA = (T) (matA == matB);

    for (uint i = 0; i < N; i++) {
        matB[i, :] = ranks;
    }

    // Calculate the average of the ranks where the data values are equal
    return (FT) rowSums(matA * matB) / (FT) rowSums(matA);
}

template <domain D : shared3p, type T, type FT>
D FT[[1]] _wilcoxonRankSum (D T[[1]] sample1,
                            D bool[[1]] ia1,
                            D T[[1]] sample2,
                            D bool[[1]] ia2,
                            bool correctRanks,
                            int64 alternative)
{
    // Zero will indicate that the matrix row is from sample2, one
    // indicates that it's from sample1.
    D T[[2]] mat (size (sample1) + size (sample2), 2);
    mat[: size (sample1), 0] = sample1;
    mat[: size (sample1), 1] = 1;
    mat[size (sample1) :, 0] = sample2;
    mat[size (sample1) :, 1] = 0;

    // Remove unavailable elements and sort
    mat = _cut (mat, cat (ia1, ia2));
    mat = sortingNetworkSort (mat, 0 :: uint);

    uint N = shape (mat)[0];

    // Use the rank sum of the first sample
    D FT w;
    if (correctRanks) {
        // Replace tied ranks with their average
        D FT[[1]] ranksFixed = _rank (mat[:, 0]);
        w = sum (ranksFixed * (FT) mat[:, 1]);
    } else {
        T[[1]] ranks (N);
        for (uint i = 0; i < N; i++) {
            ranks[i] = (T) i + 1;
        }
        w = (FT) sum (ranks * mat[:, 1]);
    }

    // Calculate z score
    D FT n1 = (FT) sum ((T) ia1);
    D FT n2 = (FT) sum ((T) ia2);
    D FT meanW = n1 * ((FT) N + 1) / 2;
    D FT sigma = sqrt (n1 * n2 * ((FT) N + 1) / 12);
    D FT z;
    FT correction;

    // Continuity correction
    assert (alternative == ALTERNATIVE_LESS ||
            alternative == ALTERNATIVE_GREATER ||
            alternative == ALTERNATIVE_TWO_SIDED);

    if (alternative == ALTERNATIVE_LESS)
        correction = 0.5;
    else if (alternative == ALTERNATIVE_GREATER)
        correction = -0.5;
    else if (alternative == ALTERNATIVE_TWO_SIDED)
        correction = -0.5;

    z = ((w - meanW) + correction) / sigma;

    D FT[[1]] res = {w, z};

    return res;
}
/** \endcond */


/** \addtogroup wilcoxon_rank_sum
 *  @{
 *  @brief Perform Wilcoxon rank sum tests
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @note The t-test requires the populations to be normally
 *  distributed. If the populations cannot be assumed to be normally
 *  distributed but are ordinal then the Mann-Whitney U or Wilcoxon
 *  rank-sum test can be used instead.
 *  @param sample1 - first sample
 *  @param ia1 - vector indicating which elements of the first sample
 *  are available
 *  @param sample2 - second sample
 *  @param ia2 - vector indicating which elements of the second sample
 *  are available
 *  @param correctRanks - indicates if the equal sample values should
 *  be ranked correctly. If they are not the test is more conservative
 *  but faster.
 *  @param alternative - the type of alternative hypothesis. Less -
 *  mean of sample1 is less than mean of sample2, greater - mean of
 *  sample1 is greater than mean of sample2, two-sided - means of
 *  sample1 and sample2 are different
 *  @return returns a vector where the first element is the test
 *  statistic and the second element is the z-score. The z-score is
 *  continuity corrected. The z-score is an approximation and its
 *  values are only correct when both samples have at least 5
 *  elements.
 */
template <domain D : shared3p>
D float32[[1]] wilcoxonRankSum (D int32[[1]] sample1,
                                D bool[[1]] ia1,
                                D int32[[1]] sample2,
                                D bool[[1]] ia2,
                                bool correctRanks,
                                int64 alternative)
{
    return _wilcoxonRankSum (sample1, ia1, sample2, ia2, correctRanks, alternative);
}

template <domain D : shared3p>
D float64[[1]] wilcoxonRankSum (D int64[[1]] sample1,
                                D bool[[1]] ia1,
                                D int64[[1]] sample2,
                                D bool[[1]] ia2,
                                bool correctRanks,
                                int64 alternative)
{
    return _wilcoxonRankSum (sample1, ia1, sample2, ia2, correctRanks, alternative);
}
/** @} */

/** \cond */

/*
 * Mann-Whitney U from "Nonparametric Statistical Methods". Z-score
 * from "Biostatistical Analysis".
 */
template <domain D : shared3p, type T, type FT>
D FT[[1]] _mannWhitneyU (D T[[1]] sample1,
                         D bool[[1]] ia1,
                         D T[[1]] sample2,
                         D bool[[1]] ia2,
                         bool correctRanks,
                         int64 alternative)
{
    // Zero will indicate that the matrix row is from sample2, one
    // indicates that it's from sample1.
    D T[[2]] mat (size (sample1) + size (sample2), 2);
    mat[: size (sample1), 0] = sample1;
    mat[: size (sample1), 1] = 1;
    mat[size (sample1) :, 0] = sample2;
    mat[size (sample1) :, 1] = 0;

    // Remove unavailable elements and sort
    mat = _cut (mat, cat (ia1, ia2));
    mat = sortingNetworkSort (mat, 0 :: uint);

    // Note: can't go from uint64 to float32
    D uint32 n1 = sum ((uint32) ia1);
    D uint32 n2 = sum ((uint32) ia2);
    D FT n1n2 = (FT) (n1 * n2);
    uint N = shape (mat)[0];

    D FT sum1;
    if (correctRanks) {
        D FT[[1]] ranks = _rank (mat[:, 0]);
        sum1 = sum (ranks * (FT) mat[:, 1]);
    } else {
        T[[1]] ranks (N);
        for (uint64 i = 0; i < N; i = i + 1) {
            ranks[i] = (T) i + 1;
        }
        sum1 = (FT) sum (ranks * mat[:, 1]);
    }

    D FT U1 = sum1 - ((FT) n1 * ((FT) n1 + 1)) / 2;
    D FT U2 = n1n2 - U1;
    D FT U = choose (U1 < U2, U1, U2);

    // Calculate z-score from U1 (it doesn't matter which one we use).
    FT correction;
    D FT meanU = n1n2 / 2;
    D FT sigmaU = sqrt (n1n2 * (FT) (N + 1) / 12);
    D FT z;

    // Continuity correction
    assert (alternative == ALTERNATIVE_LESS ||
            alternative == ALTERNATIVE_GREATER ||
            alternative == ALTERNATIVE_TWO_SIDED);

    if (alternative == ALTERNATIVE_LESS)
        correction = 0.5;
    else if (alternative == ALTERNATIVE_GREATER)
        correction = -0.5;
    else if (alternative == ALTERNATIVE_TWO_SIDED)
        correction = -0.5;

    z = ((U - meanU) + correction) / sigmaU;

    D FT[[1]] res(2) = {U, z};

    return res;
}
/** \endcond */

/**
 * \addtogroup mann_whitney_u
 * @{
 * @brief Perform Mann-Whitney U test
 * @note **D** - shared3p protection domain
 * @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 * @note The t-test requires the populations to be normally
 * distributed. If the populations cannot be assumed to be normally
 * distributed but are ordinal then the Mann-Whitney U or Wilcoxon
 * rank-sum test can be used instead.
 * @param sample1 - first sample
 * @param ia1 - vector indicating which elements of the first sample
 * are available
 * @param sample2 - second sample
 * @param ia2 - vector indicating which elements of the second sample
 * are available
 * @param correctRanks - indicates if the equal sample values should
 * be ranked correctly. If they are not the test is more conservative
 * but faster.
 * @param alternative - the type of alternative hypothesis. Less -
 * mean of sample1 is less than mean of sample2, greater - mean of
 * sample1 is greater than mean of sample2, two-sided - means of
 * sample1 and sample2 are different
 * @return returns a vector where the first element is the test
 * statistic and the second element is the z-score. The z-score is
 * continuity corrected. The z-score is an approximation and is only
 * correct when the samples are large and the significance level is
 * not very low.
 */
template <domain D : shared3p>
D float32[[1]] mannWhitneyU (D int32[[1]] sample1,
                             D bool[[1]] ia1,
                             D int32[[1]] sample2,
                             D bool[[1]] ia2,
                             bool correctRanks,
                             int64 alternative)
{
    return _mannWhitneyU (sample1, ia1, sample2, ia2, correctRanks, ALTERNATIVE_TWO_SIDED);
}

template <domain D : shared3p>
D float64[[1]] mannWhitneyU (D int64[[1]] sample1,
                             D bool[[1]] ia1,
                             D int64[[1]] sample2,
                             D bool[[1]] ia2,
                             bool correctRanks,
                             int64 alternative)
{
    return _mannWhitneyU (sample1, ia1, sample2, ia2, correctRanks, ALTERNATIVE_TWO_SIDED);
}
/** @} */

/** \cond */
template <domain D : shared3p, type T, type FT>
D FT[[1]] _wilcoxonSignedRank (D T[[1]] sample1,
                               D T[[1]] sample2,
                               D bool[[1]] filter,
                               bool correctRanks,
                               int64 alternative)
{
    assert (size (sample1) == size (sample2) && size (sample1) == size (filter));

    // Pairs whose difference is zero are dropped
    D T[[1]] differences = sample1 - sample2;
    filter = filter && (differences != 0);

    D T[[2]] bothSamples (size (sample1), 2);
    bothSamples[:, 0] = sample1;
    bothSamples[:, 1] = sample2;
    bothSamples = cut (bothSamples, filter);

    differences = bothSamples[:, 0] - bothSamples[:, 1];
    uint n = size (differences);
    D T[[1]] signs = sign (differences);
    D T[[1]] absDiffs = (T) abs (differences);

    // Sort a matrix with sign and absolute difference columns by the
    // difference column
    D T[[2]] signAndMagnitude (n, 2);
    signAndMagnitude[:, 0] = signs;
    signAndMagnitude[:, 1] = absDiffs;
    signAndMagnitude = sortingNetworkSort(signAndMagnitude, 1 :: uint);
    signs = signAndMagnitude[:, 0];
    absDiffs = signAndMagnitude[:, 1];

    // Calculate test statistic
    D FT w;
    if (correctRanks) {
    // Replace tied ranks with their average
        D FT[[1]] ranksFixed = _rank (absDiffs);
        w = sum (ranksFixed * (FT) signs);
    } else {
        T[[1]] ranks (n);
        for (uint i = 0; i < n; i++) {
            ranks[i] = (T) i + 1;
        }
        w = (FT) sum (signs * ranks);
    }

    // Calculate z score
    D FT z = w;
    FT sigma = sqrt ((FT) (n * (n + 1) * (2 * n + 1)) / 6);
    FT correction;

    // Continuity correction
    assert (alternative == ALTERNATIVE_LESS ||
            alternative == ALTERNATIVE_GREATER ||
            alternative == ALTERNATIVE_TWO_SIDED);

    if (alternative == ALTERNATIVE_LESS)
        correction = 0.5;
    else if (alternative == ALTERNATIVE_GREATER)
        correction = -0.5;
    else if (alternative == ALTERNATIVE_TWO_SIDED)
        correction = -0.5;

    z = (z + correction) / sigma;

    D FT[[1]] res = {w, z};

    return res;
}
/** \endcond */


/** \addtogroup wilcoxon_signed_rank
 *  @{
 *  @brief Perform Wilcoxon signed rank tests.
 *  @note The paired t-test requires the populations to be normally
 *  distributed. If the populations cannot be assumed to be normally
 *  distributed but are ordinal then the Wilcoxon signed rank test can
 *  be used instead.
 *  @note **D** - shared3p protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @note This function does not match the one in R.
 *  @param sample1 - first  sample
 *  @param sample2 - second sample
 *  @param filter - vector indicating which elements of the sample to
 *  include in computing the statistic
 *  @param correctRanks - indicates if the equal sample values should
 *  be ranked correctly. If they are not the test is more conservative
 *  but faster.
 *  @param alternative - the type of alternative hypothesis. Less -
 *  mean of sample1 is less than mean of sample2, greater - mean of
 *  sample1 is greater than mean of sample2, two-sided - means of
 *  sample1 and sample2 are different
 *  @return returns a vector where the first element is the test
 *  statistic and the second element is the z-score. The z-score is
 *  continuity corrected. The z-score is an approximation and when
 *  there's less than 10 pairs with non-zero difference, it's
 *  incorrect.
 */
template <domain D : shared3p>
D float32[[1]] wilcoxonSignedRank (D int32[[1]] sample1, D int32[[1]] sample2, D bool[[1]] filter, bool correctRanks, int64 alternative) {
    return _wilcoxonSignedRank (sample1, sample2, filter, correctRanks, alternative);
}

template <domain D : shared3p>
D float64[[1]] wilcoxonSignedRank (D int64[[1]] sample1, D int64[[1]] sample2, D bool[[1]] filter, bool correctRanks, int64 alternative) {
    return _wilcoxonSignedRank (sample1, sample2, filter, correctRanks, alternative);
}
/** @} */

/** \cond */
template <domain D : shared3p, type FT>
D uint[[1]] _benjaminiHochberg (D FT[[1]] statistics,
                                FT[[1]] quantiles)
{
    assert (size (statistics) == size (quantiles));

    // Columns: statistics, indices, quantiles
    D FT[[2]] mat (size (statistics), 3);
    mat[:, 0] = statistics;
    mat[:, 2] = quantiles;

    uint32[[1]] indices (size (statistics));
    for (uint i = 0; i < size (statistics); i++) {
        indices[i] = (uint32) i;
    }
    // Note: can't go from uint to float32
    mat[:, 1] = (FT) indices;

    mat = sort (mat, 0 :: uint);
    D bool[[1]] comp = mat[:, 0] >= mat[:, 2];

    for (uint i = 0; i < size (comp); i++) {
        bool compPub = declassify (comp[i]);
        if (compPub) {
            return (uint) mat[i :, 1];
        }
    }

    D uint[[1]] res;
    return res;
}
/** \endcond */

/** \addtogroup multiple_testing
 *  @{
 *  @brief Perform the Benjamini-Hochberg procedure for false
 *  discovery rate control.
 *  @note If multiple variables of a dataset are used for testing a
 *  hypothesis then this procedure will help avoid false discoveries
 *  (incorrectly rejected null hypothesis). This procedure is only
 *  correct when the alternative hypothesis is of the upper tail kind.
 *  @note **D** - shared3p protection domain
 *  @param statistics - vector of calculated test statistics
 *  @param quantiles - vector of critical values for the test statistics
 *  @return returns the indices of the tests for which the null
 *  hypothesis is rejected
 */
template <domain D : shared3p>
D uint[[1]] multipleTesting (D float32[[1]] statistics, float32[[1]] quantiles) {
    return _benjaminiHochberg (statistics, quantiles);
}

template <domain D : shared3p>
D uint[[1]] multipleTesting (D float64[[1]] statistics, float64[[1]] quantiles) {
    return _benjaminiHochberg (statistics, quantiles);
}
/** @} */

/** @} */

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
module shared3p_statistics_distribution;

import shared3p_matrix;
import shared3p_sort;
import shared3p_statistics_common;
import shared3p_statistics_summary;
import shared3p;
import stdlib;
/** \endcond */


/**
 * @file
 * \defgroup shared3p_statistics_distribution shared3p_statistics_distribution.sc
 * \defgroup histogram histogram
 * \defgroup discreteDistributionCount discreteDistributionCount
 * \defgroup discreteDistributionCount_stepSize discreteDistributionCount(with stepSize)
 * \defgroup heatmap heatmap
 */

/** \addtogroup shared3p_statistics_distribution
 *  @{
 *  @brief Module for visualising distribution of data.
 */


/** \cond */
// Sturges' formula calculates the number of breaks in the histogram
// k = ceiling (log2(n) + 1)
uint64 _getNoOfBreaks (uint64 sizeData){
    uint64 k = 1;

    for (uint powOf2 = 2; powOf2 < sizeData; powOf2 = powOf2 * 2) {
        k++;
    }

    return (k + 1);
}

// Gives the sequence of breaks
// NOTE: Currently not used
float64[[1]] _getExactBreaksHist (uint64 min, uint64 max, uint64 noOfBreaks) {
    float64 stepSize = (float64)(max - min) / (float64) noOfBreaks;
    float64[[1]] breaks (noOfBreaks + 1);
    for (uint i = 0; i < noOfBreaks; i = i + 1){
        breaks[i] = (float64) min + stepSize * (float64) i;
    }
    breaks[noOfBreaks] = (float64) max;
    return breaks;
}


template<type T>
T[[1]] _getApproximateBreaksHist (T min, T max, uint64 noOfBreaks) {
    uint64 stepSize = 0;
    uint64 difference = (uint)(max - min);

    if (difference % noOfBreaks == 0) {
        stepSize  = difference / noOfBreaks;
    } else {
        stepSize  = (difference / noOfBreaks) + 1;
    }

    T[[1]] breaks (noOfBreaks + 1);
    for (uint i = 0; i < noOfBreaks + 1; i = i + 1) {
        breaks[i] = min + (T)(i * stepSize);
    }

    return breaks;
}

template<type T>
uint _niceStep (T min, T max, uint idealIntervalCount) {
    assert (idealIntervalCount > 1);
    assert (max > min);

    uint[[1]] niceSmall = {1, 2, 5};
    uint[[1]] niceBig = {10, 20, 25, 50};
    uint range = (uint) (max - min);
    float64 stepF = max ((float64) range / (float64) idealIntervalCount, 1 :: float64);
    uint exp = 0;
    bool found = false;
    uint step = niceSmall[0];
    uint next_step;

    // Find a 'nice' step size closest to stepF

    // First search small steps
    for (uint i = 0; i < size (niceSmall); i++) {
        if ((float64) niceSmall[i] < stepF) {
            step = niceSmall[i];
            if (i == size (niceSmall) - 1)
                next_step = niceBig[0];
            else
                next_step = niceSmall[i + 1];
        } else {
            found = true;
            break;
        }
    }

    // Now search among {x * 10^z, x <- niceBig, z <- 0, 1, ...}
    while (!found) {
        for (uint i = 0; i < size (niceBig); i++) {
            uint cur_step = niceBig[i] * _power (10 :: uint, exp);
            if ((float64) cur_step < stepF) {
                step = cur_step;
                if (i != size (niceBig) - 1)
                    next_step = niceBig[i] * _power (10 :: uint, exp);
                else
                    next_step = niceBig[0] * _power (10 :: uint, exp + 1);
            } else {
                found = true;
                break;
            }
        }
        exp++;
    }

    if (abs ((float64) next_step - stepF) < abs ((float64) step - stepF))
        step = next_step;

    return step;
}

template<type T>
T _roundToMultiple (T x, uint to) {
    // Integer division is rounded towards zero so we need to handle
    // the case when 'min' is negative separately. If 'min' can be
    // represented as a multiple of 'step' then everything is fine.
    if (x >= 0 || x % (T) to == 0)
        return (x / (T) to) * (T) to;
    else
        return ((x / (T) to) - 1) * (T) to;
}

template<type T>
T[[1]] _niceTics (T min, T max, uint idealIntervalCount) {
    assert (idealIntervalCount > 1);
    assert (max >= min);

    if (max == min)
        max++;

    uint step = _niceStep (min, max, idealIntervalCount);
    min = _roundToMultiple (min, step);

    T[[1]] tics;
    T val = min;
    while (true) {
        T[[1]] singleton = {val};
        tics = cat (tics, singleton);
        val += (T) step;

        if (singleton[0] >= max)
            break;
    }

    return tics;
}

template<domain D, type T>
D T[[2]] _histogram (D T[[1]] data, D bool[[1]] isAvailable) {
    D T[[1]] data = cut (data, isAvailable);
    uint dataSize = size (data);

    if (dataSize < 5) {
        D T[[2]] result;
        return result;
    }

    T min = declassify (min (data));
    T max = declassify (max (data));

    uint noBreaks = _getNoOfBreaks (dataSize);
    T[[1]] breaks = _niceTics (min, max, noBreaks);

    uint countsSize = size (breaks) - 1;
    D T[[1]] counts (countsSize);
    D T[[2]] dataMat (countsSize, dataSize);
    D T[[2]] breakMat (countsSize, dataSize);

    for (uint i = 0; i < countsSize; i++) {
        dataMat[i, :] = data;
        breakMat[i, :] = breaks[i + 1];
    }

    counts = rowSums ((T) (dataMat <= breakMat));

    for (int i = (int) countsSize - 1; i > 0; i--) {
        counts[(uint) i] -= counts[(uint) i - 1];
    }

    D T[[2]] result (2, size (breaks));
    result[0, :] = breaks;
    result[1, : size (breaks) - 1] = counts;

    return result;
}


template<domain D, type T>
D T[[2]] _discreteDistributionCount (D T[[1]] data, D bool[[1]] isAvailable, D T min, D T max, D T stepSize) {

    D T[[1]] cutData = cut (data, isAvailable);

    uint sizeData = size (cutData);

    // Why exactly 5? Should it be bigger than 5?
    if (sizeData < 5) {
        D T[[2]] result;
        return result;
    }

    // Number of "columns" (different possible values).
    uint cols = (uint)declassify ((max - min)) + 1;
    // Already declassifying something (matrix size).
    D T[[2]] result (2, cols) = stepSize;

    uint compSize = sizeData * cols;
    // Vectors for parallel computations.
    D T[[1]] compA (compSize), compB (compSize), compC (compSize);

    uint startIndex, endIndex;  // Tmp for loop.
    D T colVal = 0;
    // compA contains cols times cutData vector. (val1, val2, val3, val1, val2, val3)
    // compB contains sizeData times values from "columns". (col1, col1, col1, col2, col2, col2)
    // While we're at it we can also populate first row of result matrix.
    // (As we don't have {1..10} and { x * x | x <- {1..10}} syntax YET, have to do it with loops.)
    for (uint i = 0; i < cols; ++i)
    {
        startIndex = i * sizeData;
        endIndex = (i + 1) * sizeData;
        compA[startIndex:endIndex] = cutData;
        // Here we declassify stepSize. Problem? No? Probably should make stepSize parameter public.
        colVal = min + (T)(i * (uint)declassify(stepSize));
        compB[startIndex:endIndex] = colVal;

        result[0,i] = colVal;
    }

    // Here we get match between cutData value and distribution class value.
    compC = (T)(compA == compB);

    // We need to get "cols" sums. This way compC is split into "cols" arrays (each containing sizeData elements).
    result[1,:] = sum (compC, cols);

    return result;
}

template<type T>
T _max (T x, T y) {
    T[[1]] z = {x, y};
    return max (z);
}

template <domain D : shared3p, type T, type UT>
D T[[2]] _heatmap (D T[[1]] x,
                   D T[[1]] y,
                   D bool[[1]] xIsAvailable,
                   D bool[[1]] yIsAvailable,
                   uint K,
                   UT unsignedBuddy)
{
    assert (size (x) == size (y));

    uint dataSize = size (x);

    // If either data vector has a missing sample then we are missing
    // a point on the plot.
    D bool[[1]] isAvailable = xIsAvailable && yIsAvailable;

    // Cut two samples with one mask.
    D T[[2]] mat (dataSize, 2);
    mat[:,0] = x;
    mat[:,1] = y;
    mat = cut (mat, isAvailable);

    T xmin = declassify (min (mat[:,0]));
    T xmax = declassify (max (mat[:,0]));
    T ymin = declassify (min (mat[:,1]));
    T ymax = declassify (max (mat[:,1]));

    uint s = _getNoOfBreaks (dataSize);
    uint xstep = max (K, _niceStep (xmin, xmax, s));
    uint ystep = max (K, _niceStep (ymin, ymax, s));
    xmin = _roundToMultiple (xmin, xstep);
    ymin = _roundToMultiple (ymin, ystep);

    // z will be a matrix where each element counts the number of
    // points falling in a specific bin. The bins are sequential, ie
    // element (a, b) is the a-th bin on the x-axis and b-th bin on
    // the y-axis.
    uint rows = (uint) (ymax - ymin) / ystep;
    uint columns = (uint) (xmax - xmin) / xstep;

    if ((uint) (ymax - ymin) % ystep != 0)
        rows++;

    if ((uint) (xmax - xmin) % xstep != 0)
        columns++;

    D T[[2]] z (rows, columns);

    // For each data point we'll find coordinates of its bin in z
    dataSize = shape (mat)[0];

    D T[[1]] xy (2 * dataSize);
    xy[:dataSize] = mat[:,0];
    xy[dataSize:] = mat[:,1];

    uint[[1]] steps (2 * dataSize);
    steps[:dataSize] = xstep;
    steps[dataSize:] = ystep;

    T[[1]] mins (2 * dataSize);
    mins[:dataSize] = xmin;
    mins[dataSize:] = ymin;

    D uint[[1]] bins (2 * dataSize);
    // TODO: replace with a single cast when we have T -> uint64.
    bins = (uint) (UT) (xy - mins) / steps;

    for (uint i = 0; i < rows; i++) {
        for (uint j = 0; j < columns; j++) {
            // Count the number data points that have coordinates of this bin
            D uint[[1]] zcoords (size (bins));
            zcoords[:dataSize] = j;
            zcoords[dataSize:] = i;
            D bool[[1]] eq = zcoords == bins;
            eq = eq[:dataSize] && eq[dataSize:];
            z[i, j] = (T) sum ((UT) eq);
        }
    }

    // Remove counts < K.
    z *= (T) (z >= (T) K);

    // We can't publish exact counts. So we will find ranges for z as
    // well and replace counts with bin numbers.
    D T[[1]] zflat = reshape (z, size (z));
    T zmin = declassify (min (zflat));
    T zmax = declassify (max (zflat));
    s = max (K, _getNoOfBreaks ((uint) (zmax - zmin)));
    uint zstep = _niceStep (zmin, zmax, s);
    zmin = _roundToMultiple (zmin, zstep);
    // TODO: remove casts when we can divide Ts.
    D T[[2]] gradient = (T) ((UT) (z - zmin) / (UT) zstep);

    D T[[2]] res (2, max (8 :: uint, size (z)));
    res[0, 0] = xmin;
    res[0, 1] = ymin;
    res[0, 2] = (T) xstep;
    res[0, 3] = (T) ystep;
    res[0, 4] = (T) zmin;
    res[0, 5] = (T) zstep;
    res[0, 6] = (T) rows;
    res[0, 7] = (T) columns;
    res[1, : size (gradient)] = reshape (gradient, size (gradient));

    return res;
}

/** \endcond */


/** \addtogroup histogram
 *  @{
 *  @brief Create a histogram
 *  @note **D** - any protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @param data - input vector
 *  @param isAvailable - vector indicating which elements of the input vector are available
 *  @return returns a matrix where the first row contains histogram
 *  bin boundaries and the second row contains counts for each bin
 *  (note that the last element of the second row is always 0 because
 *  for n bins we have n+1 boundaries). An element x belongs to a bin
 *  with boundaries (a, b) if a < x <= b.
 */
template<domain D>
D int32[[2]] histogram (D int32[[1]] data, D bool[[1]] isAvailable) {
    return _histogram (data, isAvailable);
}

template<domain D>
D int64[[2]] histogram (D int64[[1]] data, D bool[[1]] isAvailable) {
    return _histogram (data, isAvailable);
}
/** @} */


/** \addtogroup discreteDistributionCount
 *  @{
 *  @brief Find discrete distribution of an input vector
 *  @note **D** - any protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @param data - input vector
 *  @param isAvailable - vector indicating which elements of the input vector are available
 *  @param min - fixed lowest value in returned matrix (lower values from input vector are discarded)
 *  @param max - fixed highest value in returned matrix (higher values from input vector are discarded)
 *  @return returns a matrix where the first row contains discrete distribution values
 *  and the second row contains counts for each value
 */
/*
 * In most of the use cases stepsize is 1, so can omit that from parameters for ease of use.
 */
template<domain D>
D int32[[2]] discreteDistributionCount (D int32[[1]] data, D bool[[1]] isAvailable, D int32 min, D int32 max) {
    D int32 one = 1;    // No better idea at the moment.
    return discreteDistributionCount (data, isAvailable, min, max, one);
}

template<domain D>
D int64[[2]] discreteDistributionCount (D int64[[1]] data, D bool[[1]] isAvailable, D int64 min, D int64 max) {
    D int64 one = 1;    // No better idea at the moment.
    return discreteDistributionCount (data, isAvailable, min, max, one);
}
/** @} */

/** \addtogroup discreteDistributionCount_stepSize
 *  @{
 *  @brief Find discrete distribution of an input vector
 *  @note **D** - any protection domain
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @param data - input vector
 *  @param isAvailable - vector indicating which elements of the input vector are available
 *  @param min - fixed lowest value in returned matrix (lower values from input vector are discarded)
 *  @param max - fixed highest value in returned matrix (higher values from input vector are discarded)
 *  @param stepSize - difference between adjacent values in returned matrix
 *  (values in returned matrix are: min, min + stepSize, min + 2*stepSize, min + 3*stepSize, ...).
 *  Other values from input vector are discarded.
 *  @return returns a matrix where the first row contains discrete distribution values
 *  and the second row contains counts for each value
 */
/*
 * More possible versions of discreteDistributionCount():
 * a) instead of min/max/stepSize give vector of possible values.
 */
template<domain D>
D int32[[2]] discreteDistributionCount (D int32[[1]] data, D bool[[1]] isAvailable, D int32 min, D int32 max, D int32 stepSize) {
    return _discreteDistributionCount (data, isAvailable, min, max, stepSize);
}

template<domain D>
D int64[[2]] discreteDistributionCount (D int64[[1]] data, D bool[[1]] isAvailable, D int64 min, D int64 max, D int64 stepSize) {
    return _discreteDistributionCount (data, isAvailable, min, max, stepSize);
}

/** @} */

/** \addtogroup heatmap
 *  @{
 *  @brief Create a heatmap
 *  @note **D** - shared3p
 *  @note Supported types - \ref int32 "int32" / \ref int64 "int64"
 *  @param x - first sample
 *  @param y - second sample
 *  @param xIsAvailable - vector indicating which elements of x are available
 *  @param yIsAvailable - vector indicating which elements of y are available
 *  @param K - minimal length of bin side

 *  @note A heatmap (in this case) is a plot of two variables of a set
 *  of data. It can be used to visualise data in the same way as a
 *  scatterplot while leaking less information about individual
 *  values. Values of sample x will determine coordinates on the x
 *  axis and values of sample y will determine coordinates on the y
 *  axis. Instead of displaying individual points, this function
 *  counts the number of points in fixed rectangular areas (called
 *  bins). The counts will then be replaced with ranges.

 *  @return returns a matrix with two rows. The second row is a
 *  flattened matrix with as many elements as there are bins in the
 *  heatmap. The second row may actually be longer if there's less
 *  than 8 elements in the matrix. Each bin will contain a number,
 *  starting from 1, which indicates the frequency range of the
 *  bin. When plotting, a bin with matrix coordinates (i, j) and value
 *  z will have its lower left point at (xmin + i · xstep, ymin + j ·
 *  ystep), will have dimensions (xstep, ystep) and will indicate a
 *  frequency count in the range [zmin + z · zstep, zmin + (z + 1) ·
 *  zstep).  The first 8 elements of the first row are
 *  <table><tr><td>xmin</td><td>beginning of
 *  x-axis</td></tr><tr><td>ymin</td><td>beginning of
 *  y-axis</td></tr><tr><td>xstep</td><td>difference of x-axis
 *  tics</td></tr><tr><td>ystep</td><td>difference of y-axis
 *  tics</td></tr><tr><td>zmin</td><td>beginning of
 *  z-axis</td></tr><tr><td>zstep</td><td>difference of z-axis
 *  tics</td></tr><tr><td>rows</td><td>number of rows in the
 *  matrix</td></tr><tr><td>columns</td><td>number of columns in the
 *  matrix</td></tr></table>
 */
template <domain D : shared3p>
D int32[[2]] heatmap (D int32[[1]] x,
                      D int32[[1]] y,
                      D bool[[1]] xIsAvailable,
                      D bool[[1]] yIsAvailable,
                      uint K)
{
    uint32 buddy;
    return _heatmap (x, y, xIsAvailable, yIsAvailable, K, buddy);
}

template <domain D : shared3p>
D int64[[2]] heatmap (D int64[[1]] x,
                      D int64[[1]] y,
                      D bool[[1]] xIsAvailable,
                      D bool[[1]] yIsAvailable,
                      uint K)
{
    uint64 buddy;
    return _heatmap (x, y, xIsAvailable, yIsAvailable, K, buddy);
}
/** @} */

/** @} */

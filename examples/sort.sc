/*
 * This file is a part of the Sharemind framework.
 * Copyright (C) Cybernetica AS
 *
 * All rights are reserved. Reproduction in whole or part is prohibited
 * without the written consent of the copyright owner. The usage of this
 * code is subject to the appropriate license agreement.
 */

import stdlib; // printVector, all
import additive3pp; // additive3pp kind, (specialized all)
import a3p_random; // shuffle, randomize


/**
 * To sort an array xs the general scheme is:
 * 1. xs = shuffle (xs);
 * 2. sort xs using public comparisons: declassify (xs[i] < xs[j])
 *
 * What kind of data is leaked depends on the sorting algorithm used.  For
 * instance bubble sort would not leak anything.
 *
 * Below there's working (very inefficient) quicksort implementation using this
 * method.
 */

// pd_a3p is our test protection domain
domain pd_a3p additive3pp;

// "pd_a3p uint[[1]]" is type of one dimensional array of uint-s under pd_a3p domain
// "uint[[1]]" or "public uint[[1]]" is a public 1D array of uints

struct _partition_result {
    pd_a3p uint[[1]] ls; // <= pivot
    pd_a3p uint[[1]] rs; // > pivot
}

// append an element to the end of an array. everything is pass-by-value
pd_a3p uint[[1]] snoc (pd_a3p uint[[1]] xs, pd_a3p uint x) {
    return cat (xs, {x});
}

// partition a list by
_partition_result _partition (pd_a3p uint[[1]] xs, pd_a3p uint p) {
    pd_a3p uint[[1]] ls, rs;
    for (uint i = 0; i < size (xs); ++ i) {
        pd_a3p uint y = xs[i];
        // XXX public branching!
        if (declassify (y <= p))
            ls = snoc (ls, y);
        else
            rs = snoc (rs, y);
    }

    _partition_result result;
    result.ls = ls;
    result.rs = rs;
    return result;
}

pd_a3p uint[[1]] _sort (pd_a3p uint[[1]] xs) {
    if (size (xs) <= 1)
        return xs;

    pd_a3p uint pivot = xs[0];
    _partition_result r = _partition (xs[1:], pivot);
    pd_a3p uint[[1]] ls = _sort (r.ls);
    pd_a3p uint[[1]] rs = _sort (r.rs);
    return cat (snoc (ls, pivot), rs);
}

pd_a3p uint[[1]] sort (pd_a3p uint[[1]] xs) {
    return _sort (shuffle (xs));
}

pd_a3p bool isSorted (pd_a3p uint[[1]] xs) {
    return all (xs[:size(xs)-1] <= xs[1:]);
}

void main () {

    // Generate some public lengths via private randomization:
    pd_a3p uint8[[1]] plens (100);
    plens = randomize (plens);
    uint[[1]] lens = (uint) declassify (plens);

    for (uint i = 0; i < size (lens); ++ i) {
        pd_a3p uint[[1]] xs (lens[i]);
        xs = randomize (xs);
        xs = sort (xs);
        assert (declassify (isSorted (xs)));
    }
}

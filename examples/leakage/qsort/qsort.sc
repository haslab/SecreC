
module qsort;

import axioms;

//* Domain declarations

kind privatek;
domain private privatek;

//* Annotations

//@ template <domain D,type T>
//@ leakage function bool lcomparison (D T[[1]] xs,D T x)
//@ noinline;
//@ {
//@     forall uint i ; (0 <= i && i < size(xs)) ==> public(xs[i] <= x)
//@ }

//@ template <domain D,type T>
//@ leakage function bool lcomparisons (D T[[1]] xs)
//@ noinline;
//@ {
//@     forall uint i,uint j ; (0 <= i && i < size(xs) && 0 <= j && j < size(xs)) ==> public(xs[i] <= xs[j])
//@ }

//@ leakage lemma lcomparisons_subset <domain D,type T> (D T[[1]] xs,D T[[1]] ys)
//@ requires multiset(ys) <= multiset(xs);
//@ requires lcomparisons(xs);
//@ ensures lcomparisons(ys);

//@ leakage lemma lcomparison_subset <domain D,type T> (D T[[1]] xs,D T[[1]] ys, D T z)
//@ requires multiset(ys) <= multiset(xs);
//@ requires in(z,xs);
//@ requires lcomparisons(xs);
//@ ensures lcomparison(ys,z);

//@ lemma ArrayHead <domain D,type T> (D T[[1]] xs)
//@ requires size(xs) > 1;
//@ ensures xs == cat({xs[0]},xs[1:]);

//* Code

struct partition_result {
    private uint[[1]] ls; // <= pivot
    private uint[[1]] rs; // > pivot
}

// append an element to the end of an array. everything is pass-by-value
private uint[[1]] snoc (private uint[[1]] xs, private uint x) {
    return cat (xs, {x});
}

// partition a list by
// the intermediate comparisons cannot be computed from the public values. they leak the "shape" of the input.
partition_result partition (private uint[[1]] xs, private uint p)
//@ leakage requires lcomparison(xs,p);
//@ ensures multiset(xs) == multiset(\result.ls) + multiset(\result.rs);
{
    private uint[[1]] ls, rs;
    for (uint i = 0; i < size (xs); i=i+1)
    //@ invariant 0 <= i && i <= size(xs);
    //@ invariant multiset(xs[:i]) == multiset(ls) + multiset(rs);
    {
        private uint y = xs[i];
        // XXX public branching!
        if (declassify (y <= p)) ls = snoc (ls, y);
        else rs = snoc (rs, y);
    }

    partition_result result;
    result.ls = ls;
    result.rs = rs;
    return result;
}

private uint[[1]] leaky_sort (private uint[[1]] xs)
//@ decreases size(xs);
//@ leakage requires lcomparisons(xs);
//@ ensures multiset(xs) == multiset(\result);
{
    if (size(xs) <= 1) return xs;

    //@ ArrayHead(xs);

    private uint pivot = xs[0];
    //@ leakage lcomparison_subset(xs,xs[1:],pivot);
    partition_result r = partition (xs[1:], pivot);
    //@ leakage lcomparisons_subset(xs,r.ls);
    private uint[[1]] ls = leaky_sort (r.ls);
    //@ leakage lcomparisons_subset(xs,r.rs);
    private uint[[1]] rs = leaky_sort (r.rs);
    return cat (snoc (ls, pivot), rs);
}

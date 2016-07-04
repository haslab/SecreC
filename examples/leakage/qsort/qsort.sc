
module qsort;

import axioms;

kind privatek;
domain private privatek;

function int declassify(private int x) {
    __builtin("core.declassify",x) :: int
}
function uint declassify(private uint x) {
    __builtin("core.declassify",x) :: uint
}
function bool declassify(private bool x) {
    __builtin("core.declassify",x) :: bool
}
function private int classify(int x) {
    __builtin("core.classify",x) :: private int
}
function private uint classify(uint x) {
    __builtin("core.classify",x) :: private uint
}
function private bool classify(bool x) {
    __builtin("core.classify",x) :: private bool
}

function private bool operator <= (private uint x,private uint y) {
    __builtin("core.le",x,y) :: private bool
}

struct partition_result {
    private uint[[1]] ls; // <= pivot
    private uint[[1]] rs; // > pivot
}

// append an element to the end of an array. everything is pass-by-value
private uint[[1]] snoc (private uint[[1]] xs, private uint x) {
    return cat (xs, {x});
}

//@ template <type T>
//@ leakage function bool lcomparison (private T[[1]] xs,private T x)
//@ {
//@     forall uint i ; (0 <= i && i < size(xs)) ==> public(xs[i] <= x)
//@ }

//@ template <type T>
//@ leakage function bool lcomparisons (private T[[1]] xs)
//@ {
//@     forall uint i,uint j ; (0 <= i && i < size(xs) && 0 <= j && j < size(xs)) ==> public(xs[i] <= xs[j])
//@ }

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

//@ leakage lemma lcomparisons_subset <domain D,type T> (D T[[1]] xs,D T[[1]] ys)
//@ requires multiset(ys) <= multiset(xs);
//@ requires lcomparisons(xs);
//@ ensures lcomparisons(ys);

//@ leakage lemma lcomparison_subset <domain D,type T> (D T[[1]] xs,D T[[1]] ys, D T[[1]] z)
//@ requires multiset(ys) <= multiset(xs);
//@ requires z in xs;
//@ requires lcomparisons(xs);
//@ ensures lcomparison(ys,z);

//@ lemma ArrayHead <domain D,type T> (D T[[1]] xs)
//@ requires size(xs) > 1;
//@ ensures xs == cat({xs[0]},xs[1:]);

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

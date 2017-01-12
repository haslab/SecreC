//#OPTIONS_SECREC --implicitcoercions=defaultsc --backtrack=tryb --matching=gorderedm --promote=nop --ignorespecdomains --verify=bothv --entrypoints="leaky_sort" --nodafnymodules

module qsort;

import axioms;

//* Domain declarations

kind privatek;
domain private privatek;

//* Annotations

//@ template <nonpublic kind K,domain D : K,type T>
//@ leakage function bool lcomparison (D T[[1]] xs,D T x)
//@ context<>
//@ noinline;
//@ {
//@     forall uint i ; (0 <= i && i < size(xs)) ==> public(xs[i] <= x)
//@ }

//@ template <nonpublic kind K,domain D : K,type T>
//@ leakage function bool lcomparisons (D T[[1]] xs)
//@ context<>
//@ noinline;
//@ {
//@     forall uint i,uint j ; (0 <= i && i < size(xs) && 0 <= j && j < size(xs)) ==> public(xs[i] <= xs[j])
//@ }

//@ leakage lemma lcomparisons_subset <nonpublic kind K,domain D : K,type T> (D T[[1]] xs,D T[[1]] ys)
//@ requires multiset(ys) <= multiset(xs);
//@ requires lcomparisons(xs);
//@ ensures lcomparisons(ys);
 
//@ leakage lemma lcomparison_subset <nonpublic kind K,domain D : K,type T> (D T[[1]] xs,D T[[1]] ys, D T z)
//@ requires multiset(ys) <= multiset(xs);
//@ requires in(z,xs);
//@ requires lcomparisons(xs);
//@ ensures lcomparison(ys,z);

//* Code

struct partition_result {
    private uint[[1]] ls; // <= pivot
    private uint[[1]] rs; // > pivot
}

// partition a list by
// the intermediate comparisons cannot be computed from the public values. they leak the "shape" of the input.
partition_result partition (private uint[[1]] xs, private uint p)
//@ leakage requires lcomparison(xs,p);
//@ ensures multiset(xs) === union(multiset(\result.ls),multiset(\result.rs));
//@ ensures size(xs) === size(\result.ls) + size(\result.rs);
{
    private uint[[1]] ls, rs;
    for (uint i = 0; i < size (xs); i=i+1)
    //@ invariant 0 <= i && i <= size(xs);
    //@ invariant multiset(xs[:i]) === union(multiset(ls),multiset(rs));
    //@ invariant size(xs[:i]) === size(ls) + size(rs);
    {
        //@ assert i < size(xs);
        //@ MultisetSliceOne(xs,i);
        private uint y = xs[i];
        if (declassify (y <= p)) {
            ls = snoc(ls,y);
            //@ MultisetSnoc(ls);
        }
        else {
            rs = snoc (rs, y);
            //@ MultisetSnoc(rs);
        }
    }
    //@ MultisetSlice(xs);

    partition_result result;
    result.ls = ls;
    result.rs = rs;
    return result;
}

private uint[[1]] leaky_sort (private uint[[1]] xs)
//@ decreases size(xs);
//@ leakage requires lcomparisons(xs);
//@ ensures multiset(xs) === multiset(\result);
{
    if (size(xs) <= 1) return xs;

    //@ ConsDef(xs);

    private uint pivot = xs[0];
    //@ leakage lcomparison_subset(xs,xs[1:],pivot);
    partition_result r = partition (xs[1:], pivot);
    //@ leakage lcomparisons_subset(xs,r.ls);
    private uint[[1]] ls = leaky_sort (r.ls);
    //@ leakage lcomparisons_subset(xs,r.rs);
    private uint[[1]] rs = leaky_sort (r.rs);
    return cat (snoc (ls, pivot), rs);
}

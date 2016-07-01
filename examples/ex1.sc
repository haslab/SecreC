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

partition_result leaky_sort (private uint[[1]] xs)

//@ leakage requires lcomparisons(xs);
{
    partition_result result;
    //@ leakage assume lcomparisons(result.ls);
    return result;
}
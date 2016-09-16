
module cut2;

import axioms;

//* Domain declarations

kind privatek;
domain private privatek;

function int declassify(private int x) {
    __builtin("core.declassify",x) :: int
}
function bool declassify(private bool x) {
    __builtin("core.declassify",x) :: bool
}
function private int classify(int x) {
    __builtin("core.classify",x) :: private int
}
function private bool classify(bool x) {
    __builtin("core.classify",x) :: private bool
}

//* Code

private int[[1]] cut (private int[[1]] aS, private bool [[1]] mS)
//@ requires size(aS) == size(mS);
//@ leakage requires public(mS);
//@ ensures multiset(\result) <= multiset(aS);
{   
    uint i, j;
    private int[[1]] x (size(mS));

    while (i < size(mS))
    //@ invariant size(x) == size(mS);
    //@ invariant 0 <= j && j <= i && i <= size(aS);
    //@ invariant multiset(x[:j]) <= multiset(aS[:i]);
    {
        if (declassify(mS[i])) { x[j] = aS[i]; j = j + 1; }
        i = i + 1;
    }
    return x[:j];
}
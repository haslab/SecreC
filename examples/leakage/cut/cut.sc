
module cut;

import axioms;

//* Domain declarations

kind privatek;
domain private privatek;

//* Code

private int[[1]] cut (private int[[1]] aS, private bool [[1]] mS)
//@ requires size(aS) == size(mS);
//@ leakage requires public(mS);
//@ ensures multiset(\result) <= multiset(aS);
{   
    uint i;
    private int[[1]] x;

    while (i < size(mS))
    //@ invariant 0 <= i && i <= size(aS);
    //@ invariant multiset(x) <= multiset(aS[:i]);
    {
        if (declassify(mS[i])) { x = cat(x,{aS[i]}); }
        i = i + 1;
    }
    return x;
}
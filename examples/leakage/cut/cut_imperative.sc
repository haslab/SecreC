//#OPTIONS_SECREC --implicitcoercions=defaultsc --backtrack=tryb --matching=gorderedm --promote=nop --ignorespecdomains --verify=bothv --nodafnymodules

module cut_imperative;

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
    uint i, j;
    private int[[1]] x (size(mS));

    while (i < size(mS))
    //@ invariant size(x) == size(mS);
    //@ invariant 0 <= j && j <= i && i <= size(aS);
    //@ invariant multiset(x[:j]) <= multiset(aS[:i]);
    {
        if (declassify(mS[i])) {
            x[j] = aS[i];
            //@ MultisetSliceOne(x,j);
            j = j + 1;
        }
        //@ MultisetSliceOne(aS,i);
        i = i + 1;
    }
    //@ MultisetSlice(aS);
    return x[:j];
}
//#OPTIONS_SECREC --implicitcoercions=defaultsc --backtrack=tryb --matching=gorderedm --promote=nop --ignorespecdomains --verify=bothv

module cut_shuffle;

import axioms;

kind privatek;
domain private privatek;

struct pair {
    private int[[1]] left;
    private bool[[1]] right;
}

pair shuffle_pair (private int[[1]] x,private bool[[1]] y)
//@ requires size(x) == size(y);
//@ free ensures multiset(x) == multiset(\result.left);
//@ free ensures multiset(y) == multiset(\result.right);
//@ free leakage ensures public(multiset(x)) ==> public(\result.left);
//@ free leakage ensures public(multiset(y)) ==> public(\result.right);
{
    havoc pair ret;
    return ret;
}

private int[[1]] cut (private int[[1]] a, private bool [[1]] m)
//@ requires size(a) == size(m);
//@ leakage requires public(multiset(m));
//@ ensures multiset(\result) <= multiset(a);
{
    pair amS = shuffle_pair (a,m);
    private int[[1]] aS = amS.left;
    private bool[[1]] mS = amS.right;
    //@ MultisetSize(aS);
    //@ MultisetSize(mS);
    
    uint i = 0;
    private int[[1]] x;

    while (i < size(mS))
    //@ invariant 0 <= i && i <= size(aS);
    //@ invariant multiset(x) <= multiset(aS[:i]);
    {
        if (declassify(mS[i])) { x = cat(x,{aS[i]}); }
        //@ MultisetSliceOne(aS,i);
        i = i + 1;
    }
    //@ MultisetSlice(aS);
    return x;
}
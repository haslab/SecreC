
module ex;

kind privatek;
domain private privatek;

struct pair {
    private int[[1]] left;
    private bool[[1]] right;
}

bool declassify(private bool b) {

    return __builtin("core.declassify",b);
}

//@ axiom <domain D,type T> (D T[[1]] xs)
//@ ensures size(xs) == size(multiset(xs));


//@ axiom <domain D,type T> (D T[[1]] xs, uint i)
//@ requires 0 <= i && i < size(xs);
//@ ensures multiset(xs[:i+1]) == multiset(xs[:i]) + multiset{xs[i]};

pair shuffle_pair (private int[[1]] x,private bool[[1]] y)
//@ requires size(x) == size(y);
//@ free ensures multiset(x) == multiset(\result.left);
//@ free ensures multiset(y) == multiset(\result.right);
//@ free leakage ensures public(multiset(x)) ==> public(\result.left);
//@ free leakage ensures public(multiset(y)) ==> public(\result.right);
{
    //stub;
    pair pS;
    return pS;
}

private int[[1]] cut (private int[[1]] a, private bool [[1]] m)
//@ requires size(a) == size(m);
//@ leakage requires public(multiset(m));
//@ ensures multiset(\result) <= multiset(a);
{
    pair amS = shuffle_pair (a,m);
    private int[[1]] aS = amS.left;
    private bool[[1]] mS = amS.right;
    
    uint i = 0;
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
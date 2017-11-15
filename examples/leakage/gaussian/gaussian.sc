//#OPTIONS_SECREC --implicitcoercions=defaultsc --backtrack=tryb --matching=gorderedm --promote=nop --verify=funcv --entrypoints="_gaussianElimination" --nodafnymodules

module gaussian;

import axioms;
//* Domain declarations

kind privatek;
domain private privatek;

struct result {
    private float64[[2]] vec; 
    public uint[[1]] perm;
}

template<type T>
function private T choose(private bool comp,private T new,private T old)
{
    old - (float64) comp * old + (float64) comp * new
}

uint maxFirstLocAbs(private float64[[1]] vec)
//@ requires size(vec) > 0;
//@ ensures 0 <= \result && \result < size(vec);
{
    private float64 best = vec[0];
    private uint idx = classify(0);

    for (uint i = 1; i < size(vec); i=i+1)
    //@ invariant 0 <= i && i <= size(vec);
    //@ invariant 0 <= idx && idx < size(vec);
    {
        private bool comp = abs(vec[i]) > abs(best);
        best = choose(comp, vec[i], best);
        private uint secret = classify(i);
        idx = idx - (uint) comp * idx + (uint) comp * secret;
    }
    return declassify(idx);
}

//@ function bool IsPermUpTo (uint[[1]] perm, uint n)
//@ context<>
//@ noinline;
//@ {
//@    (forall uint i ; (0 <= i && i < size(perm)) ==> 0 <= perm[i] && perm[i] < n)
//@ }

//@ function bool Distinct (uint[[1]] perm)
//@ context<>
//@ noinline;
//@ {
//@   (forall uint i,uint j; (i < size(perm)) && (j < size(perm)) && (i != j) ==> perm[i] != perm[j])
//@ }

//@ function bool IsPerm (uint[[1]] perm)
//@ context<>
//@ inline;
//@ {
//@    IsPermUpTo(perm,size(perm)) && Distinct(perm)
//@ }

result _gaussianElimination(private float64[[2]] a, private float64[[1]] b)
//@ requires size(b) > 0;
//@ requires shape(a)[0] === shape(a)[1];
//@ requires size(b) === shape(a)[0];
//@ ensures IsPerm(\result.perm); 
//@ ensures size(\result.perm) === size(b);
{
    uint n = shape(a)[0];
    public result res;
    public uint[[1]] perm (n);
    for (uint i = 0; i < n; i=i+1)
    //@ invariant 0 <= i && i <= n;
    //@ invariant size(perm) === n;
    //@ invariant forall uint j; j < i ==> perm[j] === j;
    //@ invariant IsPerm(perm[:i]);
    {
        perm[i] = i;
    }
 
    // Main loop over the columns to be reduced
    for (uint i = 0; i < n - 1; i=i+1)
    //@ invariant 0 <= i && i < n;
    //@ invariant shape(a)[0] === n;
    //@ invariant size(perm) === n;
    //@ invariant size(b) === n;
    //@ invariant multiset(perm) === old(multiset(perm));
    //@ invariant IsPerm(perm);
    {
        uint icol = i;
        // Search for a pivot element
        uint irow = maxFirstLocAbs(a[i:, i]) + i;
        //@ assert irow >= i;
        //@ assert irow < n;
        
        // Interchange rows
        if (irow != icol)
        {
            public uint permi = perm[i];
            perm[i] = perm[irow];
            perm[irow] = permi;
            
            private float64[[1]] tmpVec = a[irow, :];
            a[irow, :] = a[i, :];
            a[i, :] = tmpVec;
            
            private float64 tmp = b[irow];
            b[irow] = b[icol];
            b[icol] = tmp;
        }
        
        // Divide the pivot row by the pivot element, located at (irow, icol).
        private float64 pivinv = a[icol, icol];
        private float64 one = classify(1);
        pivinv = inv(pivinv);
        a[icol, icol] = one;
        for (uint j = 0; j < n; j=j+1)
        //@ invariant 0 <= j && j <= n;
        {
            a[icol,j] *= pivinv;
        }
        b[icol] *= pivinv;
 
        // Reduce the rows below the pivot row
        for (uint ll = icol + 1; ll < n; ll=ll+1)
        //@ invariant shape(a)[0] === n;    
        //@ invariant shape(a)[1] === n;
        //@ invariant size(b) === n;
        //@ invariant 0 <= ll && ll <= n;
        {
            private float64 dum = a[ll, icol];
            a[ll, icol] = classify(0);
            
            private float64[[1]] sub(n);
            for (uint j = 0; j < n; j=j+1)
            //@ invariant size(sub) === n;
            //@ invariant shape(a)[0] === n;
            //@ invariant shape(a)[1] === n;
            //@ invariant 0 <= j && j <= n;
            {
                sub[j] = a[icol, j] * dum;
            }
            sub[icol] = classify(0);
            
            for (uint j = 0; j < n; j=j+1)
            //@ invariant size(sub) === n;
            //@ invariant shape(a)[0] === n;
            //@ invariant shape(a)[1] === n;
            //@ invariant 0 <= j && j <= n;
            {
                a[ll,j] -= sub[j];
            }
            
            b[ll] -= b[icol] * dum;
        }
    }
 
    // Backsubstitution
    private float64 zero = classify(0);
    uint n1 = n - 1;
    private bool c = b[n1] != zero;
    b[n1] = choose(c,a[n1, n1],b[n1]);
    for (uint i = n; i > 0; i=i-1)
    //@ invariant shape(a)[0] === n;
    //@ invariant shape(a)[1] === n;
    //@ invariant size(b) === n;
    //@ invariant 0 <= i && i <= n;
    {
        uint i1 = i-1;
        private float64[[1]] tmpa = a[i1, i:];
        private float64[[1]] tmpb = b[i:];
        private float64[[1]] tmp = tmpa * tmpb;
        private float64 sumt = sum(tmp);
        b[i1] -= sumt;
    }
 
    res.vec = a;
    res.perm = perm;
    return res;
}
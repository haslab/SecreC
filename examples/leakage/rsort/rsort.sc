//#OPTIONS_SECREC --implicitcoercions=defaultsc --backtrack=tryb --matching=gorderedm --promote=nop --verify=funcv --entrypoints="bitwise_rsort" --nodafnymodules

module rsort;

import axioms;
//* Domain declarations

kind privatek;
domain private privatek;

//* Annotations

//@ function bool IsPermUpTo (uint[[1]] perm, uint n)
//@ context<>
//@ noinline;
//@ {
//@    (forall uint i ; (0 <= i && i < size(perm)) ==> 0 <= perm[i] && perm[i] < n)
//@ }

//@ function bool DistinctUpTo (uint[[1]] perm, uint n)
//@ context<>
//@ noinline;
//@ requires n <= size(perm);
//@ {
//@   (forall uint i,uint j; (0 <= i && i < n) && (0 <= j && j < n) && (i != j) ==> perm[i] != perm[j])
//@ }

//@ function bool IsPerm (uint[[1]] perm)
//@ context<>
//@ inline;
//@ {
//@    IsPermUpTo(perm,size(perm)) && DistinctUpTo(perm,size(perm))
//@ }

//* Code

// applies a permutation to an array
private bool[[2]] permute (private bool[[2]] xs, uint[[1]] perm)
//@ requires IsPerm(perm);
//@ requires shape(xs)[0] === size(perm);
//@ ensures shape(xs) === shape(\result);
{
    uint n1 = shape(xs)[0];
    uint n2 = shape(xs)[1];
    
    havoc private bool[[2]] ys (n1,n2);
    for (uint i = 0; i < n1; i=i+1)
    //@ invariant 0 <= i && i <= n1;
    //@ invariant shape(ys) === shape(xs);
    {
        for (uint j = 0; j < n2; j=j+1)
        //@ invariant 0 <= j && j <= n2;
        //@ invariant shape(ys) === shape(xs);
        {
            ys[perm[i],j] = xs[i,j];
        }
    }
    return ys;
}

struct pair {
    private bool[[2]] bits; 
    private uint[[1]] ord; 
}

pair shuffle_pair (private bool [[2]] xs, private uint [[1]] ys)
//@ requires shape(xs)[0] === size(ys);
//@ requires IsPerm(ys);
//@ free ensures shape(\result.bits) === shape(xs);
//@ free ensures size(\result.ord) === size(ys);
//@ free ensures IsPerm(\result.ord);
//@ free leakage ensures public(\result.ord);
{
    havoc pair ret;
//    private uint8[[1]] key (32) = randomize(key);
//    pair ret;
//    ret.bits = shuffleRows(bits,key);
//    ret.ord = shuffle(ord,key);
    return ret;
}

private bool[[2]] apply_perm (private bool[[2]] bits, private uint[[1]] ord)
//@ requires IsPerm(ord);
//@ requires shape(bits)[0] === size(ord);
//@ ensures shape(bits) === shape(\result);
{
    pair p = shuffle_pair(bits,ord);
    bits = p.bits;
    public uint[[1]] pord = declassify(p.ord);
    bits = permute(bits,pord);
    return bits;
}


private bool[[2]] bitwise_rsort (private bool[[2]] bits)
{
    uint n = shape(bits)[0];
    uint k = shape(bits)[1];
    for (uint m = k; m > 0; m=m-1)
    //@ invariant shape(bits) === {n,k};
    //@ invariant 0 <= m && m <= k;
    {
        // extract an array of only the k-th bits
        private bool[[1]] bitCol = bits[:,m-1];
        // convert to numericals and count the number of 0s
        private uint[[1]] bitColMod2n (n);
        private uint n1;
        for (uint i = 0; i < n; i=i+1)
        //@ invariant shape(bits) === {n,k};
        //@ invariant n == size(bitCol);
        //@ invariant n == size(bitColMod2n);
        //@ invariant 0 <= i && i <= n;
        //@ invariant n1 <= i;
        //@ invariant forall uint j; 0 <= j && j < i ==> bitColMod2n[j] <= 1;
        //@ invariant sum(bitColMod2n[:i]) === n1;
        {
            bitColMod2n[i] = (uint) bitCol[i];
            private uint ubit = bitColMod2n[i];
            //@ assert ubit <= 1;
            //@ assert sum(bitColMod2n[:i]) === n1;
            //@ SumSliceEnd(bitColMod2n,i);
            n1 = ubit + n1;
            //@ assert sum(bitColMod2n[:i+1]) === n1;
        }
        private uint n0 = classify(n) - n1;
        //@ SliceEndEqual(bitColMod2n);
        //@ SliceBeginEqual(bitColMod2n);
        //@ assert sum(bitColMod2n) === n1;
        //@ assert n1 <= n;
        //@ assert n0 === n - sum(bitColMod2n);
        // counter for number of 0s
        private uint c0;
        // counter for number of 1s
        private uint c1;
        // permutation on input
        private uint[[1]] ord (n);
        // compute a permutation that sorts according to the k-th bit
        for (uint i = 0; i < n; i=i+1)
        //@ invariant shape(bits) === {n,k};
        //@ invariant n0 <= n;
        //@ invariant forall uint j; 0 <= j && j < n ==> bitColMod2n[j] <= 1;
        //@ invariant n === size(bitColMod2n);
        //@ invariant n === size(ord);
        //@ invariant 0 <= i && i <= n;
        //@ invariant c0 + c1 == i;
        //@ free invariant forall uint i ; 0 <= i && i < n ==> sum(bitColMod2n[:i]) <= size(bitColMod2n[:i]);
        //@ free invariant forall uint i ; 0 <= i && i < n ==> sum(bitColMod2n[i:]) <= size(bitColMod2n[i:]);
        //@ invariant c0 === i - sum(bitColMod2n[:i]);
        //@ invariant c1 === sum(bitColMod2n[:i]);
        //@ invariant n0 === c0 + n - i - sum(bitColMod2n[i:]);
        //@ invariant forall uint j ; (0 <= j && j < i) ==> ord[j] < n;
        //@ invariant forall uint j ; (0 <= j && j < i) ==> ((0 <= ord[j] && ord[j] < c0) || (n0 <= ord[j] && ord[j] < n0 + c1));
        //@ invariant DistinctUpTo(ord,i);
        {
            //@ SumSliceBegin(bitColMod2n,i);
            private uint ubit = bitColMod2n[i];
            //@ assert ubit <= 1;
            private uint nubit = classify(1)-ubit;
            //@ assert nubit <= 1;
            //@ assert 0 <= c0 && c0 < n;
            //@ assert bitColMod2n[i] === 1 ==> (0 <= n0 + c1 && n0 + c1 < n);
            ord[i] = nubit * c0 + ubit * (n0 + c1);
            c0 = c0 + nubit;
            c1 = c1 + ubit;
            //@ SumSliceEnd(bitColMod2n,i);
            //@ assert forall uint j ; (0 <= j && j < i) ==> ord[i] != ord[j];
        }
        bits = apply_perm(bits,ord);
    }
    return bits;
}



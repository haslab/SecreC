#OPTIONS_SECREC --implicitcoercions=onc --backtrack=tryb --matching=gorderedm --promote=nop

module apriori_spec;

import shared3p;

//kind shared3p;
domain pd_shared3p shared3p;

//* Utility functions

template<domain D>
D uint[[1]] snoc (D uint[[1]] xs, D uint x)
//@ inline;
//@ free ensures size(\result) == size(xs) + 1;
//@ free ensures forall uint i; i < size(xs) ==> assertion<D>(\result[i] == xs[i] :: D uint);
//@ free ensures assertion(\result[size(xs)] == x);
{
    return cat(xs,{x});
}

template<domain D>
D uint[[2]] snoc (D uint[[2]] xs, D uint[[1]] x)
//@ inline;
//@ requires shape(xs)[1] == size(x);
//@ free ensures shape(\result)[0] == shape(xs)[0] + 1;
//@ free ensures shape(\result)[1] == shape(xs)[1];
//@ free ensures forall uint i; i < shape(xs)[0] ==> assertion<D>(\result[i,:] == xs[i,:] :: D uint[[1]]);
//@ free ensures assertion<D>(\result[shape(xs)[0],:] == x);
{
    return cat(xs,reshape(x,1,size(x)));
}

//* Structures

struct frequent {
    uint [[2]] items;
    pd_shared3p uint [[2]] cache;
}

frequent newfrequent(uint F_size, pd_shared3p uint[[2]] db)
//@ inline;
{
   frequent f;
   uint[[2]] F (0,F_size);
   //pd_shared3p uint[[2]] F_cache (0,shape(db)[0]);
   pd_shared3p uint[[2]] F_cache = reshape(classify({} :: pd_shared3p uint[[1]]),0,shape(db)[0]);
   f.items = F;
   f.cache = F_cache;
   return f;
}

//* Correctness functions

//@ function bool IsDB (pd_shared3p uint[[2]] db)
//@ noinline;
//@ {
//@     forall pd_shared3p uint x; assertion<pd_shared3p>(in(x,db) ==> x <= classify(1))
//@ }

//@ function bool IsItemSet (uint[[1]] is, uint sz)
//@ noinline;
//@ {
//@    size(is) > 0
//@    && (forall uint k; k < size(is) ==> is[k] < sz)
//@    && (forall uint i, uint j; i < j && j < size(is) ==> is[i] < is[j])
//@ }

//@ function bool IsItemSetOf (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ { IsItemSet(is,shape(db)[1]) }

//@ function pd_shared3p uint[[1]] transactions (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ noinline;
//@ requires IsDB(db);
//@ requires IsItemSetOf(is,db);
//@ ensures size(\result) == shape(db)[0];
//@ { (size(is) == 1) ? db[:,is[0]] : db[:,is[0]] * transactions(is[1:],db) }

//@ function pd_shared3p uint frequency (uint[[1]] is, pd_shared3p uint[[2]] db)
//x //@ noinline;
//x //@ requires IsDB(db);
//x //@ requires IsItemSetOf(is,db);
//@ { sum(transactions(is,db)) }

//@ function bool Candidate(uint[[1]] fitems, pd_shared3p uint[[2]] db, uint k)
//@ {
//@     size(fitems) == k
//@     &&
//@     IsItemSetOf(fitems,db)
//@ }

//@ function bool CandidateCache(uint[[1]] fitems, pd_shared3p uint[[1]] fcache, pd_shared3p uint[[2]] db, uint k)
//@ {
//@     Candidate(fitems,db,k)
//@     &&
//@     size(fcache) == shape(db)[0]
//@     &&
//@     declassify(fcache == transactions(fitems,db))
//@ }

//@ function bool FrequentCache(uint[[1]] fitems, pd_shared3p uint[[1]] fcache, pd_shared3p uint[[2]] db, uint threshold, uint k)
//@ noinline;
//@ requires IsDB(db);
//@ {
//@     CandidateCache(fitems,fcache,db,k)
//@     &&
//@     declassify(frequency(fitems,db)::pd_shared3p uint) >= threshold
//@ }

//@ function bool FrequentsCache(frequent f, pd_shared3p uint[[2]] db, uint threshold, uint k)
//@ noinline;
//@ requires IsDB(db);
//@ {
//@     shape(f.items)[0] == shape(f.cache)[0]
//@     &&
//@     shape(f.items)[1] == k
//@     &&
//@     shape(f.cache)[1] == shape(db)[0]
//@     &&
//@     forall uint i; i < shape(f.items)[0] ==> FrequentCache(f.items[i,:],f.cache[i,:],db,threshold,k)
//@ }

//* Correctness proofs

//@ template<domain D>
//@ void SnocRange (D uint[[2]] xs, uint i, uint n)
//@ inline;
//@ {
//@     assert assertion<D>(xs[i,:n+1] == snoc(xs[i,:n],xs[i,n]));
//@ }

//@ lemma JoinCaches(uint[[1]] C, pd_shared3p uint[[1]] C_dot, uint[[1]] xs, uint[[1]] ys, pd_shared3p uint[[2]] db, uint k)
//@ requires k > 1;
//@ requires IsDB(db);
//@ requires IsItemSetOf(xs,db);
//@ requires IsItemSetOf(ys,db);
//@ requires size(xs) == k-1;
//@ requires size(xs) == size(ys);
//@ requires Candidate(C,db,k);
//@ requires size(C_dot) == shape(db)[0];
//@ requires (C == snoc(xs,last(ys)) :: bool);
//@ requires assertion(C_dot == transactions(xs,db) * transactions(ys,db) :: pd_shared3p bool);
//@ requires init(xs) == init(ys);
//@ ensures CandidateCache(C,C_dot,db,k);
//x //@ ensures assertion(C_dot == transactions(C,db) :: pd_shared3p bool);

//* Leakage functions

//@ leakage function bool LeakFrequents (pd_shared3p uint[[2]] db, uint threshold)
//@ noinline;
//@ requires IsDB(db);
//@ { forall uint[[1]] is; IsItemSetOf(is,db) ==> public (frequency(is,db) >= classify(threshold)) }

          
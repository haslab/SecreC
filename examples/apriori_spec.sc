#OPTIONS_SECREC --implicitcoercions=extendedc --backtrack=fullb --matching=unorderedm --promote=localp

module apriori_spec;

import shared3p;

//kind shared3p;
domain pd_shared3p shared3p;

//* Utility functions

template<domain D>
D uint[[1]] snoc (D uint[[1]] xs, D uint x)
context<>
//@ inline;
//@ free ensures size(\result) == size(xs) + 1;
//@ free ensures forall uint i; i < size(xs) ==> assertion(\result[i] == xs[i]);
//@ free ensures assertion(\result[size(xs)] == x);
{
    return cat(xs,{x});
}

template<domain D>
D uint[[2]] snoc (D uint[[2]] xs, D uint[[1]] x)
context<>
//@ inline;
//@ requires shape(xs)[1] == size(x);
//@ free ensures shape(\result)[0] == shape(xs)[0] + 1;
//@ free ensures shape(\result)[1] == shape(xs)[1];
//@ free ensures forall uint i; i < shape(xs)[0] ==> assertion(\result[i,:] == xs[i,:]);
//@ free ensures assertion(\result[shape(xs)[0],:] == x);
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
   pd_shared3p uint[[2]] F_cache (0,shape(db)[0]);
   f.items = F;
   f.cache = F_cache;
   return f;
}

//* Correctness functions

//@ function bool IsDB (pd_shared3p uint[[2]] db)
//@ noinline;
//@ {
//@     forall pd_shared3p uint x; assertion(in(x,db) ==> x <= 1)
//@ }

//x //@ function bool IsItemSet (uint[[1]] is, uint sz)
//x //@ noinline;
//x //@ {
//x //@    size(is) > 0
//x //@    && (forall uint k; k < size(is) ==> is[k] < sz)
//x //@    && (forall uint i, uint j; i < j && j < size(is) ==> is[i] < is[j])
//x //@ }
//x 
//x //@ function bool IsItemSetOf (uint[[1]] is, pd_shared3p uint[[2]] db)
//x //@ requires IsDB(db);
//x //@ { IsItemSet(is,shape(db)[1]) }
//x 
//x //@ function pd_shared3p uint[[1]] transactions (uint[[1]] is, pd_shared3p uint[[2]] db)
//x //@ noinline;
//x //@ requires IsDB(db);
//x //@ requires IsItemSetOf(is,db);
//x //@ ensures size(\result) == shape(db)[0];
//x //@ { (size(is) == 1) ? db[:,is[0]] : db[:,is[0]] * transactions(is[1:],db) }
//x 
//x //@ function pd_shared3p uint frequency (uint[[1]] is, pd_shared3p uint[[2]] db)
//x //x //@ noinline;
//x //x //@ requires IsDB(db);
//x //x //@ requires IsItemSetOf(is,db);
//x //@ { sum(transactions(is,db)) }
//x 
//x //@ function bool Candidate(uint[[1]] fitems, pd_shared3p uint[[2]] db, uint k)
//x //@ {
//x //@     size(fitems) == k
//x //@     &&
//x //@     IsItemSetOf(fitems,db)
//x //@ }
//x 
//x //@ function bool CandidateCache(uint[[1]] fitems, pd_shared3p uint[[1]] fcache, pd_shared3p uint[[2]] db, uint k)
//x //@ {
//x //@     Candidate(fitems,db,k)
//x //@     &&
//x //@     size(fcache) == shape(db)[0]
//x //@     &&
//x //@     declassify(fcache == transactions(fitems,db))
//x //@ }
//x 
//x //@ function bool FrequentCache(uint[[1]] fitems, pd_shared3p uint[[1]] fcache, pd_shared3p uint[[2]] db, uint threshold, uint k)
//x //@ noinline;
//x //@ requires IsDB(db);
//x //@ {
//x //@     CandidateCache(fitems,fcache,db,k)
//x //@     &&
//x //@     declassify(frequency(fitems,db)::pd_shared3p uint) >= threshold
//x //@ }
//x 
//x //@ function bool FrequentsCache(frequent f, pd_shared3p uint[[2]] db, uint threshold, uint k)
//x //@ noinline;
//x //@ requires IsDB(db);
//x //@ {
//x //@     shape(f.items)[0] == shape(f.cache)[0]
//x //@     &&
//x //@     shape(f.items)[1] == k
//x //@     &&
//x //@     shape(f.cache)[1] == shape(db)[0]
//x //@     &&
//x //@     forall uint i; i < shape(f.items)[0] ==> FrequentCache(f.items[i,:],f.cache[i,:],db,threshold,k)
//x //@ }
//x 
//x //* Correctness proofs
//x 
//x //@ template<domain D>
//x //@ void SnocRange (D uint[[2]] xs, uint i, uint n)
//x //@ inline;
//x //@ {
//x //@     assert assertion<D>(xs[i,:n+1] == snoc(xs[i,:n],xs[i,n]));
//x //@ }
//x 
//x //@ lemma JoinCaches(uint[[1]] C, pd_shared3p uint[[1]] C_dot, uint[[1]] xs, uint[[1]] ys, pd_shared3p uint[[2]] db, uint k)
//x //@ requires k > 1;
//x //@ requires IsDB(db);
//x //@ requires IsItemSetOf(xs,db);
//x //@ requires IsItemSetOf(ys,db);
//x //@ requires size(xs) == k-1;
//x //@ requires size(xs) == size(ys);
//x //@ requires Candidate(C,db,k);
//x //@ requires size(C_dot) == shape(db)[0];
//x //@ requires (C == snoc(xs,last(ys)) :: bool);
//x //@ requires assertion(C_dot == transactions(xs,db) * transactions(ys,db) :: pd_shared3p bool);
//x //@ requires init(xs) == init(ys);
//x //@ ensures CandidateCache(C,C_dot,db,k);
//x //x //@ ensures assertion(C_dot == transactions(C,db) :: pd_shared3p bool);
//x 
//x //* Leakage functions
//x 
//x //@ leakage function bool LeakFrequents (pd_shared3p uint[[2]] db, uint threshold)
//x //@ noinline;
//x //@ requires IsDB(db);
//x //@ { forall uint[[1]] is; IsItemSetOf(is,db) ==> public (frequency(is,db) >= classify(threshold)) }

          
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
//@     assertion(fcache == transactions(fitems,db))
//@ }

//@ function bool FrequentCache(uint[[1]] fitems, pd_shared3p uint[[1]] fcache, pd_shared3p uint[[2]] db, uint threshold, uint k)
//@ noinline;
//@ requires IsDB(db);
//@ {
//@     CandidateCache(fitems,fcache,db,k)
//@     &&
//@     assertion(frequency(fitems,db) >= threshold)
//@ }

//* Correctness proofs

//@ template<domain D>
//@ void SnocRange (D uint[[2]] xs, uint i, uint n)
//@ context<>
//@ inline;
//@ {
//@     assert assertion(xs[i,:n+1] == snoc(xs[i,:n],xs[i,n]));
//@ }

          
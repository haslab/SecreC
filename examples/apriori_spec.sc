//#OPTIONS_SECREC --implicitcoercions=onc --backtrack=fullb --matching=unorderedm --promote=localp --ignorespecdomains --implicitcontext=inferctx

module apriori_spec;

//import shared3p;

import axioms;

kind shared3p;
domain pd_shared3p shared3p;

//* Utility functions

template<domain D>
D uint[[1]] snoc (D uint[[1]] xs, D uint x)
//@ inline;
//@ free ensures size(\result) == size(xs) + 1;
//@ free ensures forall uint i; i < size(xs) ==> \result[i] == xs[i];
//@ free ensures \result[size(xs)] == x;
{
    return cat(xs,{x});
}

template<domain D>
D uint[[2]] snoc (D uint[[2]] xs, D uint[[1]] x)
//@ inline;
//@ requires shape(xs)[1] == size(x);
//@ free ensures shape(\result)[0] == shape(xs)[0] + 1;
//@ free ensures shape(\result)[1] == shape(xs)[1];
//@ free ensures forall uint i; i < shape(xs)[0] ==> \result[i,:] == xs[i,:];
//@ free ensures \result[shape(xs)[0],:] == x;
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

//@ function bool IsBool (pd_shared3p uint[[1]] xs)
//@ noinline;
//@ {
//@     forall pd_shared3p uint x; in(x,xs) ==> x <= 1
//@ }

//@ function bool IsDB (pd_shared3p uint[[2]] db)
//@ noinline;
//@ {
//@     forall pd_shared3p uint x; in(x,db) ==> x <= 1
//@ }

//@ function bool IsItemSet (uint[[1]] is, uint sz)
//@ noinline;
//@ { size(is) > 0 && forall uint k; k < size(is) ==> is[k] < sz }

//@ function bool IsItemSetOf (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ { IsItemSet(is,shape(db)[1]) }

//@ function pd_shared3p uint[[1]] transaction (uint i, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires i < shape(db)[1];
//@ ensures size(\result) == shape(db)[0];
//@ { db[:,i] }

//@ function pd_shared3p uint[[1]] transactions (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ noinline;
//@ requires IsDB(db);
//@ requires IsItemSetOf(is,db);
//@ ensures size(\result) == shape(db)[0];
//@ { (size(is) == 1) ? transaction(is[0],db) : transaction(is[0],db) * transactions(is[1:],db) }

//@ function pd_shared3p uint frequency (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemSetOf(is,db);
//@ { sum(transactions(is,db)) }
 
//@ function bool Candidate(uint[[1]] fitems, pd_shared3p uint[[2]] db, uint k)
//@ requires IsDB(db);
//@ {
//@     size(fitems) == k
//@     &&
//@     IsItemSetOf(fitems,db)
//@ }

//@ function bool CandidateCache(uint[[1]] fitems, pd_shared3p uint[[1]] fcache, pd_shared3p uint[[2]] db, uint k)
//@ requires IsDB(db);
//@ {
//@     Candidate(fitems,db,k)
//@     &&
//@     size(fcache) == shape(db)[0]
//@     &&
//@     fcache == transactions(fitems,db)
//@ }

//@ function bool FrequentCache(uint[[1]] fitems, pd_shared3p uint[[1]] fcache, pd_shared3p uint[[2]] db, uint threshold, uint k)
//@ noinline;
//@ requires IsDB(db);
//@ {
//@     CandidateCache(fitems,fcache,db,k)
//@     &&
//@     frequency(fitems,db) >= threshold
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
//@     forall uint i; i < shape(f.items)[0] ==> IsItemSetOf(f.items[i,:],db) && FrequentCache(f.items[i,:],f.cache[i,:],db,threshold,k)
//@ }

//* Correctness proofs

//@ lemma MulCommu <domain D> (D uint[[1]] xs, D uint[[1]] ys)
//@ requires size(xs) == size(ys);
//@ ensures xs * ys == ys * xs;
//@ {}

//@ lemma MulAssoc <domain D> (D uint[[1]] xs, D uint[[1]] ys, D uint[[1]] zs)
//@ requires size(xs) == size(ys) && size(ys) == size(zs);
//@ ensures xs * (ys * zs) == (xs * ys) * zs;
//@ {}

//@ lemma MulCommu4 <domain D> (uint[[1]] a, uint[[1]] b, uint[[1]] c, uint[[1]] d)
//@ requires size(a) == size(b) && size(b) == size(c) && size(c) == size(d);
//@ ensures (a * b) * (c * d) == (a * c) * (b * d);
//@ {
//@     MulAssoc(a,b,c * d);
//@     MulCommu(c,d);
//@     MulAssoc(b,d,c);
//@     MulAssoc(a,c,b * d);
//@ }

//@ lemma MulBool <domain D> (D uint[[1]] xs)
//@ requires IsBool(xs);
//@ ensures xs * xs == xs;
//@ {
//@     if (size(xs) == 0) {
//@         assert heax(xs) <= (1 :: uint);
//@     } else {
//@         assert head(xs) <= (1 :: uint);
//@         assert head(xs) * head(xs) == head(xs);
//@         MulBool(tail(xs));
//@     }
//@ }

//@ template<domain D>
//@ void SnocRange (D uint[[2]] xs, uint i, uint n)
//@ context<>
//@ inline;
//@ {
//@     assert xs[i,:n+1] == snoc(xs[i,:n],xs[i,n]);
//@ }

//@ lemma TransactionsDef (uint[[1]] xs, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemSetOf(xs,db);
//@ requires size(xs) > 1;
//@ ensures transactions(xs,db) == transaction(head(xs),db) * transactions(tail(xs),db);
//@ {}

//@ lemma TransactionsIdem (uint[[1]] xs, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemSetOf(xs,db);
//@ ensures transactions(xs,db) * transactions(xs,db) == transactions(xs,db);
//@ {
//@     if (size(xs) == 1) {
//@         MulBool(transaction(head(xs),db));
//@     } else {
//@         TransactionsDef(xs,db);
//@         MulCommu4(transaction(head(xs),db),transactions(tail(xs),db),transaction(head(xs),db),transactions(tail(xs),db));
//@         MulBool(transaction(head(xs),db));
//@         TransactionsIdem(tail(xs),db);
//@     }
//@ }

//@ lemma TransactionsSnoc (uint[[1]] xs, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemSetOf(xs,db);
//@ requires size(xs) > 1;
//@ ensures transactions(xs,db) == transactions(init(xs),db) * transaction (last(xs),db);
//@ {
//@     if (size(xs) == 2) {
//@     } else {
//@         TransactionsDef(xs,db);
//@         TransactionsSnoc(tail(xs),db);
//@         MulAssoc(transaction(head(xs),db),transactions(init(tail(xs)),db),transaction(last(xs),db));
//@         assert head(xs) == head(init(xs));
//@         assert init(tail(xs)) == tail(init(xs));
//@         TransactionsDef(init(xs),db);
//@     }
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
//@ requires C == snoc(xs,last(ys));
//@ requires C_dot == transactions(xs,db) * transactions(ys,db);
//@ requires init(xs) == init(ys);
//@ ensures CandidateCache(C,C_dot,db,k);
//@ {
//@     if (size(xs) == 1)
//@     {
//@     } else {
//@         TransactionsSnoc(xs,db);
//@         TransactionsSnoc(ys,db);
//@         assert IsItemSetOf(init(xs),db);
//@         assert last(xs) < shape(db)[1];
//@         assert IsItemSetOf(init(ys),db);
//@         assert last(ys) < shape(db)[1];
//@         MulCommu4(transactions(init(xs),db),transaction(last(xs),db),transactions(init(ys),db),transaction(last(ys),db));
//@         MulAssoc(transactions(init(xs),db),transaction(last(xs),db),transaction(last(ys),db));
//@         TransactionsIdem(init(xs),db);
//@         TransactionsSnoc(C,db);
//@     }
//@ }
          
//* Leakage functions

//@ leakage function bool LeakFrequents (pd_shared3p uint[[2]] db, uint threshold)
//@ noinline;
//@ requires IsDB(db);
//@ { forall uint[[1]] is; IsItemSetOf(is,db) ==> public (frequency(is,db) >= threshold) }
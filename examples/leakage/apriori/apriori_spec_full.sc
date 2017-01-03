//#OPTIONS_SECREC --implicitcoercions=defaultsc --backtrack=tryb --matching=gorderedm --promote=nop --ignorespecdomains --implicitcontext=inferctx

module apriori_spec;

import axioms;

kind shared3p;
domain pd_shared3p shared3p;

//* Stubs

template <type T>
void printVector (T[[1]] vec) {}

template <type T>
void printMatrix (T[[2]] mat) {}

//* Structures

struct frequent {
    uint [[2]] items;
    pd_shared3p uint [[2]] cache;
}

struct itemset {
    uint[[2]] items;
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

//@ predicate IsBool (pd_shared3p uint[[1]] xs)
//@ noinline;
//@ { forall uint i; i < size(xs) ==> xs[i] <= 1 }

//@ predicate IsDB (pd_shared3p uint[[2]] db)
//@ noinline;
//@ { forall uint i, uint j; i < shape(db)[0] && j < shape(db)[1] ==> db[i,j] <= 1 }

//@ predicate IsItemSet (uint[[1]] is, uint sz)
//@ noinline;
//@ {
//@     size(is) > 0
//@     && (forall uint k; k < size(is) ==> is[k] < sz)                     // within the size
//@     && (forall uint i, uint j; i < j && j < size(is) ==> is[i] < is[j]) // ordered
//@ }

//@ predicate IsItemOf (uint i, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ { i < shape(db)[1] }

//@ predicate IsItemSetOf (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ { IsItemSet(is,shape(db)[1]) }

//@ function pd_shared3p uint[[1]] transactions (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ noinline;
//@ requires IsDB(db);
//@ requires IsItemSetOf(is,db);
//@ ensures size(\result) === shape(db)[0];
//@ { (size(is) === 1) ? db[:,is[0]] : db[:,is[0]] * transactions(is[1:],db) }

//@ function pd_shared3p uint frequency (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemSetOf(is,db);
//@ { sum(transactions(is,db)) }
 
//@ predicate Candidate(uint[[1]] fitems, pd_shared3p uint[[2]] db, uint k)
//@ requires IsDB(db);
//@ { size(fitems) === k && IsItemSetOf(fitems,db) }

//@ predicate CandidateCache(uint[[1]] fitems, pd_shared3p uint[[1]] fcache, pd_shared3p uint[[2]] db, uint k)
//@ requires IsDB(db);
//@ {
//@     Candidate(fitems,db,k)
//@     &&
//@     size(fcache) === shape(db)[0]
//@     &&
//@     fcache === transactions(fitems,db)
//@ }

//@ predicate FrequentCache(uint[[1]] fitems, pd_shared3p uint[[1]] fcache, pd_shared3p uint[[2]] db, uint threshold, uint k)
//@ noinline;
//@ requires IsDB(db);
//@ {
//@     CandidateCache(fitems,fcache,db,k)
//@     &&
//@     frequency(fitems,db) >= threshold
//@ }

//@ predicate FrequentsCache(frequent f, pd_shared3p uint[[2]] db, uint threshold, uint k)
//@ noinline;
//@ requires IsDB(db);
//@ {
//@     shape(f.items)[0] === shape(f.cache)[0]
//@     &&
//@     shape(f.items)[1] === k
//@     &&
//@     shape(f.cache)[1] === shape(db)[0]
//@     &&
//@     forall uint i; i < shape(f.items)[0] ==> IsItemSetOf(f.items[i,:],db) && FrequentCache(f.items[i,:],f.cache[i,:],db,threshold,k)
//@ }

//@ predicate AllFrequents(itemset[[1]] itemsets, pd_shared3p uint[[2]] db, uint threshold, uint k)
//@ requires IsDB(db);
//@ requires size(itemsets) === k;
//@ noinline;
//@ {
//@     forall uint[[1]] js; IsItemSetOf(js,db) && size(js) <= k && frequency(js,db) >= threshold ==> in(js,set(itemsets[size(js)-1]))
//@ }

//* Correctness proofs

//@ lemma MulCommu <domain D> (D uint[[1]] xs, D uint[[1]] ys)
//@ requires size(xs) === size(ys);
//@ ensures xs * ys === ys * xs;
//@ {}

//@ lemma MulAssoc <domain D> (D uint[[1]] xs, D uint[[1]] ys, D uint[[1]] zs)
//@ requires size(xs) === size(ys) && size(ys) === size(zs);
//@ ensures xs * (ys * zs) === (xs * ys) * zs;
//@ {}

//@ lemma MulCommu4 <domain D> (uint[[1]] a, uint[[1]] b, uint[[1]] c, uint[[1]] d)
//@ requires size(a) === size(b) && size(b) === size(c) && size(c) === size(d);
//@ ensures ((a * b) * (c * d)) === ((a * c) * (b * d));
//@ {
//@     MulAssoc(a,b,c * d);
//@     MulCommu(c,d);
//@     MulAssoc(b,d,c);
//@     MulAssoc(a,c,b * d);
//@ }

//@ lemma MulBool (pd_shared3p uint[[1]] xs)
//@ requires IsBool(xs);
//@ ensures xs * xs === xs;
//@ {
//@     if (size(xs) === 0) {
//@         assume xs * xs === xs;
//@     } else {
//@         assert head(xs) <= (1 :: uint);
//@         assert head(xs) * head(xs) === head(xs);
//@         MulBool(tail(xs));
//@     }
//@ }

//@ template<domain D>
//@ void SnocRange (D uint[[2]] xs, uint i, uint n)
//@ context<>
//@ inline;
//@ { assert xs[i,:n+1] === snoc(xs[i,:n],xs[i,n]); }

//@ lemma TransactionsDef (uint[[1]] xs, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemSetOf(xs,db);
//@ requires size(xs) > 1;
//@ ensures transactions(xs,db) === db[:,head(xs)] * transactions(tail(xs),db);
//@ {}

//@ lemma SingleTransactionsIdem (uint i, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemOf(i,db);
//@ ensures db[:,i] * db[:,i] === db[:,i];
//@ {
//@     assert forall uint j; j < shape(db)[0] ==> db[:,i][j] === db[j,i];
//@     MulBool(db[:,i]);
//@ }

//@ lemma TransactionsIdem (uint[[1]] xs, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemSetOf(xs,db);
//@ ensures transactions(xs,db) * transactions(xs,db) === transactions(xs,db);
//@ {
//@     if (size(xs) === 1) {
//@         SingleTransactionsIdem(head(xs),db);
//@     } else {
//@         TransactionsDef(xs,db);
//@         MulCommu4(db[:,head(xs)],transactions(tail(xs),db),db[:,head(xs)],transactions(tail(xs),db));
//@         SingleTransactionsIdem(head(xs),db);
//@         TransactionsIdem(tail(xs),db);
//@     }
//@ }

//@ lemma TransactionsSnoc (uint[[1]] xs, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemSetOf(xs,db);
//@ requires size(xs) > 1;
//@ ensures transactions(xs,db) === transactions(init(xs),db) * db[:,last(xs)];
//@ {
//@     if (size(xs) === 2) {
//@     } else {
//@         TransactionsDef(xs,db);
//@         TransactionsSnoc(tail(xs),db);
//@         MulAssoc(db[:,head(xs)],transactions(init(tail(xs)),db),db[:,last(xs)]);
//@         assert head(xs) === head(init(xs));
//@         assert init(tail(xs)) === tail(init(xs));
//@         TransactionsDef(init(xs),db);
//@     }
//@ }

//@ lemma JoinCaches(uint[[1]] C, pd_shared3p uint[[1]] C_dot, uint[[1]] xs, uint[[1]] ys, pd_shared3p uint[[2]] db, uint k)
//@ requires k > 1;
//@ requires IsDB(db);
//@ requires IsItemSetOf(xs,db);
//@ requires IsItemSetOf(ys,db);
//@ requires size(xs) === k-1;
//@ requires size(xs) === size(ys);
//@ requires Candidate(C,db,k);
//@ requires size(C_dot) === shape(db)[0];
//@ requires C === snoc(xs,last(ys));
//@ requires C_dot === transactions(xs,db) * transactions(ys,db);
//@ requires init(xs) === init(ys);
//@ ensures CandidateCache(C,C_dot,db,k);
//@ {
//@     if (size(xs) === 1)
//@     {
//@     } else {
//@         TransactionsSnoc(xs,db);
//@         TransactionsSnoc(ys,db);
//@         assert IsItemSetOf(init(xs),db);
//@         assert IsItemOf(last(xs),db);
//@         assert IsItemSetOf(init(ys),db);
//@         assert IsItemOf(last(ys),db);
//@         MulCommu4(transactions(init(xs),db),db[:,last(xs)],transactions(init(ys),db),db[:,last(ys)]);
//@         MulAssoc(transactions(init(xs),db),db[:,last(xs)],db[:,last(ys)]);
//@         TransactionsIdem(init(xs),db);
//@         TransactionsSnoc(C,db);
//@     }
//@ }
          
//* Leakage functions

//@ leakage predicate LeakFrequents (pd_shared3p uint[[2]] db, uint threshold, uint k)
//@ noinline;
//@ requires IsDB(db);
//@ { forall uint[[1]] is; (IsItemSetOf(is,db) && size(is) <= k) ==> public (frequency(is,db) >= threshold) }

//* Leakage proofs

//@ leakage lemma LeakFrequentsSmaller (pd_shared3p uint[[2]] db, uint threshold, uint k1, uint k2)
//@ requires IsDB(db);
//@ requires k1 <= k2;
//@ leakage requires LeakFrequents(db,threshold,k2);
//@ leakage ensures LeakFrequents(db,threshold,k1);

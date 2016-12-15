#OPTIONS_SECREC --implicitcoercions=extendedc --backtrack=fullb --matching=unorderedm --promote=localp

module apriori_spec2;

import shared3p;
import apriori_spec;

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

//* Correctness proofs

//@ template<domain D>
//@ context<>
//@ void SnocRange (D uint[[2]] xs, uint i, uint n)
//@ inline;
//@ {
//@     assert assertion(xs[i,:n+1] == snoc(xs[i,:n],xs[i,n]));
//@ }

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
//x //@ requires assertion(C_dot == transactions(xs,db) * transactions(ys,db));
//x //@ requires init(xs) == init(ys);
//x //@ ensures CandidateCache(C,C_dot,db,k);
//x 
//x //* Leakage functions
//x 
//x //@ leakage function bool LeakFrequents (pd_shared3p uint[[2]] db, uint threshold)
//x //@ noinline;
//x //@ requires IsDB(db);
//x //@ { forall uint[[1]] is; IsItemSetOf(is,db) ==> public (frequency(is,db) >= threshold) }
#OPTIONS_SECREC --path="examples" --implicitcoercions=extendedc --backtrack=fullb --matching=unorderedm --promote=localp --ignorespecdomains --verify=funcv --entrypoints="FrequentsCache:JoinCaches:LeakFrequents"

module apriori_spec2;

import shared3p;
import apriori_spec;

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

//x //* Leakage functions
//x 
//x //@ leakage function bool LeakFrequents (pd_shared3p uint[[2]] db, uint threshold)
//x //@ noinline;
//x //@ requires IsDB(db);
//x //@ { forall uint[[1]] is; IsItemSetOf(is,db) ==> public (frequency(is,db) >= threshold) }
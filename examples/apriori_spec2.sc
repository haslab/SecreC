#OPTIONS_SECREC --path="examples" --implicitcoercions=extendedc --backtrack=fullb --matching=unorderedm --promote=localp --ignorespecdomains

module apriori_spec2;

import shared3p;
import apriori_spec;

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
//@ requires assertion(C_dot == transactions(xs,db) * transactions(ys,db));
//@ requires init(xs) == init(ys);
//@ ensures CandidateCache(C,C_dot,db,k);

//* Leakage functions

//@ leakage function bool LeakFrequents (pd_shared3p uint[[2]] db, uint threshold)
//@ noinline;
//@ requires IsDB(db);
//@ { forall uint[[1]] is; IsItemSetOf(is,db) ==> public (frequency(is,db) >= threshold) }
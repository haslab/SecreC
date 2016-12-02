#OPTIONS_SECREC --implicitcoercions=defaultsc --verify=funcv --entrypoints="apriori"

module apriori;

//import stdlib;
//import shared3p;

kind shared3p;
domain pd_a3p shared3p;

template<domain D>
function D uint sum (D uint[[1]] xs)
context<>
//@ inline;
{
    __builtin("core.sum",xs) :: D uint
}

template <domain D >
function D uint[[1]] operator * (D uint[[1]] x,D uint[[1]] y)
context<>
//@ inline;
{
    __builtin("core.mul",x,y) :: D uint[[1]]
}

template <type T, dim N>
void printArray (T[[N]] arr) {
}

pd_a3p uint [[2]] load_db () {
    pd_a3p uint [[2]] db (5,5);
    db[0, 0] = classify(1);
    db[0, 1] = classify(1);
    db[0, 3] = classify(1);
    db[1, 0] = classify(1);
    db[1, 3] = classify(1);
    db[1, 4] = classify(1);
    db[2, 0] = classify(1);
    db[2, 1] = classify(1);
    db[3, 2] = classify(1);
    db[4, 1] = classify(1);
    db[4, 2] = classify(1);
    db[4, 3] = classify(1);
    return db;
}

//@ function bool IsItemSetOf (uint[[1]] is, pd_a3p uint[[2]] db)
//@ noinline;
//@ { size(is) > 0 && forall uint i; i < size(is) ==> is[i] < shape(db)[1] }

//@ function bool hasItemsOf (uint[[2]] F, pd_a3p uint[[2]] db)
//@ noinline;
//@ { (forall uint i, uint j; i < shape(F)[0] && j < shape(F)[1] ==> F[i,j] < shape(db)[1]) }


//@ function pd_a3p uint[[1]] transactions (uint[[1]] is, pd_a3p uint[[2]] db)
//@ noinline;
//@ requires IsItemSetOf(is,db);
//@ ensures size(\result) == shape(db)[0];
//@ { (size(is) == 1) ? db[:,is[0]] : db[:,is[0]] * transactions(is[1:],db) }

//@ function pd_a3p uint frequency (uint[[1]] is, pd_a3p uint[[2]] db)
//@ noinline;
//@ requires IsItemSetOf(is,db);
//@ { sum(transactions(is,db)) }

//@ leakage function bool LeakFrequents (pd_a3p uint[[2]] db, uint threshold)
//@ noinline;
//@ { forall uint[[1]] is; IsItemSetOf(is,db) ==> public (frequency(is,db) >= classify(threshold)) }

//@ function bool FrequentsCache(uint[[2]] F, pd_a3p uint[[2]] Fcache, pd_a3p uint[[2]] db, uint threshold)
//@ noinline;
//@ {
//@     shape(F)[0] == shape(Fcache)[0]
//@     &&
//@     shape(Fcache)[1] == shape(db)[0]
//@     &&
//@     hasItemsOf(F,db)
//@     &&
//@     forall uint i; i < shape(F)[0]
//@            ==> IsItemSetOf(F[i,:],db)
//@            &&  declassify(frequency(F[i,:],db)) >= threshold
//@            &&  declassify(Fcache[i,:] == transactions(F[i,:],db))
//@ }

//@ function bool AllFrequents(uint[[2]] F, pd_a3p uint[[2]] db, uint threshold, uint i)
//@ noinline;
//@ requires i <= shape(db)[1];
//@ {
//@     forall uint j; (j < i && declassify(frequency({j},db)) >= threshold) ==> in({j},set(F))
//@ }

struct frequent {
    uint [[2]] items;
    pd_a3p uint [[2]] cache;
}

frequent apriori_1 (pd_a3p uint [[2]] db, uint threshold)
//@ leakage requires LeakFrequents(db,threshold);
//@ ensures shape(\result.items)[1] == 1;
//@ ensures FrequentsCache(\result.items,\result.cache,db,threshold);
//@ ensures AllFrequents(\result.items,db,threshold,shape(db)[1]);
{
    frequent ret;
    uint [[2]] F (0, 1); // frequent itemsets
    pd_a3p uint [[2]] F_cache (0, shape(db)[0]); // cached column data for corresponding frequent itemsets in F, i.e., which transactions contain the itemset
    
    // compute the itemsets of size 1
    for (uint i = 0; i < shape(db)[1]; i=i+1)
    //@ invariant i <= shape(db)[1];
    //@ invariant shape(F)[0] <= i;
    //@ invariant shape(F)[1] == 1;
    //@ invariant FrequentsCache(F,F_cache,db,threshold);
    //@ invariant AllFrequents(F,db,threshold,i);
    {
      //@ assert IsItemSetOf({i},db);
      pd_a3p uint [[1]] z = db[:, i]; // all transactions where an item i occurs
      //x //@ assert z == transactions({i},db);
      pd_a3p uint frequence = sum (z); // frequency of item i
      //x //@ assert frequence == frequency({i},db);
      if (declassify (frequence >= classify(threshold))) {
        F = snoc (F,{i});
        F_cache = snoc (F_cache,z);  
      }
    }
    ret.items = F;
    ret.cache = F_cache;
    return ret;
}

frequent apriori_k (pd_a3p uint [[2]] db, uint threshold, uint k)
//@ requires k > 0;
//@ leakage requires LeakFrequents(db,threshold);
//@ ensures shape(\result.items)[1] == k;
//@ ensures FrequentsCache(\result.items,\result.cache,db,threshold);
//@ ensures AllFrequents(\result.items,db,threshold,shape(db)[1]);
{
    
}

// database rows = transaction no, database column = item no
// result = one itemset per row
uint[[2]] apriori (pd_a3p uint [[2]] db, uint threshold, uint setSize)
//@ requires setSize > 0;
//@ leakage requires LeakFrequents(db,threshold);
{
    frequent freq = apriori_1(db,threshold);
  
  
  //// until we find itemsets with length setSize
  //for (uint k = 1; k < setSize; k=k+1)
  ////@ invariant 1 <= k && k <= setSize;
  ////@ invariant shape(F)[1] == k;
  ////@ invariant FrequentsCache(F,F_cache,db,threshold);
  //{
  //  uint [[2]] F_new (0, k + 1);
  //  pd_a3p uint [[2]] F_new_cache (0, dbRows);
  //  uint F_size = shape(F)[0]; // number of items for k-1
  //  for (uint i = 0; i < F_size; i=i+1) // for each itemset in F
  //  //@ invariant i <= F_size;
  //  //@ invariant shape(F_new)[1] == k+1;
  //  //@ invariant FrequentsCache(F_new,F_new_cache,db,threshold);
  //  {
  //    for (uint j = i + 1; j < F_size; j=j+1) // for each other itemset in F
  //    //@ invariant i < j && j <= F_size;
  //    //@ invariant shape(F_new)[1] == k+1;
  //    //@ invariant FrequentsCache(F_new,F_new_cache,db,threshold);
  //    {
  //      // check if the two itemsets have the same prefix (this is always true for singleton itemsets)
  //      bool prefixEqual = true;
  //      for (uint n = 0; n < k - 1; n=n+1)
  //      {
  //        if (F[i, n] != F[j, n]) {
  //          prefixEqual = false;
  //        }
  //      }
  //      //itemsets are ordered by item, hence the comparison in the test
  //      if (prefixEqual && F[i, k-1] < F[j, k-1]) {
  //        // new candidate itemset
  //        // create the new itemset by appending the last element of the second itemset to the first
  //        uint [[1]] C;
  //        //@ assert IsItemSetOf(F[i,:],db);
  //        //@ assert F[j,k-1] < dbColumns;
  //        C = snoc (F[i, :], F[j, k-1]);
  //        //@ assert IsItemSetOf(C,db);
  //        //join the two caches
  //        pd_a3p uint [[1]] C_dot (dbRows); // column data (dot product) for the new candidate itemset C
  //        C_dot = F_cache[i, :] * F_cache[j, :];
  //        //@ assert C_dot == transactions(C,db);
  //        // compute the joint frequency
  //        pd_a3p uint frequence = sum (C_dot);
  //        //if (declassify (frequence >= classify(threshold))) {
  //        //  F_new_cache = cat (F_new_cache, reshape(C_dot, 1, size(C_dot)));
  //        //  F_new = cat (F_new, reshape(C, 1, k+1));
  //        //}
  //      }
  //    }
  //  }
  //  
  //  F = F_new;
  //  F_cache = F_new_cache;
  //}

  return freq.items;
}


void main () {
    pd_a3p uint [[2]] db = load_db ();
    uint [[2]] itemsets = apriori (db, 1 :: uint, 3 :: uint);
    printArray (itemsets);
}

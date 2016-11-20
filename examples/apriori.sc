#OPTIONS_SECREC --implicitcoercions=defaultsc --verify --entrypoints="apriori"

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
//@ requires size(x) == size(y);
//@ ensures size(\result) == size(x);
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

//@ template <domain D>
//@ function set<uint> itemsof(D uint[[2]] db)
//@ context<>
//@ noinline;
//@ ensures forall uint i; in(i,\result) ==> i < shape(db)[1];
//@ { (set uint x | 0 <= x && x < shape(db)[1]) }

//x //@ axiom <domain D,type T> (uint[[1]] is, D uint[[2]] db)
//x //@ requires set(is) <= itemsof(db);
//x //@ ensures forall uint i; i < size(is) ==> is[i] < shape(db)[1];

//@ template <nonpublic kind K, domain D : K>
//@ function D uint[[1]] transactions (uint[[1]] is, D uint[[2]] db)
//@ context<>
//@ noinline;
//@ requires forall uint i; i < size(is) ==> is[i] < shape(db)[1];
//@ ensures size(\result) == shape(db)[0];
//@ { (size(is) == 0) ? repeat(classify(1),shape(db)[0]) : db[:,is[0]] * transactions(is[1:],db) }

//@ template <nonpublic kind K,domain D : K, type T>
//@ leakage function bool lfrequents (D uint[[2]] db, uint threshold)
//@ context<>
//@ noinline;
//@ { forall uint[[1]] is; set(is) <= itemsof(db) ==> public (sum(transactions(is,db)) >= classify(threshold)) }

// database rows = transaction no, database column = item no
// result = one itemset per row
uint [[2]] apriori (pd_a3p uint [[2]] db, uint threshold, uint setSize)
//@ leakage requires lfrequents(db,threshold);
{
  uint dbColumns = shape(db)[1]; // number of items
  uint dbRows = shape(db)[0]; // number of transactions

  uint [[2]] F (0, 1); // frequent itemsets
  //@ assert shape(F)[0] == 0;
  //@ assert shape(F)[1] == 0;
  pd_a3p uint [[2]] F_cache (0, dbRows); // cached column data for corresponding frequent itemsets in F, i.e., which transactions contain the itemset

  uint [[2]] F_new; // new frequent itemsets based on existing ones in F
  pd_a3p uint [[2]] F_newcache (0, dbRows); // cached column data for newly generated frequent itemsets

  uint [[1]] C; // new candidate itemset
  pd_a3p uint [[1]] C_dot (dbRows); // column data (dot product) for the new candidate itemset C

  // compute the itemsets of size 1
  //x for (uint i = 0; i < dbColumns; i=i+1)
  //x //@ invariant shape(F)[0] <= i;
  //x //@ invariant shape(F)[1] == 1;
  //x {
  //x   pd_a3p uint [[1]] z = db[:, i]; // all transactions where an item i occurs
  //x   pd_a3p uint frequence = sum (z); // frequency of item i
  //x   if (declassify (frequence >= classify(threshold))) {
  //x     F = cat (F, reshape(i, 1, 1));
  //x     //F_cache = cat (F_cache, reshape (z, 1, dbRows));
  //x   }
  //x }
  
  //// until we find itemsets with length setSize
  //for (uint k = 1; k < setSize; k=k+1)
  ////x //@ invariant shape(F)[1] == k;
  //{
  //  F_new = reshape ({}, 0, k + 1); // empty?
  //  F_newcache = reshape ({}, 0, dbRows); // empty?
  //  uint F_size = shape(F)[0]; // number of items for k-1
  //  for (uint i = 0; i < F_size; i=i+1) // for each itemset in F
  //  {
  //    for (uint j = i + 1; j < F_size; j=j+1) // for each other itemset in F
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
  //        pd_a3p uint [[1]] C_dot = F_cache[i, :] * F_cache[j, :]; //join the two caches
  //        pd_a3p uint frequence = sum (C_dot); // compute the joint frequency
  //        if (declassify (frequence >= classify(threshold))) {
  //          F_newcache = cat (F_newcache, reshape(C_dot, 1, size(C_dot)));
  //          // create the new itemset by appending the last element of the second itemset to the first
  //          C = cat (F[i, :], F[j, k-1:k]);
  //          F_new = cat (F_new, reshape(C, 1, k+1));
  //        }
  //      }
  //    }
  //  }
  //  
  //  F = F_new;
  //  F_cache = F_newcache;
  //}

  return F;
}


void main () {
    pd_a3p uint [[2]] db = load_db ();
    uint [[2]] itemsets = apriori (db, 1 :: uint, 3 :: uint);
    printArray (itemsets);
}

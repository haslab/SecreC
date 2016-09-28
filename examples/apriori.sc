module apriori;

import stdlib;
import shared3p;

domain pd_a3p shared3p;

function pd_a3p bool operator >= (pd_a3p uint x,pd_a3p uint y) {
    __builtin("core.ge",x,y) :: pd_a3p bool
}

// database rows = transaction no, database column = item no
// result = one itemset per row
template <domain D >
uint [[2]] apriori (D uint [[2]] db, uint threshold, uint setSize)
//x //@ leakage requires public(frequents(db));
//x //@ ensures \result == frequents(db);
//x //@ ensures shape(\result)[1] == setSize; //
{
  uint dbColumns = shape(db)[1];
  uint dbRows = shape(db)[0];

  uint [[2]] F (0, 1); // frequent itemsets
  D uint [[2]] F_cache (0, dbRows); // cached column data for corresponding frequent itemsets in F, i.e., which transactions contain the itemset

  uint [[2]] F_new; // new frequent itemsets based on existing ones in F
  D uint [[2]] F_newcache (0, dbRows); // cached column data for newly generated frequent itemsets

  uint [[1]] C; // new candidate itemset
  D uint [[1]] C_dot (dbRows); // column data (dot product) for the new candidate itemset C

  // compute the itemsets of size 1
  for (uint i = 0; i < dbColumns; i=i+1)
  //x //@ invariant shape(F)[0] <= dbColumns;
  //x //@ invariant shape(F)[1] == 1;
  //x //@ invariant shape(F_cache)[0] == shape(F)[0];
  //x //@ invariant shape(F_cache)[1] == dbRows;
  {
    D uint [[1]] z = db[:, i]; // all transactions where an item i occurs
    D uint frequence = sum (z); // frequency of item i
    if (declassify (frequence >= threshold)) {
      F = cat (F, reshape((uint) i, 1, 1));
      F_cache = cat (F_cache, reshape (z, 1, dbRows));
    }
  }
  
  // until we find itemsets with length setSize
  //for (uint k = 1; k < setSize; k=k+1)
  ////x //@ invariant shape(F)[1] == k;
  //{
  //  F_new = reshape (0, 0, k + 1); // empty?
  //  F_newcache = reshape (0, 0, dbRows); // empty?
  //  uint F_size = shape(F)[0];
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
  //      
  //      if (prefixEqual && F[i, k-1] < F[j, k-1]) {
  //        D uint [[1]] C_dot = F_cache[i, :] * F_cache[j, :];
  //        D uint frequence = sum (C_dot);
  //        if (declassify (frequence >= threshold)) {
  //          F_newcache = cat (F_newcache, reshape(C_dot, 1, size(C_dot)));
  //          // create the new itemset by appending the last element of the second itemset to the fist
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
    pd_a3p uint [[2]] db; // = load_db ();
    //x //@ leakage infer frequents(db);
    uint [[2]] itemsets = apriori (db, 1 :: uint, 3 :: uint);
    //printArray (itemsets);
}

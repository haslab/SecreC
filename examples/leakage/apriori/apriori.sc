/*
 * This file is a part of the Sharemind framework.
 *
 * Copyright (C) AS Cybernetica
 * All rights are reserved. Reproduction in whole or part is prohibited
 * without the written consent of the copyright owner.
 *
 * Main contributors:
 * Roman Jagomgis (neo15@ut.ee)
 */

import stdlib;
import shared3p;

domain pd_a3p shared3p;

// ./bin/scc -o t.sb ../00-apriori.sc  -I ../src/stdlib/


//template <domain D>
//D uint [[2]] load_db () {
//    D uint [[2]] db = reshape (0, 5, 5);
//    db[0, 0] = 1; db[0, 1] = 1;               db[0, 3] = 1;
//    db[1, 0] = 1;                             db[1, 3] = 1; db[1,4] = 1;
//    db[2, 0] = 1; db[2, 1] = 1;
//                                db[3, 2] = 1;
//                  db[4, 1] = 1; db[4, 2] = 1; db[4, 3] = 1;
//    return db;
//}
    


//Property: all subsets of a frequent itemset are frequent
//
//Problem:
//Assume that
//t1 = 1,2,3,6
//t2 = 1,2,3,4
//t3 = 1,2,5

//db =
//1,1,1,0,0,1
//1,1,1,1,0,0
//1,1,0,0,1,0

//
//Frequent itemsets of size 2 with threshold 2 = {{1,2},{1,3},{2,3}}
//
//Frequent itemsets of size 3 with threshold 3 = {}
//However, the apriori code is declassifying the comparison of the frequencies of all subsets, e.g. {1,2}, but from the result we don't know that {1,2} is frequent.

// database rows = transaction no, database column = item no
// result = one itemset per row
template <domain D >
uint [[2]] apriori (D uint [[2]] db, uint threshold, uint setSize)
//@ leakage requires public(frequents(db));
//@ ensures \result == frequents(db);
//@ ensures shape(\result)[1] == setSize; //
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
  for (uint k = 1; k < setSize; k=k+1)
  //x //@ invariant shape(F)[1] == k;
  {
    F_new = reshape (0, 0, k + 1); // empty?
    F_newcache = reshape (0, 0, dbRows); // empty?
    uint F_size = shape(F)[0];
    for (uint i = 0; i < F_size; i=i+1) {
      for (uint j = i + 1; j < F_size; j=j+1) {
        bool prefixEqual = true;
        for (uint n = 0; n < k - 1; n=n+1) {
          if (F[i, n] != F[j, n]) {
            prefixEqual = false;
          }
        }
        
        if (prefixEqual && F[i, k-1] < F[j, k-1]) {
          D uint [[1]] C_dot = F_cache[i, :] * F_cache[j, :];
          D uint frequence = sum (C_dot);
          if (declassify (frequence >= threshold)) {
            F_newcache = cat (F_newcache, reshape(C_dot, 1, size(C_dot)));
            C = cat (F[i, :], F[j, k-1:k]);
            F_new = cat (F_new, reshape(C, 1, k+1));
          }
        }
      }
    }
    
    F = F_new;
    F_cache = F_newcache;
  }

  return F;
}


void main () {
    pd_a3p uint [[2]] db; // = load_db ();
    //x //@ leakage infer frequents(db);
    uint [[2]] itemsets = apriori (db, 1 :: uint, 3 :: uint);
    //printArray (itemsets);
}

#OPTIONS_SECREC --paths="examples" --implicitcoercions=onc --backtrack=tryb --matching=gorderedm --promote=nop --verify=funcv --entrypoints="apriori"

/*
 * This file is a part of the Sharemind framework.
 *
 * Copyright (C) AS Cybernetica
 * All rights are reserved. Reproduction in whole or part is prohibited
 * without the written consent of the copyright owner.
 *
 * Main contributors:
 * Roman Jagomagis (neo15@ut.ee)
 */

module apriori;

//import stdlib;
//import shared3p;
//import table_database;
//import shared3p_table_database;
import axioms;

import apriori_spec;

template <domain D>
D uint [[2]] load_db ()
//@ ensures IsDB(\result);
{
    string data_source = "DS1";
    string table_name = "FIMTable";

    tdbOpenConnection(data_source);
    assert(tdbTableExists(data_source, table_name));

    uint columns = tdbGetColumnCount (data_source, table_name);
    uint rows = tdbGetRowCount (data_source, table_name);

    D uint [[2]] db(rows, columns);

    for (uint i = 0; i < columns; i++) {
        db[:, i] = tdbReadColumn (data_source, table_name, i);
    }

    return db;
}

frequent AddFrequent(frequent f, uint[[1]] C, pd_shared3p uint[[1]] C_dot, pd_shared3p uint [[2]] db, uint threshold)
//@ requires IsDB(db);
//x //@ requires IsItemSetOf(C,db);
//@ requires CandidateCache(C,C_dot,db,size(C));
//x //@ requires shape(f.items)[0] == shape(f.cache)[0];
//x //@ requires shape(f.cache)[1] == size(C_dot);
//x //@ ensures shape(\result.items)[0] == shape(\result.cache)[0];
//@ ensures shape(\result.items)[0] <= shape(f.items)[0] + 1;
//@ ensures shape(\result.cache)[1] == size(C_dot);
//x //@ requires assertion<pd_shared3p>(C_dot == transactions(C,db) :: pd_shared3p bool);
//@ leakage requires LeakFrequents(db,threshold);
//@ requires FrequentsCache(f,db,threshold,size(C));
//@ ensures FrequentsCache(\result,db,threshold,size(C));
{
    pd_shared3p uint frequence = sum (C_dot);
    //@ assert assertion(frequency(C,db) == frequence);
    if (declassify (frequence >= threshold)) {
      f.items = snoc (f.items,C);
      f.cache = snoc (f.cache,C_dot);  
    }
    return f;
}

frequent apriori_1 (pd_shared3p uint [[2]] db, uint threshold)
//@ requires IsDB(db);
//@ leakage requires LeakFrequents(db,threshold);
//@ ensures FrequentsCache(\result,db,threshold,1);
{
    frequent f = newfrequent(1,db);

    for (uint i = 0; i < shape(db)[1]; i=i+1)
    //@ invariant i <= shape(db)[1];
    //@ invariant shape(f.items)[0] <= i;
    //@ invariant FrequentsCache(f,db,threshold,1);
    {
        //@ assert size({i}) == 1;
        //@ assert size(db[:,i]) == shape(db)[0];
        //@ assert IsItemSetOf({i},db);
        //@ assert assertion(db[:,i] == transactions({i},db) :: pd_shared3p bool);
      f = AddFrequent(f,{i},db[:,i],db,threshold);
    }
    return f;
}

frequent apriori_k (pd_shared3p uint [[2]] db, uint threshold, frequent prev,uint k)
//@ requires IsDB(db);
//@ requires k >= 1;
//@ leakage requires LeakFrequents(db,threshold);
//@ requires FrequentsCache(prev,db,threshold,k);
//@ ensures FrequentsCache(\result,db,threshold,k+1);
{
    frequent next = newfrequent(k+1,db);
    
    uint prev_F_size = shape(prev.items)[0];
    for (uint i = 0; i < prev_F_size; i=i+1)
    //@ invariant i <= prev_F_size;
    //@ invariant FrequentsCache(next,db,threshold,k+1);
    {
      for (uint j = i + 1; j < prev_F_size; j=j+1)
      //@ invariant i < j && j <= prev_F_size;
      //@ invariant FrequentsCache(next,db,threshold,k+1);
      {
        bool prefixEqual = true;
        uint n = 0;
        //@ assert prev.items[i,:n] == {};
        //@ assert prev.items[j,:n] == {};
        //@ assert prev.items[i,:n] == prev.items[j,:n];
        //@ assert prefixEqual == (prev.items[i,:n] == prev.items[j,:n] :: bool);
        for (; n < k - 1; n=n+1)
        //@ invariant n < k;
        //@ invariant prefixEqual == (prev.items[i,:n] == prev.items[j,:n] :: bool);
        //x //@ invariant prefixEqual == forall uint m; m < n ==> prev.items[i,m] == prev.items[j,m];
        {
          if (prev.items[i, n] != prev.items[j, n]) {
            prefixEqual = false;
          }
          //@ assert prev.items[i,:n+1] == snoc(prev.items[i,:n],prev.items[i,n]);
          //@ assert prev.items[j,:n+1] == snoc(prev.items[j,:n],prev.items[j,n]);
        }
        if (prefixEqual && prev.items[i, k-1] < prev.items[j, k-1])
        {
          //@ assert (prev.items[i,:k-1] == prev.items[j,:k-1] :: bool);
          //@ assert (init(prev.items[i,:]) == prev.items[i,:k-1] :: bool);
          //@ assert (init (prev.items[j,:]) == prev.items[j,:k-1] :: bool);
          //@ assert prev.items[j,:][k-1] == prev.items[j,k-1];
          //@ assert prev.items[j,k-1] < shape(db)[1];
          uint[[1]] C = snoc (prev.items[i, :], prev.items[j, k-1]);
          //@ assert (last(prev.items[i,:]) == prev.items[i,k-1] :: bool);
          //@ assert IsItemSetOf(C,db);
          pd_shared3p uint [[1]] C_dot = prev.cache[i, :] * prev.cache[j, :];
          //@ JoinCaches(C,C_dot,prev.items[i,:],prev.items[j,:],db,k+1);
          next = AddFrequent(next,C,C_dot,db,threshold);
          //@ assert size(C) == k+1;
          //@ assert shape(next.items)[1] == k+1;
        }
      }
    }
    return next;
}

uint[[2]] apriori (pd_shared3p uint [[2]] db, uint threshold, uint setSize)
//@ requires IsDB(db);
//@ requires setSize > 0;
//@ leakage requires LeakFrequents(db,threshold);
//x //@ free ensures AllFrequents(\result,db,threshold);
{
  frequent freq = apriori_1(db,threshold);
  
  for (uint k = 1; k < setSize; k=k+1)
  //@ invariant 1 <= k && k <= setSize;
  //@ invariant FrequentsCache(freq,db,threshold,k);
  {
      freq = apriori_k(db,threshold,freq,k);
  }

  return freq.items;
}


void main () {
    pd_shared3p uint [[2]] db = load_db ();
    uint[[2]] itemsets = apriori (db, 2 :: uint, 2 :: uint);
    printMatrix (declassify(db));
    printMatrix (itemsets);
}

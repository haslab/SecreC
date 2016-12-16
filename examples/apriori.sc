//#OPTIONS_SECREC --paths="examples" --implicitcoercions=onc --backtrack=tryb --matching=gorderedm --promote=nop --verify=bothv --entrypoints="apriori" --ignorespecdomains

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

import stdlib;
import shared3p;
import table_database;
import shared3p_table_database;
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
//@ requires FrequentsCache(f,db,threshold,size(C));
//@ requires CandidateCache(C,C_dot,db,size(C));
//@ leakage requires LeakFrequents(db,threshold);
//@ ensures FrequentsCache(\result,db,threshold,size(C));
//@ ensures shape(\result.items)[0] <= shape(f.items)[0] + 1;
{
    pd_shared3p uint frequence = sum (C_dot);
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
    frequent f = newfrequent(1 :: uint,db);

    for (uint i = 0; i < shape(db)[1]; i=i+1)
    //@ invariant i <= shape(db)[1];
    //@ invariant shape(f.items)[0] <= i;
    //@ invariant FrequentsCache(f,db,threshold,1);
    {
      f = AddFrequent(f,{i},db[:,i],db,threshold);
    }
    return f;
}

frequent apriori_k (pd_shared3p uint [[2]] db, uint threshold, frequent prev,uint k)
//@ requires IsDB(db);
//@ requires k >= 1;
//@ requires FrequentsCache(prev,db,threshold,k);
//@ leakage requires LeakFrequents(db,threshold);
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
        for (uint n = 0; n < k - 1; n=n+1)
        //@ invariant n < k;
        //@ invariant prefixEqual == (prev.items[i,:n] == prev.items[j,:n] :: bool);
        {
          if (prev.items[i, n] != prev.items[j, n]) {
            prefixEqual = false;
          }
          //@ SnocRange(prev.items,i,n); SnocRange(prev.items,j,n);
        }
        if (prefixEqual && prev.items[i, k-1] < prev.items[j, k-1])
        {
          //@ assert (init(prev.items[i,:]) == prev.items[i,:k-1] :: bool);
          //@ assert (init (prev.items[j,:]) == prev.items[j,:k-1] :: bool);
          //@ assert prev.items[j,:][k-1] == prev.items[j,k-1];
          //@ assert prev.items[j,k-1] < shape(db)[1];
          uint[[1]] C = snoc (prev.items[i, :], prev.items[j, k-1]);
          //@ assert (last(prev.items[i,:]) == prev.items[i,k-1] :: bool);
          pd_shared3p uint [[1]] C_dot = prev.cache[i, :] * prev.cache[j, :];
          //@ JoinCaches(C,C_dot,prev.items[i,:],prev.items[j,:],db,k+1);
          next = AddFrequent(next,C,C_dot,db,threshold);
        }
      }
    }
    return next;
}

uint[[2]] apriori (pd_shared3p uint [[2]] db, uint threshold, uint setSize)
//@ requires IsDB(db);
//@ requires setSize > 0;
//@ leakage requires LeakFrequents(db,threshold);
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

#OPTIONS_SECREC --implicitcoercions=onc --backtrack=tryb --matching=gorderedm --promote=nop --verify=funcv --entrypoints="apriori"

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

domain pd_shared3p shared3p;

//@ function bool IsDB (pd_shared3p uint[[2]] db)
//@ noinline;
//@ {
//@     forall pd_shared3p uint x; assertion<pd_shared3p>(in(x,db) ==> x <= classify(1))
//@ }

template <domain D>
D uint [[2]] load_db ()
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

struct frequent {
    uint [[2]] items;
    pd_shared3p uint [[2]] cache;
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

//@ function bool IsItemSet (uint[[1]] is, uint sz)
//@ noinline;
//@ {
//@    size(is) > 0
//@    && (forall uint k; k < size(is) ==> is[k] < sz)
//@    && (forall uint i, uint j; i < j && j < size(is) ==> is[i] < is[j])
//@ }

//x //@ axiom<> (uint i, uint sz)
//x //@ requires i < sz;
//x //@ ensures IsItemSet({i},sz);

//@ function bool IsItemSetOf (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ { IsItemSet(is,shape(db)[1]) }

//@ function pd_shared3p uint[[1]] transactions (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ noinline;
//@ requires IsDB(db);
//@ requires IsItemSetOf(is,db);
//@ ensures size(\result) == shape(db)[0];
//@ { (size(is) == 1) ? db[:,is[0]] : db[:,is[0]] * transactions(is[1:],db) }

//@ function pd_shared3p uint frequency (uint[[1]] is, pd_shared3p uint[[2]] db)
//@ noinline;
//@ requires IsDB(db);
//@ requires IsItemSetOf(is,db);
//@ { sum(transactions(is,db)) }

//@ leakage function bool LeakFrequents (pd_shared3p uint[[2]] db, uint threshold)
//@ noinline;
//@ requires IsDB(db);
//@ { forall uint[[1]] is; IsItemSetOf(is,db) ==> public (frequency(is,db) >= classify(threshold)) }

//@ function bool FrequentsCache(frequent f, pd_shared3p uint[[2]] db, uint threshold)
//@ noinline;
//@ requires IsDB(db);
//@ {
//@     shape(f.items)[0] == shape(f.cache)[0]
//@     &&
//@     shape(f.cache)[1] == shape(db)[0]
//@     &&
//@     (forall uint i; i < shape(f.items)[0]
//@            ==> IsItemSetOf(f.items[i,:],db)
//@            &&  declassify(frequency(f.items[i,:],db)::pd_shared3p uint) >= threshold
//@            &&  declassify(f.cache[i,:] == transactions(f.items[i,:],db)))
//@ }

//x //@ lemma SameItemTransactions(uint i, pd_shared3p uint[[2]] db)
//x //@ requires IsDB(db);
//x //@ requires i < shape(db)[1];
//x //@ ensures db[:,i] * db[:,i] == db[:,i];
//x //@ {}

//@ lemma JoinCaches(uint[[1]] C, pd_shared3p uint[[1]] C_dot, uint[[1]] xs, uint[[1]] ys, pd_shared3p uint[[2]] db)
//@ requires IsDB(db);
//@ requires IsItemSetOf(xs,db);
//@ requires IsItemSetOf(ys,db);
//@ requires size(xs) == size(ys);
//@ requires IsItemSetOf(C,db);
//@ requires (C == snoc(xs,last(ys)) :: bool);
//@ requires assertion(C_dot == transactions(xs,db) * transactions(ys,db) :: pd_shared3p bool);
//@ requires init(xs) == init(ys);
//x //@ requires forall uint n; n < size(xs)-1 ==> xs[n] == ys[n];
//@ ensures assertion(C_dot == transactions(C,db) :: pd_shared3p bool);


//x //@ assert transactions(prev.items[i,:]) == transactions(init(prev.items[i,:])) * transaction(last(prev.items[i,:]));
//x //@ assert transactions(prev.items[j,:]) == transactions(init(prev.items[j,:])) * transaction(last(prev.items[j,:]));
//x //@ assert transactions(C) == transactions(prev.items[i,:]) * transaction(last(prev.items[j,:]));

frequent AddFrequent(frequent f, uint[[1]] C, pd_shared3p uint[[1]] C_dot, pd_shared3p uint [[2]] db, uint threshold)
//@ requires IsDB(db);
//@ requires IsItemSetOf(C,db);
//@ requires shape(f.items)[1] == size(C);
//@ requires shape(f.cache)[1] == size(C_dot);
//@ ensures shape(\result.items)[1] == size(C);
//@ ensures shape(\result.cache)[1] == size(C_dot);
//@ requires assertion<pd_shared3p>(C_dot == transactions(C,db) :: pd_shared3p bool);
//@ leakage requires LeakFrequents(db,threshold);
//@ requires FrequentsCache(f,db,threshold);
//@ ensures FrequentsCache(\result,db,threshold);
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
//@ ensures shape(\result.items)[1] == 1;
//@ ensures FrequentsCache(\result,db,threshold);
{
    frequent f = newfrequent(1,db);

    for (uint i = 0; i < shape(db)[1]; i=i+1)
    //@ invariant i <= shape(db)[1];
    //@ invariant shape(f.items)[0] <= i;
    //@ invariant shape(f.items)[1] == 1;
    //@ invariant FrequentsCache(f,db,threshold);
    {
      //@ assert assertion(db[:,i] == transactions({i},db) :: pd_shared3p bool);
      AddFrequent(f,{i},db[:,i],db,threshold);
    }
    return f;
}

frequent apriori_k (pd_shared3p uint [[2]] db, uint threshold, frequent prev,uint k)
//@ requires IsDB(db);
//@ requires k >= 1;
//@ requires shape(prev.items)[1] == k;
//@ leakage requires LeakFrequents(db,threshold);
//@ ensures shape(\result.items)[1] == k + 1;
//@ requires FrequentsCache(prev,db,threshold);
//@ ensures FrequentsCache(\result,db,threshold);
{
    frequent next = newfrequent(k+1,db);
    
    uint prev_F_size = shape(prev.items)[0];
    for (uint i = 0; i < prev_F_size; i=i+1)
    //@ invariant i <= prev_F_size;
    //@ invariant shape(next.items)[1] == k+1;
    //@ invariant FrequentsCache(next,db,threshold);
    {
      for (uint j = i + 1; j < prev_F_size; j=j+1) // for each other itemset in F
      //@ invariant i < j && j <= prev_F_size;
      //@ invariant shape(next.items)[1] == k+1;
      //@ invariant FrequentsCache(next,db,threshold);
      {
        bool prefixEqual = true;
        for (uint n = 0; n < k - 1; n=n+1)
        //@ invariant n < k;
        //@ invariant prefixEqual == (prev.items[i,:n] == prev.items[j,:n] :: bool);
        {
          if (prev.items[i, n] != prev.items[j, n]) {
            prefixEqual = false;
          }
          //@ Snoc1(prev.items[i,:n]);
          //@ Snoc1(prev.items[j,:n]);
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
          //@ JoinCaches(C,C_dot,prev.items[i,:],prev.items[j,:],db);
          AddFrequent(next,C,C_dot,db,threshold);
          
        }
      }
    }
    return next;
}

//@ function bool AllFrequents(frequent[[1]] freqs, pd_shared3p uint[[2]] db, uint threshold)
//@ noinline;
//@ {
//@     forall uint[[1]] js; IsItemSetOf(js,db) && declassify(frequency(js,db)) >= threshold ==> in(js,set(freqs[size(js)-1].items))
//@ }

frequent[[1]] apriori (pd_shared3p uint [[2]] db, uint threshold, uint setSize)
//@ requires IsDB(db);
//@ requires setSize > 0;
//@ leakage requires LeakFrequents(db,threshold);
//@ free ensures AllFrequents(\result,db,threshold);
{
  frequent[[1]] freqs = {apriori_1(db,threshold)};
  
  for (uint k = 1; k < setSize; k=k+1)
  //@ invariant 1 <= k && k <= setSize;
  //X //@ invariant shape(last(freqs).items)[1] == k;
  //@ invariant forall uint i; i < size(freqs) ==> FrequentsCache(freqs[i],db,threshold);
  {
      freqs = snoc(freqs,apriori_k(db,threshold,last(freqs),k));
  }

  return freqs;
}


void main () {
    pd_shared3p uint [[2]] db = load_db ();
    frequent [[1]] itemsets = apriori (db, 2 :: uint, 2 :: uint);
    printMatrix (declassify(db));
    for (uint i = 0; i < size(itemsets); i++)
        printArray (itemsets[i]);
}

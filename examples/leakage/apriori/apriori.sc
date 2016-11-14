#OPTIONS_SECREC --implicitcoercions=defaultsc

module apriori;

//import stdlib;
//import shared3p;

kind shared3p;
domain pd_a3p shared3p;

template<domain D>
D uint sum (D uint[[1]] xs) {
	havoc D uint res;
	return res;
}

pd_a3p uint [[2]] load_db () {
    pd_a3p uint [[2]] db = reshape (repeat(classify(0),25), 5, 5);
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

struct itemset {
    uint[[2]] items;
}

itemset[[1]] apriori (pd_a3p uint [[2]] db, uint threshold, uint setSize)
{
  uint dbColumns = shape(db)[1]; // number of items
  uint dbRows = shape(db)[0]; // number of transactions

  itemset[[1]] frequents;
  itemset frequent;

  uint[[2]] F (0,1); // frequent itemsets
  pd_a3p uint [[2]] F_cache (0, dbRows); // cached column data for corresponding frequent itemsets in F, i.e., which transactions contain the itemset

  uint [[2]] F_new; // new frequent itemsets based on existing ones in F
  pd_a3p uint [[2]] F_newcache (0, dbRows); // cached column data for newly generated frequent itemsets

  uint [[1]] C; // new candidate itemset
  pd_a3p uint [[1]] C_dot (dbRows); // column data (dot product) for the new candidate itemset C

  // compute the itemsets of size 1
  for (uint i = 0; i < dbColumns; i=i+1)
  {
    pd_a3p uint [[1]] z = db[:, i]; // all transactions where an item i occurs
    pd_a3p uint frequence = sum (z); // frequency of item i
    if (declassify (frequence >= classify(threshold))) {
      F = cat (F, reshape(i, 1, 1));
      F_cache = cat (F_cache, reshape (z, 1, dbRows));
    }
  }
  
  frequent.items = F;
  frequents = cat(frequents,{frequent});
  
  // until we find itemsets with length setSize
  for (uint k = 1; k < setSize; k=k+1)
  //x //@ invariant shape(F)[1] == k;
  {
    F_new = reshape ({}, 0, k + 1); // empty?
    F_newcache = reshape ({}, 0, dbRows); // empty?
    uint F_size = shape(F)[0]; // number of items for k-1
    for (uint i = 0; i < F_size; i=i+1) // for each itemset in F
    {
      for (uint j = i + 1; j < F_size; j=j+1) // for each other itemset in F
      {
        // check if the two itemsets have the same prefix (this is always true for singleton itemsets)
        bool prefixEqual = true;
        for (uint n = 0; n < k - 1; n=n+1)
        {
          if (F[i, n] != F[j, n]) {
            prefixEqual = false;
          }
        }
        //itemsets are ordered by item, hence the comparison in the test
        if (prefixEqual && F[i, k-1] < F[j, k-1]) {
          pd_a3p uint [[1]] C_dot = F_cache[i, :] * F_cache[j, :]; //join the two caches
          pd_a3p uint frequence = sum (C_dot); // compute the joint frequency
          if (declassify (frequence >= classify(threshold))) {
            F_newcache = cat (F_newcache, reshape(C_dot, 1, size(C_dot)));
            // create the new itemset by appending the last element of the second itemset to the first
            C = cat (F[i, :], F[j, k-1:k]);
            F_new = cat (F_new, reshape(C, 1, k+1));
          }
        }
      }
    }
    
    F = F_new;
    F_cache = F_newcache;
    
    frequent.items = F_new;
    frequents = cat(frequents,{frequent});
  }

  return frequents;
}


void main () {
    pd_a3p uint [[2]] db = load_db ();
    itemset [[1]] itemsets = apriori (db, 1 :: uint, 3 :: uint);
    print (itemsets);
}

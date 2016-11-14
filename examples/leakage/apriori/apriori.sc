
module apriori;

import stdlib;

kind shared3p;
domain pd_a3p shared3p;

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
  uint dbColumns = shape(db)[1]; 
  uint dbRows = shape(db)[0];

  itemset[[1]] frequents;
  itemset frequent;

  uint[[2]] F (0,1); 
  pd_a3p uint [[2]] F_cache (0, dbRows); 

  uint [[2]] F_new; 
  pd_a3p uint [[2]] F_newcache (0, dbRows);

  uint [[1]] C;
  pd_a3p uint [[1]] C_dot (dbRows);

  for (uint i = 0; i < dbColumns; i=i+1)
  {
    pd_a3p uint [[1]] z = db[:, i]; 
    pd_a3p uint frequence = sum (z); 
    if (declassify (frequence >= classify(threshold))) {
      F = cat (F, reshape(i, 1, 1));
      F_cache = cat (F_cache, reshape (z, 1, dbRows));
    }
  }
  
  frequent.items = F;
  frequents = cat(frequents,{frequent});
  
  for (uint k = 1; k < setSize; k=k+1)
  {
    F_new = reshape ({}, 0, k + 1); 
    F_newcache = reshape ({}, 0, dbRows); 
    uint F_size = shape(F)[0];
    for (uint i = 0; i < F_size; i=i+1)
    {
      for (uint j = i + 1; j < F_size; j=j+1)
      {
        bool prefixEqual = true;
        for (uint n = 0; n < k - 1; n=n+1)
        {
          if (F[i, n] != F[j, n]) {
            prefixEqual = false;
          }
        }
        if (prefixEqual && F[i, k-1] < F[j, k-1]) {
          pd_a3p uint [[1]] C_dot = F_cache[i, :] * F_cache[j, :];
          pd_a3p uint frequence = sum (C_dot);
          if (declassify (frequence >= classify(threshold))) {
            F_newcache = cat (F_newcache, reshape(C_dot, 1, size(C_dot)));
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
    for (uint i = 0; i < size(itemsets); i++)
        printArray (itemsets[i]);
}

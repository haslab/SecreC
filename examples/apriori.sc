#OPTIONS_SECREC --implicitcoercions=offc --backtrack=noneb --matching=gorderedm --promote=nop --verify=funcv --entrypoints="apriori"

module apriori;

//import stdlib;
//import shared3p;
import axioms;

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

//@ function bool IsDB (pd_a3p uint[[2]] db)
//@ noinline;
//@ {
//@     forall pd_a3p uint x; assertion<pd_a3p>(in(x,db) ==> x <= classify(1))
//@ }

pd_a3p uint [[2]] load_db ()
//@ ensures IsDB(\result);
{
    pd_a3p uint [[2]] db = reshape(classify({}),5,5);
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

struct frequent {
    uint [[2]] items;
    pd_a3p uint [[2]] cache;
}

//@ function bool IsItemSet (uint[[1]] is, uint sz)
//@ noinline;
//@ {
//@    size(is) > 0
//@    && (forall uint k; k < size(is) ==> is[k] < sz)
//@    && (forall uint i, uint j; i < j && j < size(is) ==> is[i] < is[j])
//@ }

//@ axiom<> (uint i, uint sz)
//@ requires i < sz;
//@ ensures IsItemSet({i},sz);

//@ function bool IsItemSetOf (uint[[1]] is, pd_a3p uint[[2]] db)
//@ requires IsDB(db);
//@ { IsItemSet(is,shape(db)[1]) }

//@ function pd_a3p uint[[1]] transactions (uint[[1]] is, pd_a3p uint[[2]] db)
//@ noinline;
//@ requires IsDB(db);
//@ requires IsItemSetOf(is,db);
//@ ensures size(\result) == shape(db)[0];
//@ { (size(is) == 1) ? db[:,is[0]] : db[:,is[0]] * transactions(is[1:],db) }

//@ function pd_a3p uint frequency (uint[[1]] is, pd_a3p uint[[2]] db)
//@ noinline;
//@ requires IsDB(db);
//@ requires IsItemSetOf(is,db);
//@ { sum(transactions(is,db)) }

//@ leakage function bool LeakFrequents (pd_a3p uint[[2]] db, uint threshold)
//@ noinline;
//@ requires IsDB(db);
//@ { forall uint[[1]] is; IsItemSetOf(is,db) ==> public (frequency(is,db) >= classify(threshold)) }

//@ function bool FrequentsCache(frequent f, pd_a3p uint[[2]] db, uint threshold)
//@ noinline;
//@ requires IsDB(db);
//@ {
//@     shape(f.items)[0] == shape(f.cache)[0]
//@     &&
//@     shape(f.cache)[1] == shape(db)[0]
//@     &&
//@     (forall uint i; i < shape(f.items)[0]
//@            ==> IsItemSetOf(f.items[i,:],db)
//@            &&  declassify(frequency(f.items[i,:],db)::pd_a3p uint) >= threshold
//@            &&  declassify(f.cache[i,:] == transactions(f.items[i,:],db)))
//@ }

frequent AddFrequent(frequent f, uint[[1]] C, pd_a3p uint[[1]] C_dot, pd_a3p uint [[2]] db, uint threshold)
//@ requires IsDB(db);
//@ requires IsItemSetOf(C,db);
//@ requires shape(f.items)[1] == size(C);
//@ requires shape(f.cache)[1] == size(C_dot);
//@ ensures shape(\result.items)[1] == size(C);
//@ ensures shape(\result.cache)[1] == size(C_dot);
//@ requires assertion<pd_a3p>(C_dot == transactions(C,db) :: pd_a3p bool);
//@ leakage requires LeakFrequents(db,threshold);
//@ requires FrequentsCache(f,db,threshold);
//@ ensures FrequentsCache(\result,db,threshold);
{
    pd_a3p uint frequence = sum (C_dot);
    if (declassify (frequence >= classify(threshold))) {
      f.items = snoc (f.items,C);
      f.cache = snoc (f.cache,C_dot);  
    }
    return f;
}

frequent apriori_1 (pd_a3p uint [[2]] db, uint threshold)
//@ requires IsDB(db);
//@ leakage requires LeakFrequents(db,threshold);
//@ ensures shape(\result.items)[1] == 1;
//@ ensures FrequentsCache(\result,db,threshold);
{
    frequent f;
    f.items = reshape({},0,1);
    f.cache = reshape(classify({}),0,shape(db)[0]);

    // compute the itemsets of size 1
    for (uint i = 0; i < shape(db)[1]; i=i+1)
    //@ invariant i <= shape(db)[1];
    //@ invariant shape(f.items)[0] <= i;
    //@ invariant shape(f.items)[1] == 1;
    //@ invariant FrequentsCache(f,db,threshold);
    {
      //@ assert size({i}) == 1;
      //@ assert assertion(db[:,i] == transactions({i},db) :: pd_a3p bool);
      AddFrequent(f,{i},db[:,i],db,threshold);
    }
    return f;
}

//x //@ lemma SameItemTransactions(uint i, pd_a3p uint[[2]] db)
//x //@ requires IsDB(db);
//x //@ requires i < shape(db)[1];
//x //@ ensures db[:,i] * db[:,i] == db[:,i];
//x //@ {}

//x //@ lemma SameTransactions(uint[[1]] xs, uint[[1]] ys, pd_a3p uint[[2]] db)
//x //@ requires set(xs) == set(ys);
//x //@ ensures transactions(xs,db) == transactions(ys,db);

//x //@ lemma MultiplyCaches(uint[[1]] C, uint[[1]] xs, uint[[1]] ys, pd_a3p uint[[2]] db)
//x //@ requires IsDB(db);
//x //@ requires IsItemSetOf(C,db);
//x //@ requires IsItemSetOf(xs,db);
//x //@ requires IsItemSetOf(ys,db);
//x //@ requires set(C) == set(xs) + set(ys);
//x //@ ensures assertion<pd_a3p>(transactions(C,db) == transactions(xs,db) * transactions(ys,db));

//@ lemma JoinCaches(uint[[2]] F,uint i, uint j, pd_a3p uint[[2]] db)
//@ requires init(F[i,:]) == init(F[j,:]);
//@ ensures assertion(transactions(snoc(F[i,:],last(F[j,:])),db) == transactions(F[i,:],db) * transactions(F[j,:],db) :: pd_a3p bool);


//x //@ assert transactions(prev.items[i,:]) == transactions(init(prev.items[i,:])) * transaction(last(prev.items[i,:]));
//x //@ assert transactions(prev.items[j,:]) == transactions(init(prev.items[j,:])) * transaction(last(prev.items[j,:]));
//x //@ assert transactions(C) == transactions(prev.items[i,:]) * transaction(last(prev.items[j,:]));

frequent apriori_k (pd_a3p uint [[2]] db, uint threshold, frequent prev,uint k)
//@ requires IsDB(db);
//@ requires k >= 1;
//@ requires shape(prev.items)[1] == k;
//@ leakage requires LeakFrequents(db,threshold);
//@ ensures shape(\result.items)[1] == k + 1;
//@ requires FrequentsCache(prev,db,threshold);
//@ ensures FrequentsCache(\result,db,threshold);
{
    frequent next;
    next.items = reshape({},0,k+1);
    next.cache = reshape(classify({}),0,shape(db)[0]);
    uint prev_F_size = shape(prev.items)[0]; // number of items for k-1
    for (uint i = 0; i < prev_F_size; i=i+1) // for each itemset in F
    //@ invariant i <= prev_F_size;
    //@ invariant shape(next.items)[1] == k+1;
    //@ invariant FrequentsCache(next,db,threshold);
    {
      for (uint j = i + 1; j < prev_F_size; j=j+1) // for each other itemset in F
      //@ invariant i < j && j <= prev_F_size;
      //@ invariant shape(next.items)[1] == k+1;
      //@ invariant FrequentsCache(next,db,threshold);
      {
        // check if the two itemsets have the same prefix (this is always true for singleton itemsets)
        bool prefixEqual = true;
        for (uint n = 0; n < k - 1; n=n+1)
        //@ invariant n < k;
        //@ invariant prefixEqual == forall uint m; m < n ==> prev.items[i,m] == prev.items[j,m];
        {
          if (prev.items[i, n] != prev.items[j, n]) {
            prefixEqual = false;
          }
        }
        //@ assert (prev.items[i,;k-1] == prev.items[i,:k-1] :: bool);
        if (prefixEqual && prev.items[i, k-1] < prev.items[j, k-1])
        {
          // new candidate itemset
          // create the new itemset by appending the last element of the second itemset to the first
          //@ assert IsItemSetOf(prev.items[i,:],db);
          //@ assert IsItemSetOf(prev.items[j,:],db);
          //@ assert prev.items[j,:][k-1] == prev.items[j,k-1];
          //@ assert prev.items[j,k-1] < shape(db)[1];
          uint[[1]] C = snoc (prev.items[i, :], prev.items[j, k-1]);
          //@ assert last(prev.items[i,:]) < prev.items[j,k-1];
          //@ assert IsItemSetOf(C,db);
          //join the two caches
          // column data (dot product) for the new candidate itemset C
          pd_a3p uint [[1]] C_dot = prev.cache[i, :] * prev.cache[j, :];
          //x //@ assert forall uint q; q < k-1 ==> (C[q] == prev.items[i,q] && C[q] == prev.items[j,q]);
          //x //@ assert C[k-1] == prev.items[i,k-1];
          //x //@ assert C[k] == prev.items[j,k-1];
          //x //@ assert set(prev.items[i,:]) == set(prev.items[i,:][:k-1]) + set{prev.items[i,k-1]};
          //x //@ assert set(prev.items[j,:]) == set(prev.items[j,:][:k-1]) + set{prev.items[j,k-1]};
          //x //@ assert set(C) == (set uint i ; i < size(C) ; C[i]);
          //x //@ assert forall uint x; in(x,prev.items[i,:]) ==> in(x,C);
          //x //@ assert forall uint q; q < k-1 ==> C[q] == prev.items[j,:k-1][q];
          //x //@ assert forall uint x; x < k-1 ==> in(prev.items[i,x],C);
          //x //@ assert in(prev.items[j,k-1],C);
          //x //@ assert forall uint x; in(x,prev.items[i,:]) ==> in(x,C);
          //x //@ assert forall uint x; in(x,C) ==> in(x,prev.items[i,:]) || in (x,prev.items[j,:]);
          //x //@ assert assertion<pd_a3p>(C_dot == transactions(prev.items[i,:],db) * transactions(prev.items[j,:],db) :: pd_a3p bool);
          //x //@ assert prev.items[j,:] == snoc(prev.items[j,:k-1],prev.items[j,k-1]);
          //x //@ assert forall uint x; in(x,prev.items[j,:k-1]) ==> in(x,C);
          //x //@ assert forall uint x; in(x,prev.items[j,:]) ==> in(x,C);
          //x //@ assume set(C) == set(prev.items[i,:]) + set (prev.items[j,:]);
          //x //@ MultiplyCaches(C,prev.items[i,:],prev.items[j,:],db);
          
          //@ JoinCaches(prev.items,i,j,db);
          AddFrequent(next,C,C_dot,db,threshold);
          
        }
      }
    }
    return next;
}

// database rows = transaction no, database column = item no
// result = one itemset per row
uint[[2]] apriori (pd_a3p uint [[2]] db, uint threshold, uint setSize)
//@ requires IsDB(db);
//@ requires setSize > 0;
//@ leakage requires LeakFrequents(db,threshold);
{
  frequent freq = apriori_1(db,threshold);
  
  // until we find itemsets with length setSize
  for (uint k = 1; k < setSize; k=k+1)
  //@ invariant 1 <= k && k <= setSize;
  //@ invariant shape(freq.items)[1] == k;
  //@ invariant FrequentsCache(freq,db,threshold);
  {
      freq = apriori_k(db,threshold,freq,k);
  }

  return freq.items;
}


void main () {
    pd_a3p uint [[2]] db = load_db ();
    uint [[2]] itemsets = apriori (db, 1 :: uint, 3 :: uint);
    printArray (itemsets);
}

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

pd_a3p uint [[2]] load_db () {
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

//@ function bool IsItemSetOf (uint[[1]] is, pd_a3p uint[[2]] db)
//@ { IsItemSet(is,shape(db)[1]) }

//x //@ function bool hasItemsOf (uint[[2]] F, pd_a3p uint[[2]] db)
//x //@ noinline;
//x //@ { (forall uint i, uint j; i < shape(F)[0] && j < shape(F)[1] ==> F[i,j] < shape(db)[1]) }

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

//@ function bool LtItems (uint[[1]] xs, uint[[1]] ys)
//@ noinline;
//@ {
//@     size(ys) == 0 ? false : size(xs) == 0 ? true : (xs[0] < ys[0] ? true : (xs[0] == ys[0] && size(xs) > 1) ? LtItems(xs[1:],ys[1:]) : false)
//@ }

//x //@ function bool LeItems (uint[[1]] xs, uint[[1]] ys)
//x //@ requires size(xs) == size(ys);
//x //@ { xs == ys || LtItems(xs,ys) }

//@ function bool SortedItems(uint[[2]] iss)
//@ {
//@     forall uint i, uint j; i < j && j < shape(iss)[0] ==> LtItems(iss[i,:],iss[j,:])
//@ }

//@ function bool FrequentsCache(frequent f, pd_a3p uint[[2]] db, uint threshold)
//@ noinline;
//@ {
//@     shape(f.items)[0] == shape(f.cache)[0]
//@     &&
//@     shape(f.cache)[1] == shape(db)[0]
//@     &&
//@     (forall uint i; i < shape(f.items)[0]
//@            ==> IsItemSetOf(f.items[i,:],db)
//@            &&  declassify(frequency(f.items[i,:],db)::pd_a3p uint) >= threshold
//@            &&  declassify(f.cache[i,:] == transactions(f.items[i,:],db)))
//@     &&
//@     SortedItems(f.items)
//@ }

//@ function bool AllFrequentsUpTo(uint[[2]] F, pd_a3p uint[[2]] db, uint threshold, uint[[1]] is)
//@ noinline;
//@ requires IsItemSetOf(is,db);
//@ {
//@     forall uint[[1]] js; IsItemSetOf(js,db) && LtItems(js,is) && declassify(frequency(js,db)) >= threshold ==> in(js,set(F))
//@ }

//@ function bool AllFrequents(uint[[2]] F, pd_a3p uint[[2]] db, uint threshold)
//@ noinline;
//@ {
//@     forall uint[[1]] js; IsItemSetOf(js,db) && size(js) == shape(F)[1] && declassify(frequency(js,db)) >= threshold ==> in(js,set(F))
//@ }

//@ function uint[[1]] nextSet (uint[[1]] xs)
//@ requires size(xs) > 0;
//@ {
//@     snoc(xs[:size(xs)-1],xs[size(xs)-1]+1)
//@ }

//@ function uint[[1]] candidate (uint[[2]] F, uint i, uint j, pd_a3p uint[[2]] db)
//@ requires i <= j && j <= shape(F)[0];
//@ {
//@     i == shape(F)[0] ? repeat(shape(db)[1],shape(F)[1]) : j == shape(F)[0] ? snoc(F[i,:],shape(db)[1]) : snoc(F[i,:],F[j,shape(F)[1]-1])
//@ }

frequent AddFrequent(frequent f, uint[[1]] C, pd_a3p uint[[1]] C_dot, pd_a3p uint [[2]] db, uint threshold)
//@ requires IsItemSetOf(C,db);
//@ requires shape(f.items)[1] == size(C);
//@ requires assertion<pd_a3p>(C_dot == transactions(C,db) :: pd_a3p bool);
//@ leakage requires LeakFrequents(db,threshold);
//@ requires FrequentsCache(f,db,threshold);
//@ ensures FrequentsCache(\result,db,threshold);
//@ requires AllFrequentsUpTo(f.items,db,threshold,C);
//@ ensures AllFrequentsUpTo(\result.items,db,threshold,nextSet(C));
{
    pd_a3p uint frequence = sum (C_dot);
    if (declassify (frequence >= classify(threshold))) {
      f.items = snoc (f.items,C);
      f.cache = snoc (f.cache,C_dot);  
    }
    return f;
}

frequent apriori_1 (pd_a3p uint [[2]] db, uint threshold)
//@ leakage requires LeakFrequents(db,threshold);
//@ ensures shape(\result.items)[1] == 1;
//@ ensures FrequentsCache(\result,db,threshold);
//@ ensures AllFrequents(\result.items,db,threshold);
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
    //@ invariant AllFrequentsUpTo(f.items,db,threshold,{i});
    {
      //@ assert i < shape(db)[1];
      //@ forall uint k; k < 1 ==> {i}[0] < shape(db)[1]
      AddFrequent(f,{i},db[:,i],db,threshold);
    }
    return f;
}

frequent apriori_k (pd_a3p uint [[2]] db, uint threshold, frequent prev,uint k)
//@ requires k >= 1;
//@ requires shape(prev.items)[1] == k;
//@ leakage requires LeakFrequents(db,threshold);
//@ ensures shape(\result.items)[1] == k + 1;
//@ requires FrequentsCache(prev,db,threshold);
//@ ensures FrequentsCache(\result,db,threshold);
//x //@ requires AllFrequents(prev.items,db,threshold);
//x //@ ensures AllFrequents(\result.items,db,threshold);
{
    frequent next;
    next.items = reshape({},0,k+1);
    next.cache = reshape(classify({}),0,shape(db)[0]);
    uint prev_F_size = shape(prev.items)[0]; // number of items for k-1
    for (uint i = 0; i < prev_F_size; i=i+1) // for each itemset in F
    //@ invariant i <= prev_F_size;
    //@ invariant shape(next.items)[1] == k+1;
    //@ invariant FrequentsCache(next,db,threshold);
    //x //@ invariant AllFrequentsUpTo(next,db,threshold,candidate(prev.items,i,i));
    {
      for (uint j = i + 1; j < prev_F_size; j=j+1) // for each other itemset in F
      //@ invariant i < j && j <= prev_F_size;
      //@ invariant shape(next.items)[1] == k+1;
      //@ invariant FrequentsCache(next,db,threshold);
      //x //@ invariant AllFrequentsUpTo(next,db,threshold,candidate(prev.items,i,j));
      {
        // check if the two itemsets have the same prefix (this is always true for singleton itemsets)
        bool prefixEqual = true;
        for (uint n = 0; n < k - 1; n=n+1)
        {
          if (prev.items[i, n] != prev.items[j, n]) {
            prefixEqual = false;
          }
        }
        if (prefixEqual)
        {
          // new candidate itemset
          // create the new itemset by appending the last element of the second itemset to the first
          //@ assert IsItemSetOf(prev.items[i,:],db);
          //@ assert IsItemSetOf(prev.items[j,:],db);
          //@ assert prev.items[j,:][k-1] == prev.items[j,k-1];
          //@ assert prev.items[j,k-1] < shape(db)[1];
          uint[[1]] C = snoc (prev.items[i, :], prev.items[j, k-1]);
          //@ assert IsItemSetOf(C,db);
          //join the two caches
          // column data (dot product) for the new candidate itemset C
          pd_a3p uint [[1]] C_dot = prev.cache[i, :] * prev.cache[j, :];
          //x //@ MultiplyCaches(C,C_dot,prev,i,j);
          
          //x AddFrequent(next,C,C_dot,db,threshold);
          
        }
      }
    }
    return next;
}

// database rows = transaction no, database column = item no
// result = one itemset per row
uint[[2]] apriori (pd_a3p uint [[2]] db, uint threshold, uint setSize)
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

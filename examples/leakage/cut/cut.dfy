
// Leakage annotations
predicate PublicIn<T> (x: T)
predicate PublicOut<T> (x: T)
predicate PublicMid<T> (x: T)
predicate DeclassifiedIn<T> (x: T)    
predicate DeclassifiedOut<T> (x: T)
predicate Leak<T> (x: T)

// Shuffled sequence post-condition
predicate IsShuffleLeakage<T>(xsPrivate: seq<T>,rPrivate: seq<T>) {
    (multiset(xsPrivate) == multiset(rPrivate))
    &&
    (Leak(multiset(xsPrivate)) ==> Leak(rPrivate))
}

lemma MSetSize<T> (xs: seq<T>)
ensures |xs| == |multiset(xs)|;

// Shuffles two arrays together (i.e., using the same random permutation for both)
method ShufflePair (xs: seq<int>, ys: seq<bool>) returns (xsS: seq<int>, ysS: seq<bool>)
requires |xs| == |ys|;
ensures IsShuffleLeakage(xs,xsS);
ensures IsShuffleLeakage(ys,ysS);

//missing proof for this lemma
lemma LeakMSeqBool (xs: multiset<bool>)
requires Leak(|xs|);
requires Leak(xs[true]);
ensures Leak(xs);

method Cut (a: seq<int>, m: seq<bool>) returns (x: seq<int>)
requires |a| == |m|;
requires PublicIn(|a|);
requires PublicIn(|m|);
requires Leak(multiset(m)[true]);
ensures PublicOut(|x|);
{
  var aS: seq<int>;
  var mS: seq<bool>;
  aS,mS := ShufflePair(a,m);
  MSetSize(a);
  MSetSize(m);
  LeakMSeqBool(multiset(m));
  assert(DeclassifiedIn(mS));
  x := [];
  var i: int := 0;
  while (i < |mS|)
  invariant DeclassifiedIn(i)
  invariant DeclassifiedIn(|x|)
  invariant DeclassifiedIn(i < |mS|)
  {
    if mS[i] { x := x + [aS[i]]; }
    i := i + 1; 
  }
  return x;
}



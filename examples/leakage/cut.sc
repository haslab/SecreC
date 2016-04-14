D T[[1]] cut (D T[[1]] a, D bool[[1]] m) {
    
}

//predicate PublicIn<T> (x: T)
//predicate PublicOut<T> (x: T)
//predicate PublicMid<T> (x: T)
//predicate DeclassifiedIn<T> (x: T)    
//predicate DeclassifiedOut<T> (x: T)
//predicate Leak<T> (x: T)
//
//predicate SameElems<T> (xs: seq<T>, ys: seq<T>) {
//  |xs| == |ys|
//  &&
//  (forall i :: 0 <= i < |xs| ==> xs[i] in ys) 
//  &&
//  (forall i :: 0 <= i < |ys| ==> ys[i] in xs)
//}
//
//predicate LeakEqualities_Leakage (xs: seq<int>) {
//    forall i,j :: 0 <= i < |xs| && 0 <= j < |xs| ==> Leak(xs[i] == xs[j])
//}
//
//predicate LeakComparisons_Leakage (xs: seq<int>) {
//    forall i,j :: 0 <= i < |xs| && 0 <= j < |xs| ==> Leak(xs[i] <= xs[j])
//}
//
//method ShufflePair (xs: seq<int>, ys: seq<bool>) returns (xs': seq<int>, ys': seq<bool>)
//requires |xs| == |ys|;
//ensures SameElems(xs,xs');
//ensures SameElems(ys,ys');
//ensures LeakEqualities_Leakage(xs') ==> LeakComparisons_Leakage(xs');
//
//method Cut (a: seq<int>, m: seq<bool>) returns (x: seq<int>)
//requires PublicIn(|a|);
//requires PublicIn(|m|);
//requires Leak(multiset(m)[true])
//ensures PublicOut(|x|);
//{
//  var a': seq<int>;
//  var m': seq<bool>;
//  a',m' := ShufflePair(a,m);
//  assert(DeclassifiedIn(m'));
//  x := [];
//  var i: int := 0;
//  while (i < |m'|)
//  {
//    if m'[i] { x := x + [a'[i]]; } 
//  }
//  return x;
//}
//


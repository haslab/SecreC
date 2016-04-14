
newtype uint8 = x: int | 0 <= x <= 255
newtype uint16 = x: int | 0 <= x <= 65535
newtype uint32 = x: int | 0 <= x <= 4294967295
newtype uint64 = x: int | IsUint64(x)
predicate IsUint64 (x: int) { 0 <= x <= 18446744073709551615 }
newtype xor_uint8 = x: int | 0 <= x <= 255
newtype xor_uint16 = x: int | 0 <= x <= 65535
newtype xor_uint32 = x: int | 0 <= x <= 4294967295
newtype xor_uint64 = x: int | 0 <= x <= 18446744073709551615
newtype int8 = x: int | -128 <= x <= 127
newtype int16 = x: int | -32768 <= x <= 32767
newtype int32 = x: int | -2147483648 <= x <= 2147483647        
newtype int64 = x: int | -9223372036854775808 <= x <= 9223372036854775807
newtype float32 = x: real | true
newtype float64 = x: real | true
    
predicate PublicIn<T> (x: T)
predicate PublicOut<T> (x: T)
predicate PublicMid<T> (x: T)
predicate DeclassifiedIn<T> (x: T)    
predicate DeclassifiedOut<T> (x: T)
predicate Leak<T> (x: T)


method Shuffle (xs: seq<int>) returns (r: seq<int>)
ensures |xs| == |r|;
ensures multiset(xs) == multiset(r);
ensures Distinct(xs) ==> ComparisonsLeakage(r);

predicate ComparisonLeakage (xsPrivate: seq<int>,xPrivate: int) {
    forall i :: 0 <= i < |xsPrivate| ==> Leak(xsPrivate[i] <= xPrivate)
}

predicate ComparisonsLeakage (xsPrivate: seq<int>) {
    forall i,j :: 0 <= i < |xsPrivate| && 0 <= j < |xsPrivate| ==> Leak(xsPrivate[i] <= xsPrivate[j])
}

predicate Distinct (xs: seq<int>) {
    forall i,j :: 0 <= i < |xs| && 0 <= j < |xs| && i != j ==> xs[i] != xs[j]
}

//missing proof
lemma ComparisonsMSubSet(xs: seq<int>, ys: seq<int>)
requires PublicIn(|xs|);
requires PublicIn(|ys|);
requires multiset(xs) <= multiset(ys);
requires ComparisonsLeakage(ys);
ensures ComparisonsLeakage(xs);

method Partition (xs: seq<int>, p: int) returns (ls: seq<int>,rs: seq<int>)
requires PublicIn(|xs|);
requires ComparisonLeakage(xs,p);
ensures PublicOut(|ls|);
ensures PublicOut(|rs|);
ensures |xs| == |ls| + |rs|;
ensures multiset(xs) == multiset(ls) + multiset(rs);
{
    var i: int := 0;
    var cmp: bool;
    ls := [];
    rs := [];
    
    while (true)
    decreases |xs| - i
    invariant DeclassifiedIn(i);
    invariant 0 <= i <= |xs|;
    invariant DeclassifiedIn(|ls|);
    invariant DeclassifiedIn(|rs|);
    invariant |xs[0..i]| == |ls| + |rs|;
    invariant multiset(xs[0..i]) == multiset(ls) + multiset(rs);
    {
        cmp := i < |xs|;
        assert(DeclassifiedIn(cmp));
        if (!cmp) {break;}
        var y: int := xs[i];
        var cmp2: bool := y <= p;
        assert(DeclassifiedIn(cmp2));
        if (cmp2) {
          ls := ls + [y];
        }
        else {
          rs := rs + [y];
        }
        assert(xs[0..i+1] == xs[0..i] + [y]);
        i := i + 1;
    }
    assert(xs[0..i] == xs);
    return ls,rs;
}

method LeakySort (xs: seq<int>) returns (r: seq<int>)
decreases |xs|
requires PublicIn(|xs|);
requires ComparisonsLeakage(xs);
ensures PublicOut(|r|);
ensures |xs| == |r|;
ensures multiset(xs) == multiset(r);
{
    assert(DeclassifiedIn(|xs| <= 1));
    if (|xs| <= 1) { return xs; }
    
    assert(xs == [xs[0]] + xs[1..]);
    
    var pivot: int := xs[0];
    var r_ls,r_rs: seq<int> := Partition(xs[1..],pivot);
    ComparisonsMSubSet(r_ls,xs);
    ComparisonsMSubSet(r_rs,xs);
    var ls: seq<int> := LeakySort(r_ls);
    var rs: seq<int> := LeakySort(r_rs);
    var ls_pivot: seq<int> := ls + [pivot];
    return ls_pivot + rs;
}
    
method Sort (xs: seq<int>) returns (r: seq<int>)
requires PublicIn(|xs|);
requires Distinct(xs);
ensures PublicOut(|r|);
ensures |xs| == |r|;
ensures multiset(xs) == multiset(r);
{
    var xsS: seq<int> := Shuffle(xs);
    r := LeakySort(xsS);
    return r;
}






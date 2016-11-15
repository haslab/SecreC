// Leakage annotations
predicate PublicIn<T> (x: T)
predicate PublicOut<T> (x: T)
predicate PublicMid<T> (x: T)
predicate DeclassifiedIn<T> (x: T)    
predicate DeclassifiedOut<T> (x: T)
predicate Leak<T> (x: T)
    
//newtype uint8 = x: int | 0 <= x <= 255
//newtype uint16 = x: int | 0 <= x <= 65535
//newtype uint32 = x: int | 0 <= x <= 4294967295
//newtype uint64 = x: int | IsUint64(x)
//predicate IsUint64 (x: int) { 0 <= x <= 18446744073709551615 }
//newtype xor_uint8 = x: int | 0 <= x <= 255
//newtype xor_uint16 = x: int | 0 <= x <= 65535
//newtype xor_uint32 = x: int | 0 <= x <= 4294967295
//newtype xor_uint64 = x: int | 0 <= x <= 18446744073709551615
//newtype int8 = x: int | -128 <= x <= 127
//newtype int16 = x: int | -32768 <= x <= 32767
//newtype int32 = x: int | -2147483648 <= x <= 2147483647        
//newtype int64 = x: int | -9223372036854775808 <= x <= 9223372036854775807
//newtype float32 = x: real | true
//newtype float64 = x: real | true
    
newtype uint8 = x: int | 0 <= x
newtype uint16 = x: int | 0 <= x
newtype uint32 = x: int | 0 <= x
newtype uint64 = x: int | 0 <= x
newtype xor_uint8 = x: int | 0 <= x
newtype xor_uint16 = x: int | 0 <= x
newtype xor_uint32 = x: int | 0 <= x
newtype xor_uint64 = x: int | 0 <= x
newtype int8 = x: int | true
newtype int16 = x: int | true
newtype int32 = x: int | true
newtype int64 = x: int | true
newtype float32 = x: real | true
newtype float64 = x: real | true

function method Repeat<T> (x: T, sz: uint64) : seq<T>
ensures |Repeat(x,sz)| as uint64 == sz;
ensures forall y:T :: y in Repeat(x,sz) ==> x == y;  
decreases sz;
{
  if sz == 0 then [] else [x] + Repeat(x,sz-1) 
}

function method sum_int(xs: seq<int>) : int
{
  if |xs| == 0
    then 0
    else xs[0] + sum_int(xs[1..])
}
function method sum_uint64(xs: seq<uint64>) : uint64
{
  if |xs| == 0
    then 0
    else xs[0] + sum_uint64(xs[1..])
}

function method mul_int(xs: seq<int>, ys: seq<int>) : seq<int>
requires |xs| == |ys|;
ensures |mul_int(xs,ys)| == |xs|;
ensures forall i: int :: 0 <= i < |mul_int(xs,ys)| ==> mul_int(xs,ys)[i] == xs[i] * ys[i]; 
{
  if |xs| == 0
    then []
    else [xs[0] * ys[0]] + mul_int(xs[1..],ys[1..])
}

function method mul_uint64(xs: seq<uint64>, ys: seq<uint64>) : seq<uint64>
requires |xs| == |ys|;
ensures |mul_uint64(xs,ys)| == |xs|;
ensures forall i: int :: 0 <= i < |mul_uint64(xs,ys)| ==> mul_uint64(xs,ys)[i] == xs[i] * ys[i]; 
{
  if |xs| == 0
    then []
    else [xs[0] * ys[0]] + mul_uint64(xs[1..],ys[1..])
}

class Array2<T> {
  var arr2 : array2<T>;
  
  function valid() : bool
  reads this`arr2;
  { this.arr2 != null }

  constructor(x: int,y: int)
  requires x >= 0;
  requires y >= 0;
  ensures this != null && this.valid();
  modifies this`arr2;
  { this.arr2 := new T[x,y]; }

  constructor reshape0(x: T, m: int, n: int)
  requires m * n == 1;
  free ensures this != null && this.valid();
  free ensures this.arr2.Length0 == 1 && this.arr2.Length1 == 1;
  free ensures this.arr2[0,0] == x; 
  {}
  
  constructor reshape1(xs: seq<T>, m: int, n: int)
  requires m >= 0 && n >= 0;
  requires |xs| == m * n;
  free ensures this != null && this.valid();
  free ensures this.arr2.Length0 == m && this.arr2.Length1 == n;
  free ensures forall i: int, j: int :: (0 <= i < m && 0 <= j < n) ==> i+j < |xs| && this.arr2[i,j] == xs[i+j];
  {}

  function method Length0() : int
  reads this`arr2;
  requires this.arr2 != null && this.valid()
  { this.arr2.Length0 }
  
  function method Length1() : int
  reads this`arr2;
  requires this.arr2 != null && this.valid()
  { this.arr2.Length1 }

  function method size() : int
  reads this`arr2;
  requires this.arr2 != null && this.valid()
  { this.arr2.Length0 * this.arr2.Length1 }
  
  function method shape() : seq<int>
  reads this`arr2;
  requires this.arr2 != null && this.valid()
  { [this.arr2.Length0,this.arr2.Length1] }
  
  constructor cat0(xs: Array2<T>, ys: Array2<T>)
  requires xs != null && xs.valid();
  requires ys != null && ys.valid();
  requires xs.arr2.Length1 == ys.arr2.Length1;
  free ensures this != null && this.valid();
  free ensures this.arr2.Length1 == xs.arr2.Length1;
  free ensures this.arr2.Length0 == xs.arr2.Length0 + ys.arr2.Length0;
  free ensures forall i: int, j: int :: (0 <= i < xs.arr2.Length0 && 0 <= j < xs.arr2.Length1) ==> this.arr2[i,j] == xs.arr2[i,j];
  free ensures forall i: int, j: int :: (0 <= i < ys.arr2.Length0 && 0 <= j < ys.arr2.Length1) ==> this.arr2[i+xs.arr2.Length0,j] == ys.arr2[i,j];
  {}
  
  constructor cat1(xs: Array2<T>, ys: Array2<T>)
  requires xs != null && xs.valid();
  requires ys != null && ys.valid();
  requires xs.arr2.Length0 == ys.arr2.Length0;
  free ensures this != null && this.valid();
  free ensures this.arr2.Length0 == xs.arr2.Length0;
  free ensures this.arr2.Length1 == xs.arr2.Length1 + ys.arr2.Length1;
  free ensures forall i: int, j: int :: (0 <= i < xs.arr2.Length0 && 0 <= j < xs.arr2.Length1) ==> this.arr2[i,j] == xs.arr2[i,j];
  free ensures forall i: int, j: int :: (0 <= i < ys.arr2.Length0 && 0 <= j < ys.arr2.Length1) ==> this.arr2[i,j+xs.arr2.Length1] == ys.arr2[i,j];
  {}
      
  function method project00(x: int, y: int) : T
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= x < this.arr2.Length0;
  requires 0 <= y < this.arr2.Length1;
  { this.arr2[x,y] }
  
  function method project10(x1: int, x2: int, y: int) : seq<T>
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= x1 < this.arr2.Length0;
  requires 0 <= x2 < this.arr2.Length0;
  requires x1 <= x2;
  requires 0 <= y < this.arr2.Length1;
  ensures forall i:int :: 0 <= i < x2-x1 ==> project10(x1,x2,y)[i] == this.arr2[x1+i,y];
  
  function method project01(x: int, y1: int, y2: int) : seq<T>
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= x < this.arr2.Length0;
  requires 0 <= y1 < this.arr2.Length1;
  requires 0 <= y2 < this.arr2.Length1;
  requires y1 <= y2;
  ensures forall j:int :: 0 <= j < y2-y1 ==> project01(x,y1,y2)[j] == this.arr2[x,y1+j];
  
  function method project11(x1: int, x2: int, y1: int, y2: int) : Array2<T>
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= x1 < this.arr2.Length0;
  requires 0 <= x2 < this.arr2.Length0;
  requires x1 <= x2;
  requires 0 <= y1 < this.arr2.Length1;
  requires 0 <= y2 < this.arr2.Length1;
  requires y1 <= y2;
  ensures project11(x1,x2,y1,y2) != null && project11(x1,x2,y1,y2).valid();
  ensures project11(x1,x2,y1,y2).arr2.Length0 == x2-x1;
  ensures project11(x1,x2,y1,y2).arr2.Length1 == y2-y1;
  ensures forall i: int, j:int :: (0 <= i < x2-x1 && 0 <= j < y2-y1) ==> project11(x1,x2,y1,y2).arr2[i,j] == this.arr2[x1+i,y1+j];
}

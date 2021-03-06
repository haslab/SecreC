// Leakage annotations
predicate PublicIn<T> (x: T)
predicate PublicOut<T> (x: T)
predicate PublicMid<T> (x: T)
predicate DeclassifiedIn<T> (x: T)    
predicate DeclassifiedOut<T> (x: T)
predicate Leak<T> (x: T)
// used to mark leakage annotations, since Dafny does not allow attributes everywhere
function Leakage (x: bool) : bool
function LeakageOut (x: bool) : bool
function Free (x: bool) : bool
    
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

function method bool_to_uint8(b:bool) : uint8 { if b then 1 else 0 }
function method bool_to_uint16(b:bool) : uint16 { if b then 1 else 0 }
function method bool_to_uint32(b:bool) : uint32 { if b then 1 else 0 }
function method bool_to_uint64(b:bool) : uint64 { if b then 1 else 0 }
function method bool_to_float32(b:bool) : float32 { if b then 1.0 else 0.0 }
function method bool_to_float64(b:bool) : float64 { if b then 1.0 else 0.0 }

function method inv_float32(x : float32) : float32 { if x == 0.0 then 0.0 else 1.0 / x }
function method inv_float64(x : float64) : float64 { if x == 0.0 then 0.0 else 1.0 / x }

function method abs_uint8(x: uint8): uint8 { if x < 0 then -x else x }
function method abs_uint16(x: uint16): uint16 { if x < 0 then -x else x }
function method abs_uint32(x: uint32): uint32 { if x < 0 then -x else x }
function method abs_uint64(x: uint64): uint64 { if x < 0 then -x else x }
function method abs_float32(x: float32): float32 { if x < 0.0 then -x else x }
function method abs_float64(x: float64): float64 { if x < 0.0 then -x else x }

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
function method sum_float64(xs: seq<float64>) : float64
{
  if |xs| == 0
    then 0.0
    else xs[0] + sum_float64(xs[1..])
}

function method mul1_int(xs: seq<int>, ys: seq<int>) : seq<int>
requires |xs| == |ys|;
ensures |mul1_int(xs,ys)| == |xs|;
ensures forall i: int :: 0 <= i < |mul1_int(xs,ys)| ==> mul1_int(xs,ys)[i] == xs[i] * ys[i]; 
{
  if |xs| == 0
    then []
    else [xs[0] * ys[0]] + mul1_int(xs[1..],ys[1..])
}

function method mul1_uint64(xs: seq<uint64>, ys: seq<uint64>) : seq<uint64>
requires |xs| == |ys|;
ensures |mul1_uint64(xs,ys)| == |xs|;
ensures forall i: int :: 0 <= i < |mul1_uint64(xs,ys)| ==> mul1_uint64(xs,ys)[i] == xs[i] * ys[i]; 
{
  if |xs| == 0
    then []
    else [xs[0] * ys[0]] + mul1_uint64(xs[1..],ys[1..])
}

class Array2<T> {
  var arr2 : array2<T>;
  
  predicate valid()
  reads this`arr2;
  { this.arr2 != null }

  constructor(x: uint64,y: uint64)
  requires x >= 0;
  requires y >= 0;
  ensures this != null && this.valid();
  modifies this`arr2;
  ensures this.arr2.Length0 as uint64 == x;
  ensures this.arr2.Length1 as uint64 == y;
  { this.arr2 := new T[x,y]; }

  constructor reshape0(x: T, m: uint64, n: uint64)
  requires 0 <= m && 0 <= n;
  free ensures this != null && this.valid();
  free ensures this.Length0() == m && this.Length1() == n;
  free ensures forall i: uint64, j: uint64 :: (0 <= i < m && 0 <= j < n) ==> this.arr2[i,j] == x;
  {}
  
  constructor reshape1(xs: seq<T>, m: uint64, n: uint64)
  requires m >= 0 && n >= 0;
  requires |xs| as uint64 == m * n;
  free ensures this != null && this.valid();
  free ensures this.Length0() == m && this.Length1() == n;
  free ensures forall i: uint64, j: uint64 :: (0 <= i < m && 0 <= j < n) ==> (i+j < (|xs| as uint64) && this.arr2[i,j] == xs[i+j]);
  {}

  function method Length0() : uint64
  reads this`arr2;
  requires this.arr2 != null && this.valid();
  ensures this.Length0() == (this.arr2.Length0 as uint64);
  { (this.arr2.Length0 as uint64) }
  
  function method Length1() : uint64
  reads this`arr2;
  requires this.arr2 != null && this.valid();
  ensures this.Length1() == (this.arr2.Length1 as uint64);
  { (this.arr2.Length1 as uint64) }

  function method size() : uint64
  reads this`arr2;
  requires this.arr2 != null && this.valid()
  { this.Length0() * this.Length1() }
  
  function method shape() : seq<uint64>
  reads this`arr2;
  requires this.arr2 != null && this.valid()
  { [this.Length0(),this.Length1()] }
  
  predicate contains(x: T)
  requires this != null && this.valid();
  reads this`arr2;
  reads this.arr2;
  {
    exists i: int, j: int :: 0 <= i < this.arr2.Length0 && 0 <= j < this.arr2.Length1 ==> this.arr2[i,j] == x
  }
  
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
      
  function method project00(x: uint64, y: uint64) : T
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= x < this.Length0();
  requires 0 <= y < this.Length1();
  { this.arr2[x,y] }
  
  function method project10(x1: uint64, x2: uint64, y: uint64) : seq<T>
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= x1 <= this.Length0();
  requires 0 <= x2 <= this.Length0();
  requires x1 <= x2;
  requires 0 <= y < this.Length1();
  ensures (|this.project10(x1,x2,y)| as uint64) == x2-x1;
  ensures forall i:uint64 :: 0 <= i < x2-x1 ==> this.project10(x1,x2,y)[i] == this.arr2[x1+i,y];
  
  function method project01(x: uint64, y1: uint64, y2: uint64) : seq<T>
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= x < this.Length0();
  requires 0 <= y1 <= this.Length1();
  requires 0 <= y2 <= this.Length1();
  requires y1 <= y2;
  ensures (|this.project01(x,y1,y2)| as uint64) == y2-y1;
  ensures forall j:uint64 :: 0 <= j < y2-y1 ==> this.project01(x,y1,y2)[j] == this.arr2[x,y1+j];
  
  function method project11(x1: uint64, x2: uint64, y1: uint64, y2: uint64) : Array2<T>
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= x1 <= this.Length0();
  requires 0 <= x2 <= this.Length0();
  requires x1 <= x2;
  requires 0 <= y1 <= this.Length1();
  requires 0 <= y2 <= this.Length1();
  requires y1 <= y2;
  ensures this.project11(x1,x2,y1,y2) != null && this.project11(x1,x2,y1,y2).valid();
  ensures this.project11(x1,x2,y1,y2).Length0() == x2-x1;
  ensures this.project11(x1,x2,y1,y2).Length1() == y2-y1;
  ensures forall i: uint64, j:uint64 :: (0 <= i < x2-x1 && 0 <= j < y2-y1) ==> this.project11(x1,x2,y1,y2).arr2[i,j] == this.arr2[x1+i,y1+j];
  
  function method update00(i:uint64, j: uint64, v:T) : Array2<T>
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= i < this.Length0();
  requires 0 <= j < this.Length1();
  ensures this.update00(i,j,v) != null && this.update00(i,j,v).valid();
  ensures this.update00(i,j,v).Length0() == this.Length0();
  ensures this.update00(i,j,v).Length1() == this.Length1();
  ensures forall i1: uint64, j1: uint64 :: (0 <= i1 < this.Length0() && 0 <= j1 < this.Length1() && i1 != i && j1 != j) ==> this.update00(i,j,v).arr2[i1,j1] == this.arr2[i1,j1];
  ensures forall i1: uint64, j1: uint64 :: (0 <= i1 < this.Length0() && 0 <= j1 < this.Length1() && i1 == i && j1 == j) ==> this.update00(i,j,v).arr2[i1,j1] == v;
  
  function method update01(i:uint64, j1: uint64, j2: uint64, vs:seq<T>) : Array2<T>
  reads this`arr2, this.arr2;
  requires this.arr2 != null && this.valid();
  requires 0 <= i < this.Length0();
  requires 0 <= j1 < this.Length1();
  requires 0 <= j2 <= this.Length1();
  requires |vs| == j2 as int - j1 as int;
  requires j1 <= j2;
  ensures this.update01(i,j1,j2,vs) != null && this.update01(i,j1,j2,vs).valid();
  ensures this.update01(i,j1,j2,vs).Length0() == this.Length0();
  ensures this.update01(i,j1,j2,vs).Length1() == this.Length1();
  ensures forall k1:uint64, k2:uint64 :: (0 <= k1 < this.Length0() && 0 <= k2 < this.Length1()) ==> (k1 != i || k2 < j1 || k2 >= j2) ==> this.update01(i,j1,j2,vs).arr2[k1,k2] == this.arr2[k1,k2];
  ensures forall k1:uint64, k2:uint64 :: (0 <= k1 < this.Length0() && 0 <= k2 < this.Length1()) ==> (k1 == i && k2 >= j1 && k2 < k2) ==> this.update01(i,j1,j2,vs).arr2[k1,k2] == vs[k2-j1];
  
}



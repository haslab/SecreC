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



class Array2<T> {
  var arr2 : array2<T>;
  
  function valid() : bool
  reads this`arr2;
  { this.arr2 != null }
  
  function size() : int
  reads this`arr2;
  requires this.arr2 != null && this.valid()
  { this.arr2.Length0 * this.arr2.Length1 }
  
  function shape() : seq<int>
  reads this`arr2;
  requires this.arr2 != null && this.valid()
  { [this.arr2.Length0,this.arr2.Length1] }
  
  method cat0(xs: Array2<T>, ys: Array2<T>) returns (zs: Array2<T>)
  requires xs != null && xs.valid();
  requires ys != null && ys.valid();
  requires xs.arr2.Length1 == ys.arr2.Length1;
  free ensures zs != null && zs.valid();
  free ensures zs.arr2.Length1 == xs.arr2.Length1;
  free ensures zs.arr2.Length0 == xs.arr2.Length0 + ys.arr2.Length0;
  free ensures forall i: int, j: int :: (0 <= i < xs.arr2.Length0 && 0 <= j < xs.arr2.Length1) ==> zs.arr2[i,j] == xs.arr2[i,j];
  free ensures forall i: int, j: int :: (0 <= i < ys.arr2.Length0 && 0 <= j < ys.arr2.Length1) ==> zs.arr2[i+xs.arr2.Length0,j] == ys.arr2[i,j];
  {}
  
  method cat1(xs: Array2<T>, ys: Array2<T>) returns (zs: Array2<T>)
  requires xs != null && xs.valid();
  requires ys != null && ys.valid();
  requires xs.arr2.Length0 == ys.arr2.Length0;
  free ensures zs != null && zs.valid();
  free ensures zs.arr2.Length0 == xs.arr2.Length0;
  free ensures zs.arr2.Length1 == xs.arr2.Length1 + ys.arr2.Length1;
  free ensures forall i: int, j: int :: (0 <= i < xs.arr2.Length0 && 0 <= j < xs.arr2.Length1) ==> zs.arr2[i,j] == xs.arr2[i,j];
  free ensures forall i: int, j: int :: (0 <= i < ys.arr2.Length0 && 0 <= j < ys.arr2.Length1) ==> zs.arr2[i,j+xs.arr2.Length1] == ys.arr2[i,j];
  {}
}

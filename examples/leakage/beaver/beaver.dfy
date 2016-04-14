
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

method BeaverTriple() returns (a: int,b: int,c: int)
ensures c == a * b;
ensures PublicOut(a);
ensures PublicOut(b);
ensures PublicOut(c);

method Beaver (x: int, y: int) returns (w: int)
ensures w == x * y;
{
  var a,b,c: int;
  a,b,c := BeaverTriple();
  // if a,b,c are uniformly random, then e,d are also uniformly random.
  // I don't know how to express this in Dafny in terms of leakage.
  var e: int := x - a;
  var d: int := y - b;
  //assert(DeclassifiedIn(e));
  //assert(DeclassifiedIn(d));
  w := c + e * b + d * a + e * d;
  return w;
}

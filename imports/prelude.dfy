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
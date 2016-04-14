
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
predicate DeclassifiedOut<T> (x

method median_bob (a1: int, a2: int, b1: int, b2: int) returns (r: int)
requires PublicIn(b1);
requires PublicIn(b2);
ensures PublicOut(r);
requires a1 < a2;
requires b1 < b2;
requires a1 != a2 && a1 != b1 && a1 != b2;
requires a2 != b1 && a2 != b2;
requires b1 != b2;
{   
    var a: int;
    var b: int;
    
    var x1: bool;
    x1 := a1 <= b1;
    assert(DeclassifiedOut(x1));
    if x1 { a := a2; b := b1; } else { a := a1; b := b2; }
    
    var x2: bool;
    x2 := a <= b;
    assert(DeclassifiedOut(x2));
    if x2 { r := a; } else { r := b; }
    assume(Leak(r));
    return r;
}

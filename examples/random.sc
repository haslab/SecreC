
module ex;

//@ template<domain D>
//@ function D bool operator < (D uint64 x,D uint64 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 

//@ template<domain D>
//@ function D bool operator && (D bool x,D bool y) {
//@     __builtin("core.band",x,y) :: D bool
//@ } 

//@ template <domain D, type T, dim N>
//@ function uint size (D T[[N]] x) {
//@     __builtin("core.size",x)
//@ }

//@ axiom <domain D,type T> (D T[[1]] xs, uint i)
//@ requires 0 < i && i < size(xs);


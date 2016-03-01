
template <domain D, type T, dim N>
uint size (D T[[N]] x) {
    uint ret;
    __syscall("core.size",x,__return ret);
    return ret;
}

uint64 operator - (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("haskell.sub_uint64",x,y,__return ret);
    return ret;
}

uint64 operator * (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("haskell.mul_uint64",x,y,__return ret);
    return ret;
}

bool operator == (uint64 x,uint64 y) {
    //stub
    bool ret;
    return ret;
} 

void main () {
  int [[2]] arr (5, 5);
  const uint t1 = size(arr[1,0:3]);
  const uint t2 = size(arr[1:5,0]);
  const uint t3 = size(arr[0:1,4:5]);
  assert (size(arr[0:4,0:4]) == 16);
  assert (t1 == 3);
  assert (t2 == 4); 
  assert (t3 == 1);
}


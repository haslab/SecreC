
template <domain D, type T, dim N>
uint size (D T[[N]] x) {
    uint ret;
    __syscall("core.size",x,__return ret);
    return ret;
}

bool operator == (uint64 x,uint64 y) {
    //stub
    bool ret;
    return ret;
} 

uint operator * (uint x,uint y) {
    uint ret;
    return ret;
}


void main () {
  int [[1]] empty_arr;
  int [[1]] arr (100);
  int [[2]] mat (5, 5);
  assert (size(empty_arr) == 0);
  assert (size(arr) == 100);
  assert (size(mat) == 25);
}



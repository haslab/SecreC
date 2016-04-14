

template <domain D, type T, dim N>
uint size (D T[[N]] x) {
//    uint ret;
//    __syscall("core.size",x,__return ret);
    return 0;
}

bool[[1]] operator == (uint[[1]] x,uint[[1]] y) {
    assert(size(x) == size(y));
    bool[[1]] ret (size(x));
    //for (uint i = 0; i < size(x); i++) {
    //    ret[i] = x[i] == y[i];
    //}
    return ret;
}

//void main () {
//  int [[1]] a (10) = 1;
//  uint i = size(a);
//  //const uint t = size(a + b);
////  assert (t == (10 :: uint));
//}

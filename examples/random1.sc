template <domain D, type T, dim N>
uint size (D T[[N]] x) {
//    uint ret;
//    __syscall("core.size",x,__return ret);
    return 0;
}

int operator + (int x,int y) {
    int ret;
    __syscall("core.add_int",x,y,__return ret);
    return ret;
} 
uint operator + (uint x,uint y) {
    uint ret;
    __syscall("core.add_uint",x,y,__return ret);
    return ret;
} 

bool operator > (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.gt_uint64",x,y,__return ret);
    return ret;
}
bool operator < (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.lt_uint64",x,y,__return ret);
    return ret;
} 
bool operator == (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.eq_uint64",x,y,__return ret);
    return ret;
} 
bool operator != (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.neq_uint64",x,y,__return ret);
    return ret;
} 

bool operator == (int64 x,int64 y) {
    bool ret;
    __syscall("core.eq_int64",x,y,__return ret);
    return ret;
} 

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator != (D T[[N]] x,D T[[N]] y) {
    D bool[[N]] ret;
    return ret;
    //D bool[[N]] ret (varray(shape(x),N)...);
    //for (uint i = 0; i < shape(x)[0]; i++) {
    //    ret[i] = x[i] != y[i];
    //}
    //return ret;
}

bool all (bool[[1]] vec) {
//    uint n = size (vec);
//    for (uint i = 0; i<n; ++i) {
//        if (!vec[i]) {
//            return false;
//        }
//    }
    return true;
}

template <domain D, type T>
D bool[[1]] operator == (D T[[1]] x,D T[[1]] y) {
    assert(size(x) == size(y));
    D bool[[1]] ret (size(x));
    for (uint i = 0; i < size(x); i++) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator == (D T[[N]] x,D T[[N]] y) {
    assert(all(shape(x) == shape(y)));
    D bool[[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}


template <domain D, type T, dim N>
uint[[1]] shape (D T[[N]] arr) {
    uint[[1]] ret;
    __syscall("core.shape",arr,__return ret);
    return ret;
}


template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator + (D T[[N]] x,D T[[N]] y) {
    assert(all(shape(x) == shape(y)));
    D T [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] + y[i];
    }
    return ret;
}

void main () {
  int [[1]] a (10) = 1;
  int [[1]] b (10) = 2;
  //bool [[1]] c = a == b;
  int [[1]] t = a + b;
//  assert (t == (10 :: uint));
}

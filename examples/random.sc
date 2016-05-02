
int64 operator (int64) (bool x) {
    int64 ret;
    __syscall("core.cast_bool_int64",x,__return ret);
    return ret;
}
uint16 operator (uint16) (bool x) {
    uint16 ret;
    __syscall("core.cast_bool_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (uint16 x) {
    uint16 ret;
    __syscall("core.cast_uint16_uint16",x,__return ret);
    return ret;
}
bool operator (bool) (bool x) {
    bool ret;
    __syscall("core.cast_bool_bool",x,__return ret);
    return ret;
}
bool operator (bool) (int64 x) {
    bool ret;
    __syscall("core.cast_int64_bool",x,__return ret);
    return ret;
}


// array casts
template <domain D, dim N { N > 0 }, type X, type Y>
D Y[[N]] operator (Y) (D X[[N]] x) {
    D Y[[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = (Y) x[i];
    }
    return ret;
}

bool operator > (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.gt_uint64",x,y,__return ret);
    return ret;
} 

//template <domain D, type T, dim N>
//uint size (D T[[N]] x) {
//    uint ret;
//    __syscall("core.size",x,__return ret);
//    return ret;
//}

template <domain D, type T, dim N>
uint[[1]] shape (D T[[N]] arr) {
    uint[[1]] ret;
    __syscall("core.shape",arr,__return ret);
    return ret;
}


bool operator < (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.lt_uint64",x,y,__return ret);
    return ret;
} 
uint64 operator + (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.add_uint64",x,y,__return ret);
    return ret;
} 
//bool operator == (uint16 x,uint16 y) {
//    bool ret;
//    __syscall("core.eq_uint16",x,y,__return ret);
//    return ret;
//} 
//bool operator == (bool x,bool y) {
//    bool ret;
//    __syscall("core.eq_bool",x,y,__return ret);
//    return ret;
//} 

//template <domain D, type T>
//D bool[[1]] operator == (D T[[1]] x,D T[[1]] y)
////@ requires equal(shape(x),shape(y));
//{
//
//    D bool[[1]] ret (size(x));
//    for (uint i = 0; i < size(x); i++) {
//        ret[i] = x[i] == y[i];
//    }
//    return ret;
//}

//bool operator ! (bool x) {
//    if (x==false) return true;
//    else return false;
//}
//bool all (bool [[1]] arr) {
//  for (uint i = 0; i < size (arr); ++ i)
//    if (!arr[i]) return false;
//  return true;
//}

void simple_tests () {
  //bool [[1]] b (5);
  int [[1]] i (5);
  uint16 [[1]] u (5);

  u = (uint16) 0;

  //b = false; i = 1; u = 2;
  //b = (bool)   b;
  //i = (int)    b;
  //u = (uint16) b;
  //assert (all (i == 0));
  //assert (all (u == (uint16) 0));
}

template <domain D, type T, dim N>
uint size (D T[[N]] x) {
    uint ret;
    __syscall("core.size",x,__return ret);
    return ret;
}

uint64 operator * (uint64 x,uint64 y) {
    uint64 ret;
     __syscall("haskell.mul_uint64",x,y,__return ret);
    return ret;
}

bool operator <= (uint64 x,uint64 y) {
    //stub
    bool ret;
    return ret;
} 

uint64 operator - (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("haskell.sub_uint64",x,y,__return ret);
    return ret;
} 

uint64 operator + (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("haskell.add_uint64",x,y,__return ret);
    return ret;
} 

template <domain D, type T, dim N, dim... n>
D T[[N]](n...) product (D T[[N]]... xs (n...)) {
    D T[[N]] p (n...) = 0;
    for (uint i = 0; i <= size...(xs); i++)
        p *= xs[i];
    return p;
}

template <domain D, type T, dim N>
D T[[size...(ns)]](ns...) reshape (D T[[N]] arr, uint... ns) {
    //stub
    D T[[size...(ns)]] ret;
    assert(size(arr) == product(ns...));
    return ret;
}

bool operator == (uint64 x,uint64 y) {
    //stub
    bool ret;
    return ret;
} 
bool operator == (int64 x,int64 y) {
    //stub
    bool ret;
    return ret;
} 

template <domain D, type T, dim N>
uint[[1]](N) shape (D T[[N]] arr) {
    //stub
    uint[[1]] ret (N);
    return ret;
}

void main () {
  int [[1]] t (4) = 0;
  int [[2]] m (2, 2) = 1;
  t = reshape (t, 4);
  assert (size(t) == 4);
  assert (t[0] == 0);

  t = reshape (m, 4);
  assert (size(t) == 4);
  assert (size(shape(m)) == 2);
  assert (t[0] == 1);
}


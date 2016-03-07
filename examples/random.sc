
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
uint64 operator - (uint64 x,uint64 y) {
    //stub
    uint64 ret;
    return ret;
} 
uint64 operator + (uint64 x,uint64 y) {
    //stub
    uint64 ret;
    return ret;
} 
bool operator > (uint64 x,uint64 y) {
    //stub
    bool ret;
    return ret;
} 
bool operator < (uint64 x,uint64 y) {
    //stub
    bool ret;
    return ret;
} 

template <domain D, type T, dim N { N > 0 }, dim... n >
D T[[N]](n...) operator + (D T[[N]] x (n...),D T[[N]] y (n...)) {
    //stub
    D T [[N]] ret (n...);
    D T z;
    // simply to enforce the T operator + (T,T) constraint
    z = z + z;
    return ret;
}

uint [[1]] nat (uint n) {
  uint [[1]] out (n) = 1;
  if (n == 1) return out;
  uint [[1]] rec = nat (n - 1);
  assert (size(rec) == (n - 1));
  out[1:n] += rec;
  return out;
}

void main () {
  uint [[1]] nats = nat (5 :: uint);
  assert (size(nats) == 5);
  for (uint i = 0; i < 5; ++ i) {
    assert (nats[i] == i + 1);
  }
}




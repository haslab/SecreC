
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

uint64 operator * (uint64 x,uint64 y) {
    //stub
    uint64 ret;
    return ret;
} 
int64 operator + (int64 x,int64 y) {
    //stub
    int64 ret;
    return ret;
} 
bool operator > (uint64 x,uint64 y) {
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

void main () {
  int [[1]] a (10) = 1;
  int [[1]] b (10) = 2;
  uint t = size(a + b);
//  assert (t == (10 :: uint));
}


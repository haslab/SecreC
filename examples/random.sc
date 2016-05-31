
struct wrap {
    int x;
}

struct arr_t {
    int[[1]] x;
}

int64 operator + (int64 x,int64 y) {
    int64 ret;
    __syscall("core.add_int64",x,y,__return ret);
    return ret;
}
int64 operator - (int64 x,int64 y) {
    int64 ret;
    __syscall("core.sub_int64",x,y,__return ret);
    return ret;
}
uint64 operator + (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.add_uint64",x,y,__return ret);
    return ret;
}
uint64 operator - (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.sub_uint64",x,y,__return ret);
    return ret;
}
bool operator > (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.gt_uint64",x,y,__return ret);
    return ret;
} 
template <domain D,type T,dim N>
D T[[N]] repeat (D T x) {
    D T[[N]] ret;
    __syscall("core.repeat",x,__return ret);
    return ret;
}
bool operator < (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.lt_uint64",x,y,__return ret);
    return ret;
} 


template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator + (D T[[N]] x,D T[[N]] y)
{
    D T [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] - y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator - (D T[[N]] x,D T[[N]] y)
{
    D T [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] - y[i];
    }
    return ret;
}
template <domain D, type T, dim N>
uint[[1]] shape (D T[[N]] arr) {
    uint[[1]] ret;
    __syscall("core.shape",arr,__return ret);
    return ret;
}

template <domain D, type T, dim N>
uint size (D T[[N]] x) {
    uint ret;
    __syscall("core.size",x,__return ret);
    return ret;
}
bool operator == (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.eq_uint64",x,y,__return ret);
    return ret;
} 

void main () {
    wrap t;

//    assert (t.x ++ == 0);
//    assert (t.x -- == 1);
//    assert (++ t.x == 1);
//    assert (-- t.x == 0);

    arr_t a;
//    a.x = {1};
//
    a.x ++;
    a.x --;
//    ++ a.x;
//    -- a.x;
//
//    a.x[0] ++;
//    a.x[0] --;
//    ++ a.x[0];
//    -- a.x[0];
}

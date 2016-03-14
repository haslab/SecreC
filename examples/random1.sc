
bool operator && (bool x,bool y) {
    bool ret;
    __syscall("core.band",x,y,__return ret);
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

uint64 operator - (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.sub_uint64",x,y,__return ret);
    return ret;
}
uint64 operator + (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.add_uint64",x,y,__return ret);
    return ret;
}


template <domain D, dim N { N > 0 }, dim... n >
D bool[[N]](n...) operator && (D bool[[N]] x (n...),D bool[[N]] y (n...)) {
    //stub
    D bool[[N]] ret (n...);
    for (uint i = 0; i < n[0]; i++) {
        ret[i] = x[i] && y[i];
    }
    return ret;
}

void main() {
    bool[[2]] b1(10,20);
    bool[[2]] b2(10,20);
    bool[[2]] b3 = b1 && b2;
}
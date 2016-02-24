
bool operator == (uint64 x,uint64 y) {
    //stub
    bool ret;
    return ret;
} 

bool operator < (uint64 x,uint64 y) {
    //stub
    bool ret;
    return ret;
} 

template <domain D, type T, dim N, dim... nx, dim... ny, dim... nz>
D T[[N]](nz...) cat (D T[[N]] x (nx...), D T[[N]] y (ny...), const uint n { n < N }) {
    D T[[N]] ret (nz...);
    
    for (uint i = 0; i < N; i++) {
        if (i == n) {
            assert(nz[i] == nx[i] + ny[i]);
        }
        else {
            assert(nx[i] == ny[i]);
            assert(nz[i] == nx[i]);
        }
    }
    
    return ret;
}
template <domain D, type T, dim N>
uint size (D T[[N]] x) {
//    uint ret;
//    __syscall("core.size",x,__return ret);
    return 0;
}

void main () {
    uint [[1]] nats;
    uint i = size(nats);
}
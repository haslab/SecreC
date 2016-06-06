

//cat

template <domain D, type T, dim N>
D T[[N]] cat (D T[[N]] x, D T[[N]] y) {
    return cat(x,y,0);
}

//@ D T[[N]] cat (D T[[N]] x, D T[[N]] y) {
//@     cat(x,y,0);
//@ }
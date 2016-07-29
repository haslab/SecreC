
template <domain D,type T,dim N>
function D T[[N]] repeat (D T x, uint sz) {
    __builtin("core.repeat",x,sz) :: D T [[N]]
}

string argument (string name) {
    uint num_bytes;
    uint8[[1]] bytes (num_bytes) ;
    string x;
    return x;
}



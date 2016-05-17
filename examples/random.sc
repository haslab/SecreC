
bool operator == (bool x,bool y) {
    bool ret;
    __syscall("core.eq_bool",x,y,__return ret);
    return ret;
} 

bool operator ! (bool x) {
    return (x==false);
}
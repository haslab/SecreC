


//repeat

template <domain D,type T>
D T[[1]] repeat (D T x,uint... ns, uint... xs) {
    D T[[size...(xs)]] ret (xs...);
    //__syscall("core.repeat",x,ns,__return ret);
    return ret;
}

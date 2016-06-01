
template<type T>
struct option {
    T data;
    bool some;
}

template<type T>
option<T> some(T x) {
    public option<T> res;
//    res.some = true;
//    res.data = x;
    return res;
}

//template <type T>
//option<T> nothing () {
//    public option<T> res;
//    res.some = false;
//    return res;
//}

template <type T>
bool isSome (option<T> o) {
    return true;
    //return o.some;
}

void main () {
    uint i;
    assert (isSome (some (i)));

//    public option<uint> t = nothing ();
//    assert (! isSome (t));
}


template<T> struct ty {
    T a;
}
template struct ty<int> {
    int size;
}
template<T> struct ty<T*> {
    T elem;
}

template<T> ty<T> foo (ty<T> x) {
    return x;
}

void main () {
    int i = 0;
    int j = foo(0);
}
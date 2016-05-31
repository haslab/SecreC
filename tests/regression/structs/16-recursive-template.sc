
template <type T>
struct nest {
    T x;
    nest<T> y;
}

void main () {
    nest<int> n;
    n.y.x = 0;
}

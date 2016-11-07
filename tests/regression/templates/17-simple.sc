#OPTIONS_SECREC --implicitcoercions=onc --backtrack=fullb


template <dim D>
void foo (uint [[D]] arr) {
    uint [[D]] brr = arr;
}

void main () {
    foo (3 :: uint);
    foo (reshape (7 :: uint, 5, 6));
}

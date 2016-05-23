#OPTIONS_SECREC --failtypechecker

kind a3p;

template <domain D : a3p>
struct test { }

void main () {
    test<public> x;
}

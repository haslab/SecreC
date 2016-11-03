#OPTIONS_SECREC --failtypechecker --implicitcoercions=defaultsc

kind a3p;

template <domain D : a3p>
struct test { }

void main () {
    test<public> x;
}

#OPTIONS_SECREC --implicitcoercions=offc

template <type T> T get () {T x; return x; }

void main() {
  float x = get ();
  uint  y = get ();
  uint  z = get ();
}

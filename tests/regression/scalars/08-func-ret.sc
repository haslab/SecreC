#OPTIONS_SECREC --implicitcoercions=offc

int one () { return 1; }

void main () {
  int x = one ();
  assert (x == 1);
}

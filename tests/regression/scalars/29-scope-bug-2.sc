#OPTIONS_SECREC --implicitcoercions=offc

void main () {
  if (true);
  int i;
  if (true) i = 1;
  assert (i == 1);
}

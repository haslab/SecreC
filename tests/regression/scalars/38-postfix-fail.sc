#OPTIONS_SECREC --implicitcoercions=offc

// bug in postfix inc/dec code generation -- fixed
void main () {
  int i = 0;
  if (true) {
    assert ((i ++) == 0);
  }

  return;
}

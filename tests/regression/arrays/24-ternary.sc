#OPTIONS_SECREC --implicitcoercions=onc --backtrack=fullb --matching=gorderedm --promote=nop

void main () {
  int [[1]] r (5);
  bool b = true;
  r = b ? r + 1 : r - 1;
  assert (size(r) == 5);
  assert (r[0] == 1);
}

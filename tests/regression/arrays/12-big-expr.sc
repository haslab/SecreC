#OPTIONS_SECREC --implicitcoercions=offc --backtrack=noneb --matching=gorderedm

void main () {
  int [[1]] a (10) = repeat(1,10);
  int [[1]] b (10) = repeat(1,10);
  int [[1]] c (10) = repeat(1,10);
  int [[1]] r = c * (((a + b) * c - a) + b + b + b);
  assert (size(r) == 10);
  assert (r[0] == 4);
}

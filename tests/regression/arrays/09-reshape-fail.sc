#OPTIONS_SECREC --failtypechecker

void main () {
  int [[1]] t (4) = 0;

  t = reshape (42, 1);
  assert (size(t) == 1);
  assert (t[0] == 42);
}
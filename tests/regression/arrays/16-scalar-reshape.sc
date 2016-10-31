#OPTIONS_SECREC --implicitcoercions=offc

void main () {
  int [[1]] arr (5) = 0;
  arr = reshape (1, 5);
  assert (size(arr) == 5);
  assert (arr[0] == 1);
}

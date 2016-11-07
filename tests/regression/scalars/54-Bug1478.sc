#OPTIONS_SECREC --implicitcoercions=offc

uint a = 4;
uint b = a * (a - 1);
void main() {
  assert (a == 4);
}

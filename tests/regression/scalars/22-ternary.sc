#OPTIONS_SECREC --implicitcoercions=onc

kind additive3pp;
domain sharemind_test_pd additive3pp;

int val = 0;

int load_one () { return 1; }

int load_two () { return 2; }

void main () {
  bool t = true;
  bool f = false;

  assert ( (t ? (int)11 : 12) == 11 );
  assert ( (f ? (int)13 : 14) == 14 );
  
  sharemind_test_pd int one = 1;
  sharemind_test_pd int two = 2;
  assert ( declassify ((t ? one : two) == one) );
  assert ( declassify ((f ? one : two) == two) );

  val = t ? load_one() : load_two();
  assert (val == 1);
  
  val = f ? load_one() : load_two();
  assert (val == 2);
}

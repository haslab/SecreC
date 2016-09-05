kind additive3pp;
domain sharemind_test_pd additive3pp;

sharemind_test_pd int classify (int x) {
    havoc sharemind_test_pd int y;
    return y;
}
bool declassify (sharemind_test_pd bool x) {
    havoc bool y;
    return y;
}

sharemind_test_pd bool operator == (sharemind_test_pd int x,sharemind_test_pd int y) {
    // stub
    havoc sharemind_test_pd bool     ret;
    return ret;
}

int val = 0;

void load_one () { val = 1; }

void load_two () { val = 2; }

void main () {
  bool t = true;
  bool f = false;

  assert ( (t ? (int)11 : 12) == 11 );
  assert ( (f ? (int)13 : 14) == 14 );
  
  sharemind_test_pd int one = 1;
  sharemind_test_pd int two = 2;
  assert ( declassify ((t ? one : two) == one) );
  assert ( declassify ((f ? one : two) == two) );

  t ? load_one() : load_two();
  assert (val == 1);
  
  f ? load_one() : load_two();
  assert (val == 2);
}

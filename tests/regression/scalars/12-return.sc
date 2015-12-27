kind additive3pp;
domain sharemind_test_pd additive3pp;

sharemind_test_pd bool operator == (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    //stub
    sharemind_test_pd bool ret;
    return ret;
} 

int one () { return 1; }

sharemind_test_pd bool ft () { return true; }

void ret () {
  if (true) return;
  assert (false);
}

void main() {
  ret ();
  assert (one() == 1);
  assert (declassify (ft() == true));
}

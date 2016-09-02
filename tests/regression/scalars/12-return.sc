kind additive3pp;
domain sharemind_test_pd additive3pp;

sharemind_test_pd bool classify (bool x) {
    havoc sharemind_test_pd bool y;
    return y;
}
bool declassify (sharemind_test_pd bool x) {
    havoc bool y;
    return y;
}

sharemind_test_pd bool operator == (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    //stub
    havoc sharemind_test_pd bool ret;
    return ret;
} 

int one () { return 1; }

sharemind_test_pd bool ft () { return true; }

//void ret () {
//  if (true) return;
//  assert (false);
//}

void main() {
  //ret ();
  //assert (one() == 1);
  assert (declassify (ft() == true));
}

kind additive3pp;
domain sharemind_test_pd additive3pp;

sharemind_test_pd int classify (int x) {
    havoc sharemind_test_pd int y;
    return y;
}
sharemind_test_pd bool classify (bool x) {
    havoc sharemind_test_pd bool y;
    return y;
}
bool declassify (sharemind_test_pd bool x) {
    havoc bool y;
    return y;
}

sharemind_test_pd bool operator == (sharemind_test_pd int x,sharemind_test_pd int y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}

sharemind_test_pd bool operator ! (sharemind_test_pd bool x) {
    //stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd int operator - (sharemind_test_pd int x) {
    //stub
    havoc sharemind_test_pd int ret;
    return ret;
}

void main () {
  sharemind_test_pd bool t = true;
  sharemind_test_pd bool f = false;
  sharemind_test_pd int one = 1;
  sharemind_test_pd int none = -1;
  assert (declassify (!f));
  assert (declassify (!!t));
  assert (declassify (-one == none));
  assert (declassify (- -one == one));
}

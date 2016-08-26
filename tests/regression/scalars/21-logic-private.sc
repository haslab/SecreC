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

sharemind_test_pd bool operator && (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator || (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator == (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator != (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}

void main () {
  sharemind_test_pd bool t = true;
  sharemind_test_pd bool f = false;

  //assert (declassify ((t && t) == t));
  //assert (declassify ((t && f) == f));
  //assert (declassify ((f && t) == f));
  //assert (declassify ((f && f) == f));
  //
  //assert (declassify ((t || t) == t));
  //assert (declassify ((t || f) == t));
  //assert (declassify ((f || t) == t));
  //assert (declassify ((f || f) == f));
  //
  //assert (declassify ((t == t) == t));
  //assert (declassify ((t == f) == f));
  //assert (declassify ((f == t) == f));
  //assert (declassify ((f == f) == t));
  
  assert (declassify ((t != t) == f));
  //assert (declassify ((t != f) == t));
  //assert (declassify ((f != t) == t));
  //assert (declassify ((f != f) == f));
}

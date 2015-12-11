kind additive3pp;
domain sharemind_test_pd additive3pp;

sharemind_test_pd uint classify (uint x) {
    //stub
    sharemind_test_pd uint ret;
    return ret;
}

uint declassify (sharemind_test_pd uint x) {
    //stub
    uint ret;
    return ret;
}

void main () {
  sharemind_test_pd uint [[1]] carr (5) = 1;
  uint [[1]] arr = declassify (carr);
  assert (size(arr) == 5);
  assert (arr[0] == (1 :: uint));
}

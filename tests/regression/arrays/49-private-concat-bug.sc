#OPTIONS_SECREC --implicitcoercions=offc

kind additive3pp;
domain sharemind_test_pd additive3pp;

sharemind_test_pd uint classify(uint x) {
    return __builtin("core.classify",x) :: sharemind_test_pd uint;
}

void main () {
  sharemind_test_pd uint [[2]] F_cache (0, 5);
  sharemind_test_pd uint [[2]] z (1, 5);
  cat (F_cache, z);
}

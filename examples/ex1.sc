
//@ leakage lemma lcomparisons_subset <domain D,type T> (D T[[1]] xs,D T[[1]] ys)
//@ requires multiset(ys) <= multiset(xs);
//@ requires lcomparisons(xs);
//@ ensures lcomparisons(ys);

//@ leakage lemma lcomparison_subset <domain D,type T> (D T[[1]] xs,D T[[1]] ys, D T[[1]] z)
//@ requires multiset(ys) <= multiset(xs);
//@ requires in(z,xs);
//@ requires lcomparisons(xs);
//@ ensures lcomparison(ys,z);

//@ lemma ArrayHead <domain D,type T> (D T[[1]] xs)
//@ requires size(xs) > 1;
//@ ensures xs == cat({xs[0]},xs[1:]);
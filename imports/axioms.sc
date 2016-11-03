#OPTIONS_SECREC --implicitcoercions=offc

module axioms;

//@ axiom <domain D,type T> (D T[[1]] xs)
//@ ensures size(xs) == size(multiset(xs));

//@ axiom <domain D,type T> (D T[[1]] xs)
//@ requires reclassify(xs) == {};
//@ ensures multiset(xs) == multiset{};

//@ axiom <domain D,type T> (D T[[1]] xs)
//@ ensures multiset(xs[:size(xs)]) == multiset(xs);

//@ axiom <domain D,type T> (D T[[1]] xs, uint i)
//@ requires 0 <= i && i < size(xs);
//@ ensures multiset(xs[:i+1]) == multiset(xs[:i]) + multiset{xs[i]};
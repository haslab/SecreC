
module axioms;

//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ ensures size(xs) == size(multiset(xs));

//@ axiom<domain D,type T> (D T[[1]] i)
//@ requires i == {};
//@ requires {} == i;

//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ ensures multiset(xs[:size(xs)]) == multiset(xs);
//x 
//x //@ axiom <domain D,type T> (D T[[1]] xs, uint i)
//x //@ requires 0 <= i && i < size(xs);
//x //@ ensures multiset(xs[:i+1]) == multiset(xs[:i]) + multiset{xs[i]};
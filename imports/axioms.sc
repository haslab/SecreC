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

//@ axiom <domain D,type T> (D T[[1]] xs, D T[[1]] ys)
//@ ensures set(cat(xs,ys)) == set(xs) + set(ys);

//@ axiom <domain D,type T> (D T x)
//@ ensures set({x}) == set{x};

//@ axiom <domain D,type T> (D T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures assertion<D>(xs == snoc(init(xs),last(xs)));

//x //@ lemma Snoc1 <domain D,type T> (D T[[1]] xs)
//x //@ requires size(xs) > 0;
//x //@ ensures assertion<D>(xs == snoc(init(xs),last(xs)));

//@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j < shape(xs)[1];
//@ ensures assertion<D>(xs[i,:][j] == xs[i,j]);

//@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j <= shape(xs)[1];
//@ ensures assertion<D>(xs[i,:][:j] == xs[i,:j]);

//@ axiom<domain D,type T> (D T x)
//@ ensures size({x}) == 1;
//@ ensures assertion<D>({x}[0] == x);

//@ axiom<domain D,type T> (D T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures assertion<D>(xs == snoc(init(xs),last(xs)));
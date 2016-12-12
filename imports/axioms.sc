#OPTIONS_SECREC --implicitcoercions=offc

module axioms;

//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ ensures size(xs) == size(multiset(xs));
//x 
//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ requires reclassify(xs) == {};
//x //@ ensures multiset(xs) == multiset{};
//x 
//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ ensures multiset(xs[:size(xs)]) == multiset(xs);
//x 
//x //@ axiom <domain D,type T> (D T[[1]] xs, uint i)
//x //@ requires 0 <= i && i < size(xs);
//x //@ ensures multiset(xs[:i+1]) == multiset(xs[:i]) + multiset{xs[i]};
//x 
//x //@ axiom <domain D,type T> (D T[[1]] xs, D T[[1]] ys)
//x //@ ensures set(cat(xs,ys)) == set(xs) + set(ys);
//x 
//x //@ axiom <domain D,type T> (D T x)
//x //@ ensures set({x}) == set{x};

//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ requires size(xs) > 0;
//x //@ ensures assertion<D>(xs == snoc(init(xs),last(xs)));

//@ lemma Snoc1 <domain D,type T> (D T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures assertion<D>(xs == snoc(init(xs),last(xs)));

//x //@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//x //@ requires i < shape(xs)[0];
//x //@ requires j < shape(xs)[1];
//x //@ ensures assertion<D>(xs[i,:][j] == xs[i,j]);
//x 
//x //@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//x //@ requires i < shape(xs)[0];
//x //@ requires j <= shape(xs)[1];
//x //@ ensures assertion<D>(xs[i,:][:j] == xs[i,:j]);
//x 
//x //@ axiom<domain D,type T> (D T x)
//x //@ ensures size({x}) == 1;
//x //@ ensures assertion<D>({x}[0] == x);
//x 
//x //@ axiom<domain D,type T> (D T[[1]] xs)
//x //@ requires size(xs) > 0;
//x //@ ensures assertion<D>(xs == snoc(init(xs),last(xs)));
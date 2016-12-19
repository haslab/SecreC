#OPTIONS_SECREC --implicitcoercions=offc --ignorespecdomains

module axioms;

//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ requires size(xs) > 0;
//x //@ ensures assertion<D>(xs === snoc(init(xs),last(xs)));

//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ ensures size(xs) === size(multiset(xs));
//x 
//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ requires reclassify(xs) === {};
//x //@ ensures multiset(xs) === multiset{};
//x 
//@ lemma MultisetSlice <domain D,type T> (D T[[1]] xs)
//@ ensures multiset(xs[:size(xs)]) === multiset(xs);
 
//@ lemma MultisetSliceOne <domain D,type T> (D T[[1]] xs, uint i)
//@ requires 0 <= i && i < size(xs);
//@ ensures multiset(xs[:i+1]) === union(multiset(xs[:i]),multiset{xs[i]});
//x 
//x //@ lemma SetCat <domain D,type T> (D T[[1]] xs, D T[[1]] ys)
//x //@ ensures set(cat(xs,ys)) === union(set(xs),set(ys));
//x 
//x //@ axiom <domain D,type T> (D T x)
//x //@ ensures set({x}) === set{x};
//x 
//x //@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//x //@ requires i < shape(xs)[0];
//x //@ requires j < shape(xs)[1];
//x //@ ensures assertion<D>(xs[i,:][j] === xs[i,j]);
//x 
//x //@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//x //@ requires i < shape(xs)[0];
//x //@ requires j < shape(xs)[1];
//x //@ ensures assertion<D>(xs[:,j][i] === xs[i,j]);
//x 
//x //@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//x //@ requires i < shape(xs)[0];
//x //@ requires j <= shape(xs)[1];
//x //@ ensures assertion<D>(xs[i,:][:j] === xs[i,:j]);
//x 
//x //@ axiom<domain D,type T> (D T x)
//x //@ ensures size({x}) === 1;
//x //@ ensures assertion<D>({x}[0] === x);
//x 
//x // multiplication is commutative
//x //@ axiom <domain D> (D uint[[1]] xs, D uint[[1]] ys)
//x //@ requires size(xs) === size(ys);
//x //@ ensures xs * ys === ys * xs;
//x     
//x // multiplication is associative
//x //@ axiom <domain D> (D uint[[1]] xs, D uint[[1]] ys, D uint[[1]] zs)
//x //@ requires size(xs) === size(ys) && size(ys) === size(zs);
//x //@ ensures xs * (ys * zs) === (xs * ys) * zs;


// workaround for empty modules
void empty() { }
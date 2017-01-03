#OPTIONS_SECREC --implicitcoercions=offc --ignorespecdomains

module axioms;

//@ lemma SnocDef <domain D,type T> (D T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures assertion<D>(xs === snoc(init(xs),last(xs)));

//@ lemma ConsDef <domain D,type T> (D T[[1]] xs)
//@ requires size(xs) > 1;
//@ ensures xs === cons(head(xs),tail(xs));

//@ lemma MultisetSize <domain D,type T> (D T[[1]] xs)
//@ ensures size(xs) === size(multiset(xs));

//@ lemma MultisetEmpty <domain D,type T> (D T[[1]] xs)
//@ requires reclassify(xs) === {};
//@ ensures multiset(xs) === multiset{};

//@ lemma MultisetSlice <domain D,type T> (D T[[1]] xs)
//@ ensures multiset(xs[:size(xs)]) === multiset(xs);
 
//@ lemma MultisetSliceOne <domain D,type T> (D T[[1]] xs, uint i)
//@ requires 0 <= i && i < size(xs);
//@ ensures multiset(xs[:i+1]) === union(multiset(xs[:i]),multiset{xs[i]});

//@ lemma MultisetSnoc <domain D,type T> (D T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures multiset(xs) === union(multiset(init(xs)),multiset{last(xs)});

//@ lemma SetUnion <domain D,type T> (D T[[1]] xs, D T[[1]] ys)
//@ ensures set(cat(xs,ys)) === union(set(xs),set(ys));

//@ lemma SetSingleton <domain D,type T> (D T x)
//@ ensures set({x}) === set{x};

//@ lemma SliceProjection <domain D,type T> (D T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j < shape(xs)[1];
//@ ensures assertion<D>(xs[i,:][j] === xs[i,j]);

//@ lemma DoubleSlice <domain D,type T> (D T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j <= shape(xs)[1];
//@ ensures assertion<D>(xs[i,:][:j] === xs[i,:j]);

//@ lemma SingletonProjection <domain D,type T> (D T x)
//@ ensures size({x}) === 1;
//@ ensures assertion<D>({x}[0] === x);

// array multiplication is commutative
//@ axiom <domain D> (D uint[[1]] xs, D uint[[1]] ys)
//@ requires size(xs) === size(ys);
//@ ensures xs * ys === ys * xs;

// array multiplication is associative
//@ axiom <domain D> (D uint[[1]] xs, D uint[[1]] ys, D uint[[1]] zs)
//@ requires size(xs) === size(ys) && size(ys) === size(zs);
//@ ensures xs * (ys * zs) === (xs * ys) * zs;


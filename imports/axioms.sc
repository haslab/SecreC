#OPTIONS_SECREC --implicitcoercions=offc

module axioms;

//@ axiom <type T> (T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures xs === snoc(init(xs),last(xs));

//@ lemma SnocDef <type T> (T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures xs === snoc(init(xs),last(xs));

//@ axiom <type T> (T[[1]] xs)
//@ requires size(xs) > 1;
//@ ensures xs === cons(head(xs),tail(xs));

//@ lemma SliceEndEqual <type T> (T[[1]] xs)
//@ ensures xs[:size(xs)] === xs;

//@ lemma SliceBeginEqual <type T> (T[[1]] xs)
//@ ensures xs[0:] === xs;

//@ lemma ConsDef <type T> (T[[1]] xs)
//@ requires size(xs) > 1;
//@ ensures xs === cons(head(xs),tail(xs));

//@ axiom <type T> (T[[1]] xs)
//@ ensures size(xs) === size(multiset(xs));

//@ lemma MultisetSize <type T> (T[[1]] xs)
//@ ensures size(xs) === size(multiset(xs));

//@ axiom <type T> (T[[1]] xs)
//@ requires reclassify(xs) === {};
//@ ensures multiset(xs) === multiset{};

//@ lemma MultisetEmpty <type T> (T[[1]] xs)
//@ requires reclassify(xs) === {};
//@ ensures multiset(xs) === multiset{};

//@ axiom <type T> (T[[1]] xs)
//@ ensures multiset(xs[:size(xs)]) === multiset(xs);

//@ lemma MultisetSlice <type T> (T[[1]] xs)
//@ ensures multiset(xs[:size(xs)]) === multiset(xs);

//@ axiom <type T> (T[[1]] xs, uint i)
//@ requires 0 <= i && i < size(xs);
//@ ensures multiset(xs[:i+1]) === union(multiset(xs[:i]),multiset{xs[i]});
 
//@ lemma MultisetSliceOne <type T> (T[[1]] xs, uint i)
//@ requires 0 <= i && i < size(xs);
//@ ensures multiset(xs[:i+1]) === union(multiset(xs[:i]),multiset{xs[i]});

//@ axiom <type T> (T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures multiset(xs) === union(multiset{head(xs)},multiset(tail(xs)));

//@ lemma MultisetCons <type T> (T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures multiset(xs) === union(multiset{head(xs)},multiset(tail(xs)));

//@ axiom <type T> (T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures multiset(xs) === union(multiset(init(xs)),multiset{last(xs)});

//@ lemma MultisetSnoc <type T> (T[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures multiset(xs) === union(multiset(init(xs)),multiset{last(xs)});

//@ axiom <type T> (T[[1]] xs, T x)
//@ ensures multiset(xs) === union(multiset(xs),multiset{x});

//@ lemma MultisetSnoc1 <type T> (T[[1]] xs, T x)
//@ ensures multiset(xs) === union(multiset(xs),multiset{x});

//@ axiom <type T> (T[[1]] xs, T[[1]] ys)
//@ ensures multiset(cat(xs,ys)) === union(multiset(xs),multiset(ys));

//@ lemma MultisetUnion <type T> (T[[1]] xs, T[[1]] ys)
//@ ensures multiset(cat(xs,ys)) === union(multiset(xs),multiset(ys));

//@ axiom <type T> (T[[1]] xs, T[[1]] ys)
//@ ensures set(cat(xs,ys)) === union(set(xs),set(ys));

//@ lemma SetUnion <type T> (T[[1]] xs, T[[1]] ys)
//@ ensures set(cat(xs,ys)) === union(set(xs),set(ys));

//@ axiom <type T> (T x)
//@ ensures set({x}) === set{x};

//@ lemma SetSingleton <type T> (T x)
//@ ensures set({x}) === set{x};

//@ axiom <type T> (T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j < shape(xs)[1];
//@ ensures xs[i,:][j] === xs[i,j];

//@ lemma SliceProjection <type T> (T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j < shape(xs)[1];
//@ ensures xs[i,:][j] === xs[i,j];

//@ axiom <type T> (T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j <= shape(xs)[1];
//@ ensures xs[i,:][:j] === xs[i,:j];

//@ lemma DoubleSlice <type T> (T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j <= shape(xs)[1];
//@ ensures xs[i,:][:j] === xs[i,:j];

//@ axiom <type T> (T x)
//@ ensures size({x}) === 1;
//@ ensures {x}[0] === x;

//@ lemma SingletonProjection <type T> (T x)
//@ ensures size({x}) === 1;
//@ ensures {x}[0] === x;

// array multiplication is commutative

//@ axiom (uint[[1]] xs, uint[[1]] ys)
//@ requires size(xs) === size(ys);
//@ ensures xs * ys === ys * xs;

//@ lemma ArrMulCommu (uint[[1]] xs, uint[[1]] ys)
//@ requires size(xs) === size(ys);
//@ ensures xs * ys === ys * xs;

// array multiplication is associative

//@ axiom (uint[[1]] xs, uint[[1]] ys, uint[[1]] zs)
//@ requires size(xs) === size(ys) && size(ys) === size(zs);
//@ ensures xs * (ys * zs) === (xs * ys) * zs;

//@ lemma ArrMulAssoc (uint[[1]] xs, uint[[1]] ys, uint[[1]] zs)
//@ requires size(xs) === size(ys) && size(ys) === size(zs);
//@ ensures xs * (ys * zs) === (xs * ys) * zs;

//@ lemma SumSliceEnd(uint[[1]] xs,uint i)
//@ requires size(xs) > 0;
//@ requires i < size(xs);
//@ ensures sum(xs[:i+1]) === sum(xs[:i]) + xs[i];

//@ lemma SumSliceBegin(uint[[1]] xs,uint i)
//@ requires size(xs) > 0;
//@ requires i < size(xs);
//@ ensures sum(xs[i:]) === xs[i] + sum(xs[i+1:]);



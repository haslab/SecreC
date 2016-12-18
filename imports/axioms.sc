#OPTIONS_SECREC --implicitcoercions=offc --ignorespecdomains

module axioms;

//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ requires size(xs) > 0;
//x //@ ensures assertion<D>(xs === snoc(init(xs),last(xs)));

//@ axiom <domain D,type T> (D T[[1]] xs)
//@ ensures size(xs) === size(multiset(xs));

//@ axiom <domain D,type T> (D T[[1]] xs)
//@ requires reclassify(xs) === {};
//@ ensures multiset(xs) === multiset{};

//x //@ axiom <domain D,type T> (D T[[1]] xs)
//x //@ ensures multiset(xs[:size(xs)]) === multiset(xs);
//x 
//x //@ axiom <domain D,type T> (D T[[1]] xs, uint i)
//x //@ requires 0 <= i && i < size(xs);
//x //@ ensures multiset(xs[:i+1]) === union(multiset(xs[:i]),multiset{xs[i]});
//x 
//x //@ axiom <domain D,type T> (D T[[1]] xs, D T[[1]] ys)
//x //@ ensures set(cat(xs,ys)) === union(set(xs),set(ys));

//@ axiom <domain D,type T> (D T x)
//@ ensures set({x}) === set{x};

//@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j < shape(xs)[1];
//@ ensures assertion<D>(xs[i,:][j] === xs[i,j]);

//@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j < shape(xs)[1];
//@ ensures assertion<D>(xs[:,j][i] === xs[i,j]);

//@ axiom <domain D,type T> (D T[[2]] xs, uint i, uint j)
//@ requires i < shape(xs)[0];
//@ requires j <= shape(xs)[1];
//@ ensures assertion<D>(xs[i,:][:j] === xs[i,:j]);

//@ axiom<domain D,type T> (D T x)
//@ ensures size({x}) === 1;
//@ ensures assertion<D>({x}[0] === x);

// multiplication is commutative
//@ axiom <domain D> (D uint[[1]] xs, D uint[[1]] ys)
//@ requires size(xs) === size(ys);
//@ ensures xs * ys === ys * xs;
    
// multiplication is associative
//@ axiom <domain D> (D uint[[1]] xs, D uint[[1]] ys, D uint[[1]] zs)
//@ requires size(xs) === size(ys) && size(ys) === size(zs);
//@ ensures xs * (ys * zs) === (xs * ys) * zs;


// workaround for empty modules
void empty() { }
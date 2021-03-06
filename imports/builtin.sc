#OPTIONS_SECREC --implicitcoercions=defaultsc --promote=nop

module builtin;

template <nonpublic kind K,domain D : K,type T,dim N>
function D T[[N]] classify (public T[[N]] x)
context<>
{
    __builtin("core.classify",x) :: D T[[N]]
}

template <nonpublic kind K,domain D : K,type T,dim N>
function T[[N]] declassify (D T[[N]] x)
context<>
{
    __builtin("core.declassify",x) :: T[[N]]
}

template <nonpublic kind K,domain D : K,type T,dim N>
function T[[N]] declassifyOut (D T[[N]] x)
context<>
{
    __builtin("core.declassifyOut",x) :: T[[N]]
}

//@ template <type T,dim N>
//@ function T[[N]] reclassify (T[[N]] x)
//@ context<>
//@ {
//@     __builtin("core.reclassify",x) :: T[[N]]
//@ }

template <domain D, type T, dim N>
function uint size (D T[[N]] x)
context<>
{
    __builtin("core.size",x) :: uint
}

//this repeat is a STUB 
template <domain D,type T,dim N>
function D T[[N]] repeat (D T x)
context<>
{
    __builtin("core.repeat",x) :: D T [[N]]
}

template <domain D,type T>
function D T[[size...(szs)]] repeat (D T x, uint... szs)
context<>
{
    __builtin("core.repeat",x,szs...) :: D T [[size...(szs)]]
}

template <domain D, type T, dim N>
function uint[[1]] shape (D T[[N]] arr)
context<>
{
    __builtin("core.shape",arr) :: uint[[1]]
}

// strlen

template <domain D>
function D uint strlen (D string str)
context<>
{
    __builtin("core.strlen",str) :: D uint
}

// tostring

template <domain D,type T>
function D string tostring (D T x)
context<>
{
    __builtin("core.tostring",x) :: D string
}

// addition

//@ template<type T1,dim N1>
//@ function set<T1[[N1]]> union (set<T1[[N1]]> x, set<T1[[N1]]> y)
//@ context<>
//@ {
//@     __builtin("core.union",x,y) :: set<T1[[N1]]>
//@ }

//@ template<type T1,dim N1>
//@ function multiset<T1[[N1]]> union (multiset<T1[[N1]]> x, multiset<T1[[N1]]> y)
//@ context<>
//@ {
//@     __builtin("core.union",x,y) :: multiset<T1[[N1]]>
//@ }

template<domain D, primitive type T>
function D T operator + (D T x,D T y)
context<>
{
    __builtin("core.add",x,y) :: D T
}

// variadic index sum
function uint sum()
context<>
{ 0 }

template <>
function uint sum (uint n, uint... ns)
{
    n + sum(ns...)
}

// absolute value

template <domain D, numeric type T>
function D T abs (D T x)
context<>
{
    __builtin("core.abs",x) :: D T
} 

// subtraction

template <domain D, numeric type T>
function D T operator - (D T x)
context<>
{
    __builtin("core.neg",x) :: D T
} 

template <domain D,numeric type T>
function D T operator - (D T x,D T y)
context<>
{
    __builtin("core.sub",x,y) :: D T
}

template<domain D, numeric type T>
function D T operator * (D T x,D T y)
context<>
{
    __builtin("core.mul",x,y) :: D T
} 

// variadic index product
function uint product()
context<>
{ 1 }

template <>
function uint product (uint n, uint... ns)
{
    n * product(ns...)
}

template<domain D, numeric type T>
function D T inv (D T x)
context<>
{
    __builtin("core.inv",x) :: D T
} 

// division

template<domain D, numeric type T>
function D T operator / (D T x,D T y)
context<>
{
    __builtin("core.div",x,y) :: D T
} 

// modulo

template<domain D, numeric type T>
function D T operator % (D T x,D T y)
context<>
{
    __builtin("core.mod",x,y) :: D T
}

// greater

template<domain D, primitive type T>
function D bool operator > (D T x,D T y)
context<>
{
    __builtin("core.gt",x,y) :: D bool
}

// smaller

template<domain D, primitive type T>
function D bool operator < (D T x,D T y)
context<>
{
    __builtin("core.lt",x,y) :: D bool
}

// greater or equal

template<domain D, primitive type T>
function D bool operator >= (D T x,D T y)
context<>
{
    __builtin("core.ge",x,y) :: D bool
} 

// smaller or equal

template<domain D, primitive type T>
function D bool operator <= (D T x,D T y)
context<>
{
    __builtin("core.le",x,y) :: D bool
} 

//@ template<type T>
//@ predicate operator <= (set<T> x, set<T> y)
//@ context<>
//@ {
//@     __builtin("core.subset",x,y) :: bool
//@ }

//@ template<type T>
//@ predicate operator <= (multiset<T> x, multiset<T> y)
//@ context<>
//@ {
//@     __builtin("core.subset",x,y) :: bool
//@ }

//@ template<type T1, dim N1>
//@ predicate in (T1[[N1]] x,set<T1[[N1]]> y)
//@ context<>
//@ {
//@     __builtin("core.in",x,y) :: bool
//@ }

//@ template<type T1, dim N1>
//@ predicate in (T1[[N1]] x, multiset<T1[[N1]]> y)
//@ context<>
//@ {
//@     __builtin("core.in",x,y) :: bool
//@ }

//@ template<type T, dim N { N > 0 }>
//@ function bool in (T x, T[[N]] y)
//@ context<>
//@ {
//@     __builtin("core.in",x,y) :: bool
//@ }

//@ template<type T>
//@ predicate operator >= (set<T> x, set<T> y)
//@ context<>
//@ {
//@     __builtin("core.subset",y,x) :: bool
//@ }

//@ template<type T>
//@ predicate operator >= (multiset<T> x, multiset<T> y)
//@ context<>
//@ {
//@     __builtin("core.subset",y,x) :: bool
//@ }

// equality

template<domain D,type T>
function D bool operator == (D T x,D T y)
context<>
{
    __builtin("core.eq",x,y) :: D bool
}

//@ template<type T,dim N>
//@ function bool operator === (T[[N]] x,T[[N]] y)
//@ context<>
//@ {
//@     __builtin("core.eq",x,y) :: bool
//@ } 

template<domain D, primitive type T>
function D bool operator != (D T x,D T y)
context<>
{
    __builtin("core.neq",x,y) :: D bool
} 

// logical operators

template <domain D>
function D bool operator ==> (D bool x,D bool y)
context<>
{
    __builtin("core.implies",x,y) :: D bool
}

template <domain D>
function D bool operator <==> (D bool x,D bool y)
context<>
{
    __builtin("core.eq",x,y) :: D bool
}

template <domain D>
function D bool operator && (D bool x,D bool y)
context<>
{
    __builtin("core.band",x,y) :: D bool
}

template <domain D>
function D bool operator || (D bool x,D bool y)
context<>
{
    __builtin("core.bor",x,y) :: D bool
}

template <domain D, type T >
D T[[size...(ns)]] reshape (D T val, uint... ns)
context<>
//@ inline;
{
    havoc D T[[size...(ns)]] ret;
    __syscall("core.reshape",val,ns...,__return ret);
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D T[[size...(ns)]] reshape (D T[[N]] arr, uint... ns)
context< /*@ uint product(ns...) @*/ >
//@ inline;
//@ requires product(ns...) === size(arr);
{
    havoc D T[[size...(ns)]] ret;
    __syscall("core.reshape",arr,ns...,__return ret);
    return ret;
}

template<domain D>
function D bool operator ! (D bool x)
context< D bool <~(bool) >
{
    (x==<~(false))
}

template<domain D>
function D bool operator (bool) (D bool x)
context<>
{
    x
}
template <domain D,numeric type T>
function D bool operator (bool) (D T x)
context<>
{
    __builtin("core.cast",x)
}
template <domain D,numeric type T>
function D T operator (T) (D bool x)
context<>
{
    __builtin("core.cast",x) :: D T
}
template <domain D,numeric type T1, numeric type T2>
function D T2 operator (T2) (D T1 x)
context<>
{
    __builtin("core.cast",x) :: D T2
}

// array operations

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator == (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator != (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] != y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator ! (D bool[[N]] x)
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = !x[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator && (D bool[[N]] x,D bool[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] && y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator || (D bool[[N]] x,D bool[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] || y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator + (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] + y[i];
    }
    return ret;
}


template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator - (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] - y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator - (D T[[N]] x)
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = -x[i];
    }
    return ret;
}

template <domain D, type T>
D T[[1]] operator * (D T[[1]] x,D T[[1]] y)
//@ requires size(x) === size(y);
//@ inline;
{
    D T [[1]] ret (size(x));
    for (uint i = 0; i < size(x); i=i+1)
    //@ free invariant 0 <= i && i <= size(x);
    //@ free invariant size(x) === size(y);
    //@ free invariant size(x) === size(ret);
    //@ free invariant size(x) === old(size(x));
    {
        ret[i] = x[i] * y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator * (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] * y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator >= (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] >= y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator <= (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] <= y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator > (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] > y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator < (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] < y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator / (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] / y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator % (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) === shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] % y[i];
    }
    return ret;
}

template <domain D, type X, type Y>
D Y[[1]] operator (Y) (D X[[1]] x)
//@ inline;
{
    D Y[[1]] ret (size(x));
    for (uint i = 0; i < size(x); i=i+1)
    //@ free invariant 0 <= i && i <= size(x);
    //@ free invariant 0 <= i && i <= size(ret);
    //@ free invariant size(ret) == size(x);
    {
        ret[i] = (Y) x[i];
    }
    return ret;
}

template <domain D, dim N { N > 0 }, type X, type Y>
D Y[[N]] operator (Y) (D X[[N]] x)
//@ inline;
{
    D Y[[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = (Y) x[i];
    }
    return ret;
}

//cat

template <domain D, type T>
function D T[[1]] cat (D T[[1]] x, D T[[1]] y)
context<>
//@ inline;
//@ free ensures size(\result) === size(x) + size(y);
{
    __builtin("core.cat", x,y) :: D T[[1]]
}

template <domain D, type T, dim N >
D T[[N]] cat (D T[[N]] x, D T[[N]] y, const uint n)
context<>
//@ inline;
//@ requires n < N;
//@ requires forall uint j ; 0 <= j && j < N && j != n ==> shape(x)[j] === shape(y)[j];
//@ free ensures forall uint j ; 0 <= j && j < N && j != n ==> shape(\result)[j] === shape(x)[j];
//@ free ensures shape(\result)[n] === shape(x)[n] + shape(y)[n];
{
    havoc D T[[N]] ret;
    __syscall("core.cat", x, y, n,__return ret);
    return ret;
}

template <domain D, type T, dim N>
D T[[N]] cat (D T[[N]] x, D T[[N]] y)
context<>
//@ inline;
{
    cat(x,y,0);
}

template<domain D,type T>
function D T[[1]] cons (D T x, D T[[1]] xs)
context<>
//@ inline;
//@ free ensures size(\result) === size(xs) + 1;
//@ free ensures forall uint i; i < size(xs) ==> \result[i+1] === xs[i];
//@ free ensures \result[0] === x;
{
    cat ({x},xs)
}

template<domain D,type T>
D T[[2]] cons (D T[[1]] x, D T[[2]] xs)
context<>
//@ inline;
//@ requires shape(xs)[1] === size(x);
//@ free ensures shape(\result)[0] === shape(xs)[0] + 1;
//@ free ensures shape(\result)[1] === shape(xs)[1];
//@ free ensures forall uint i; i < shape(xs)[0] ==> \result[i+1,:] === xs[i,:];
//@ free ensures \result[0,:] === x;
{
    cat (reshape(x,1,size(x)),xs);
}

template<domain D,type T>
function D T[[1]] snoc (D T[[1]] xs, D T x)
context<>
//@ inline;
//@ free ensures size(\result) === size(xs) + 1;
//@ free ensures forall uint i; i < size(xs) ==> \result[i] === xs[i];
//@ free ensures \result[size(xs)] === x;
{
    cat (xs, {x})
}

template<domain D,type T>
D T[[2]] snoc (D T[[2]] xs, D T[[1]] x)
context<>
//@ inline;
//@ requires shape(xs)[1] === size(x);
//@ free ensures shape(\result)[0] === shape(xs)[0] + 1;
//@ free ensures shape(\result)[1] === shape(xs)[1];
//@ free ensures forall uint i; i < shape(xs)[0] ==> \result[i,:] === xs[i,:];
//@ free ensures \result[shape(xs)[0],:] === x;
{
    cat (xs,reshape(x,1,size(x)));
}

template<domain D,type T>
function D T head (D T[[1]] xs)
context<>
//@ inline;
//@ requires size(xs) > 0;
{
    xs[0]
}

template<domain D,type T>
function D T[[1]] tail (D T[[1]] xs)
context<>
//@ inline;
//@ requires size(xs) > 0;
//@ free ensures size(\result) === size(xs) - 1;
//@ free ensures forall uint i; 0 < i && i < size(xs) ==> \result[i-1] === xs[i];
{
    xs[1:]
}

template<domain D,type T>
function D T[[1]] init (D T[[1]] xs)
context<>
//@ inline;
//@ requires size(xs) > 0;
//@ free ensures size(\result) === size(xs) - 1;
//@ free ensures forall uint i; i < size(xs)-1 ==> \result[i] === xs[i];
{
    xs[:size(xs)-1]
}

template<domain D,type T>
function D T last (D T[[1]] xs)
context<>
//@ inline;
//@ requires size(xs) > 0;
{
    xs[size(xs)-1]
}

template<domain D>
function D uint sum (D uint[[1]] xs)
context<>
//@ inline;
{
    __builtin("core.sum",xs) :: D uint
}


template<domain D>
function D float64 sum (D float64[[1]] xs)
context<>
//@ inline;
{
    __builtin("core.sum",xs) :: D float64
}

template <domain D >
function D uint[[1]] operator * (D uint[[1]] x,D uint[[1]] y)
context<>
//@ inline;
{
    __builtin("core.mul",x,y) :: D uint[[1]]
}

#OPTIONS_SECREC --implicitcoercions=defaultsc

module builtin;

template <nonpublic kind K,domain D : K,type T,dim N>
context<>
function D T[[N]] classify (public T[[N]] x)
context<>
{
    __builtin("core.classify",x) :: D T[[N]]
}

template <nonpublic kind K,domain D : K,type T,dim N>
context<>
function T[[N]] declassify (D T[[N]] x)
context<>
{
    __builtin("core.declassify",x) :: T[[N]]
}

template <domain D, type T, dim N>
context<>
function uint size (D T[[N]] x)
context<>
{
    __builtin("core.size",x) :: uint
}

//this repeat is a STUB 
template <domain D,type T,dim N>
context<>
function D T[[N]] repeat (D T x)
context<>
{
    __builtin("core.repeat",x) :: D T [[N]]
}

template <domain D,type T>
context<>
function D T[[size...(szs)]] repeat (D T x, uint... szs)
context<>
{
    __builtin("core.repeat",x,szs...) :: D T [[size...(szs)]]
}

template <domain D, type T, dim N>
context<>
function uint[[1]] shape (D T[[N]] arr)
context<>
{
    __builtin("core.shape",arr) :: uint[[1]]
}

// strlen

template <domain D>
context<>
function D uint strlen (D string str)
context<>
{
    __builtin("core.strlen",str) :: D uint
}

// tostring

template <domain D,type T>
context<>
function D string tostring (D T x)
context<>
{
    __builtin("core.tostring",x) :: D string
}

// addition

//@ template<domain D,type T>
//@ context<>
//@ function D multiset<T> operator + (D multiset<T> x, D multiset<T> y)
//@ context<>
//@ {
//@     __builtin("core.union",x,y) :: D multiset<T>
//@ }

template<domain D, primitive type T>
context<>
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

// subtraction

template <domain D, numeric type T>
context<>
function D T operator - (D T x)
context<>
{
    __builtin("core.neg",x) :: D T
} 

template <domain D,numeric type T>
context<>
function D T operator - (D T x,D T y)
context<>
{
    __builtin("core.sub",x,y) :: D T
}

template<domain D, numeric type T>
context<>
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

// division

template<domain D, numeric type T>
context<>
function D T operator / (D T x,D T y)
context<>
{
    __builtin("core.div",x,y) :: D T
} 

// modulo

template<domain D, numeric type T>
context<>
function D T operator % (D T x,D T y)
context<>
{
    __builtin("core.mod",x,y) :: D T
}

// greater

template<domain D, primitive type T>
context<>
function D bool operator > (D T x,D T y)
context<>
{
    __builtin("core.gt",x,y) :: D bool
}

// smaller

template<domain D, primitive type T>
context<>
function D bool operator < (D T x,D T y)
context<>
{
    __builtin("core.lt",x,y) :: D bool
}

// greater or equal

template<domain D, primitive type T>
context<>
function D bool operator >= (D T x,D T y)
context<>
{
    __builtin("core.ge",x,y) :: D bool
} 

// smaller or equal

template<domain D, primitive type T>
context<>
function D bool operator <= (D T x,D T y)
context<>
{
    __builtin("core.le",x,y) :: D bool
} 

//@ template<domain D,type T>
//@ context<>
//@ function D bool operator <= (D multiset<T> x, D multiset<T> y)
//@ context<>
//@ {
//@     __builtin("core.subset",x,y) :: D bool
//@ }

//@ template<domain D,type T>
//@ context<>
//@ function D bool in (D T x, D multiset<T> y)
//@ context<>
//@ {
//@     __builtin("core.in",x,y) :: D bool
//@ }

//@ template<domain D,type T>
//@ context<>
//@ function D bool in (D T x, D T[[1]] y)
//@ context<>
//@ {
//@     __builtin("core.in",x,y) :: D bool
//@ }

//@ template<domain D,type T>
//@ context<>
//@ function D bool operator >= (D multiset<T> x, D multiset<T> y)
//@ context<>
//@ {
//@     __builtin("core.subset",y,x) :: D bool
//@ }

// equality

template<domain D,type T>
context<>
function D bool operator == (D T x,D T y)
context<>
{
    __builtin("core.eq",x,y) :: D bool
}

//@ template<domain D,type T,dim N>
//@ context<>
//@ function D bool operator == (D T[[N]] x,D T[[N]] y)
//@ context<>
//@ {
//@     __builtin("core.eq",x,y) :: D bool
//@ } 

template<domain D, primitive type T>
context<>
function D bool operator != (D T x,D T y)
context<>
{
    __builtin("core.neq",x,y) :: D bool
} 

// logical operators

template <domain D>
context<>
function D bool operator ==> (D bool x,D bool y)
context<>
{
    __builtin("core.implies",x,y) :: D bool
}

template <domain D>
context<>
function D bool operator <==> (D bool x,D bool y)
context<>
{
    __builtin("core.eq",x,y) :: D bool
}

template <domain D>
context<>
function D bool operator && (D bool x,D bool y)
context<>
{
    __builtin("core.band",x,y) :: D bool
}

template <domain D>
context<>
function D bool operator || (D bool x,D bool y)
context<>
{
    __builtin("core.bor",x,y) :: D bool
}

template <domain D, type T, dim N>
context<>
function D T[[size...(ns)]] reshape (D T[[N]] arr, uint... ns)
context< /*@ uint sum(ns...) @*/ >
//@ requires sum(ns...) == size(arr);
{
    __builtin("core.reshape",arr,ns...) :: D T[[size...(ns)]]
}

function bool operator ! (bool x)
context<>
{
    (x==false)
}

template<domain D>
context<>
function D bool operator (bool) (D bool x)
context<>
{
    x
}
template <domain D,numeric type T>
context<>
function D bool operator (bool) (D T x)
context<>
{
    __builtin("core.cast",x)
}
template <domain D,numeric type T>
context<>
function D T operator (T) (D bool x)
context<>
{
    __builtin("core.cast",x) :: D T
}
template <domain D,numeric type T1, numeric type T2>
context<>
function D T2 operator (T2) (D T1 x)
context<>
{
    __builtin("core.cast",x) :: D T2
}

// array operations

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator == (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator != (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] != y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
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
context<>
D bool[[N]] operator && (D bool[[N]] x,D bool[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] && y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator || (D bool[[N]] x,D bool[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] || y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator + (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] + y[i];
    }
    return ret;
}


template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator - (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] - y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator - (D T[[N]] x)
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = -x[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator * (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] * y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator >= (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] >= y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator <= (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] <= y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator > (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] > y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator < (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D bool [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] < y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator / (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] / y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator % (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
//@ inline;
{
    D T [[N]] ret (shape(x)...N);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] % y[i];
    }
    return ret;
}

template <domain D, dim N { N > 0 }, type X, type Y>
context<>
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

template <domain D, type T, dim N>
context<>
function D T[[N]] cat (D T[[N]] x, D T[[N]] y, const uint n)
context<>
//@ requires n < N;
//@ requires forall uint j ; 0 <= j && j < N && j != n ==> shape(x)[j] == shape(y)[j];
//@ free ensures forall uint j ; 0 <= j && j < N && j != n ==> shape(\result)[j] == shape(x)[j];
//@ free ensures shape(\result)[n] == shape(x)[n] + shape(y)[n];
{

    __builtin("core.cat", x,y,n) :: D T[[N]]
}

template <domain D, type T, dim N>
context<>
function D T[[N]] cat (D T[[N]] x, D T[[N]] y)
context<>
{
    cat(x,y,0)
}
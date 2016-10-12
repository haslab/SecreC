#OPTIONS_SECREC --implicitcoercions=false
    
module builtin;

template <nonpublic kind K,domain D : K,type T,dim N>
function D T[[N]] classify (public T[[N]] x) {
    __builtin("core.classify",x) :: D T[[N]]
}

template <nonpublic kind K,domain D : K,type T,dim N>
function T[[N]] declassify (D T[[N]] x) {
    __builtin("core.declassify",x) :: T[[N]]
}

// strlen

template <domain D>
function D uint strlen (D string str) {
    __builtin("core.strlen",str) :: D uint
}

// tostring

template <domain D,type T>
function D string tostring (D T x) {
    __builtin("core.tostring",x) :: D string
}

// shape

template <domain D, type T, dim N>
function uint[[1]] shape (D T[[N]] arr) {
    __builtin("core.shape",arr) :: uint[[1]]
}

//cat

template <domain D, type T, dim N>
function D T[[N]] cat (D T[[N]] x, D T[[N]] y) {
    cat(x,y,0)
}

template <domain D, type T, dim N>
function D T[[N]] cat (D T[[N]] x, D T[[N]] y, const uint n)
//@ requires n < N;
//@ requires forall uint j ; 0 <= j && j < N && j != n ==> shape(x)[j] == shape(y)[j];
//@ free ensures forall uint j ; 0 <= j && j < N && j != n ==> shape(\result)[j] == shape(x)[j];
//@ free ensures shape(\result)[n] == shape(x)[n] + shape(y)[n];
{

    __builtin("core.cat", x,y,n) :: D T[[N]]
}

//this repeat is a STUB 
template <domain D,type T,dim N>
function D T[[N]] repeat (D T x) {
    __builtin("core.repeat",x) :: D T [[N]]
}

template <domain D,type T>
function D T[[size...(szs)]] repeat (D T x, const uint... szs)
{
    __builtin("core.repeat",x,szs...) :: D T [[size...(szs)]]
}

// size

template <domain D, type T, dim N>
function uint size (D T[[N]] x) {
    __builtin("core.size",x) :: uint
}

// logical operators

template <domain D>
function D bool operator ==> (D bool x,D bool y) {
    __builtin("core.implies",x,y) :: D bool
}

template <domain D>
function D bool operator <==> (D bool x,D bool y) {
    __builtin("core.eq",x,y) :: D bool
}

template <domain D>
function D bool operator && (D bool x,D bool y) {
    __builtin("core.band",x,y) :: D bool
}

template <domain D, dim N { N > 0 }>
D bool[[N]] operator && (D bool[[N]] x,D bool[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D bool[[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] && y[i];
    }
    return ret;
}

template <domain D>
function D bool operator || (D bool x,D bool y) {
    __builtin("core.bor",x,y) :: D bool
}

template <domain D, dim N { N > 0 } >
D bool[[N]] operator || (D bool[[N]] x,D bool[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D bool [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] || y[i];
    }
    return ret;
}

// unary subtraction

template <domain D, numeric type T>
function D T operator - (D T x) {
    __builtin("core.neg",x) :: D T
} 

// unary array subtraction

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator - (D T[[N]] x) {
    havoc D T [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = - x[i];
    }
    return ret;
}

// subtraction

template <domain D,numeric type T>
function D T operator - (D T x,D T y) {
    __builtin("core.sub",x,y) :: D T
}

// array subtraction

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator - (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D T [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] - y[i];
    }
    return ret;
}

// addition

//@ template<domain D,type T>
//@ function D multiset<T> operator + (D multiset<T> x, D multiset<T> y)
//@ {
//@     __builtin("core.union",x,y) :: D multiset<T>
//@ }

template<domain D, primitive type T>
function D T operator + (D T x,D T y) {
    __builtin("core.add",x,y) :: D T
}

// array addition

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator + (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D T [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] + y[i];
    }
    return ret;
}

// multiplication

template<domain D, numeric type T>
function D T operator * (D T x,D T y) {
    __builtin("core.mul",x,y) :: D T
} 

// array multiplication

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator * (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D T [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] * y[i];
    }
    return ret;
}


// division

template<domain D, numeric type T>
function D T operator / (D T x,D T y) {
    __builtin("core.div",x,y) :: D T
} 

// array division

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator / (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D T [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] / y[i];
    }
    return ret;
}

// modulo

template<domain D, numeric type T>
function D T operator % (D T x,D T y) {
    __builtin("core.mod",x,y) :: D T
}

// array modulo

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator % (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D T [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] % y[i];
    }
    return ret;
}

// greater

template<domain D, primitive type T>
function D bool operator > (D T x,D T y) {
    __builtin("core.gt",x,y) :: D bool
}

// array greater

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator > (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D bool [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] > y[i];
    }
    return ret;
}

// smaller

template<domain D, primitive type T>
function D bool operator < (D T x,D T y) {
    __builtin("core.lt",x,y) :: D bool
}

// array smaller

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator < (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D bool [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] < y[i];
    }
    return ret;
}

// greater or equal

template<domain D, primitive type T>
function D bool operator >= (D T x,D T y) {
    __builtin("core.ge",x,y) :: D bool
} 

// array greater or equal

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator >= (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D bool [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] >= y[i];
    }
    return ret;
}

// smaller or equal

template<domain D, primitive type T>
function D bool operator <= (D T x,D T y) {
    __builtin("core.le",x,y) :: D bool
} 

// array greater

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator <= (D T[[N]] x, D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D bool [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] <= y[i];
    }
    return ret;
}

//@ template<domain D,type T>
//@ function D bool operator <= (D multiset<T> x, D multiset<T> y)
//@ {
//@     __builtin("core.subset",x,y) :: D bool
//@ }

//@ template<domain D,type T>
//@ function D bool in (D T x, D multiset<T> y)
//@ {
//@     __builtin("core.in",x,y) :: D bool
//@ }

//@ template<domain D,type T>
//@ function D bool in (D T x, D T[[1]] y)
//@ {
//@     __builtin("core.in",x,y) :: D bool
//@ }

//@ template<domain D,type T>
//@ function D bool operator >= (D multiset<T> x, D multiset<T> y)
//@ {
//@     __builtin("core.subset",y,x) :: D bool
//@ }

// equal

//@ template<domain D,type T,dim N>
//@ function D bool operator == (D T[[N]] x,D T[[N]] y) {
//@     __builtin("core.eq",x,y) :: D bool
//@ } 

template<domain D,type T>
function D bool operator == (D T x,D T y) {
    __builtin("core.eq",x,y) :: D bool
} 

// array equal

template <domain D, type T>
D bool[[1]] operator == (D T[[1]] x,D T[[1]] y)
//@ requires size(x) == size(y);
{

    havoc D bool[[1]] ret;
    for (uint i = 0; i < size(x); i=i+1) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator == (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    D bool [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}

// not equal

template<domain D, primitive type T>
function D bool operator != (D T x,D T y) {
    __builtin("core.neq",x,y) :: D bool
} 

// array not equal

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator != (D T[[N]] x,D T[[N]] y)
//@ requires shape(x) == shape(y);
{
    havoc D bool [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] != y[i];
    }
    return ret;
}

function bool operator ! (bool x) {
    (x==false)
}

template <domain D,dim N { N > 0 }>
D bool[[N]] operator ! (D bool[[N]] x) {
    
    havoc D bool [[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = !x[i];
    }
    return ret;
}

// casts

template<domain D>
function D bool operator (bool) (D bool x) {
    x
}
template <domain D,numeric type T>
function D bool operator (bool) (D T x) {
    __builtin("core.cast",x)
}
template <domain D,numeric type T>
function D T operator (T) (D bool x) {
    __builtin("core.cast",x) :: D T
}
template <domain D,numeric type T1, numeric type T2>
function D T2 operator (T2) (D T1 x) {
    __builtin("core.cast",x) :: D T2
}

// array casts
template <domain D, dim N { N > 0 }, type X, type Y>
D Y[[N]] operator (Y) (D X[[N]] x) {
    havoc D Y[[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = (Y) x[i];
    }
    return ret;
}

// variadic index sum
//@ function uint sum() { 0 }

//@ template <>
//@ function uint sum (uint n, uint... ns) {
//@     n + sum(ns...)
//@ }

// reshape

template <domain D, type T, dim N>
function D T[[size...(ns)]] reshape (D T[[N]] arr, const uint... ns)
//@ requires sum(ns...) == size(arr);
{
    __builtin("core.reshape",arr,ns...) :: D T[[size...(ns)]]
}
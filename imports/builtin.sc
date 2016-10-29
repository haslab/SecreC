#OPTIONS_SECREC --implicitcoercions=false
    
module builtin;

import primitives;

// array equal

template <domain D, type T>
context<>
D bool[[1]] operator == (D T[[1]] x,D T[[1]] y)
context< D bool == (D T, D T) >
//@ requires size(x) == size(y);
{

    D bool[[1]] ret (size(x));
    for (uint i = 0; i < size(x); i=i+1) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator == (D T[[N]] x,D T[[N]] y)
context< D bool[[N-1]] == (D T[[N-1]], D T[[N-1]]) >
//@ requires shape(x) == shape(y);
{
    D bool [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}

// not equal

template<domain D, primitive type T>
context<>
function D bool operator != (D T x,D T y)
context<>
{
    __builtin("core.neq",x,y) :: D bool
} 

// array not equal

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator != (D T[[N]] x,D T[[N]] y)
context< D bool[[N-1]] != (D T[[N-1]], D T[[N-1]]) >
//@ requires shape(x) == shape(y);
{
    D bool [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] != y[i];
    }
    return ret;
}

function bool operator ! (bool x)
context<>
{
    (x==false)
}

template <domain D,dim N { N > 0 }>
context<>
D bool[[N]] operator ! (D bool[[N]] x)
context< D bool[[N-1]] ! (D bool[[N-1]]) >
{
    
    D bool [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = !x[i];
    }
    return ret;
}

// casts

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

// array casts
template <domain D, dim N { N > 0 }, type X, type Y>
context<>
D Y[[N]] operator (Y) (D X[[N]] x)
context<>
{
    D Y[[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = (Y) x[i];
    }
    return ret;
}

// variadic index sum
function uint sum()
context<>
{ 0 }

template <>
context<>
function uint sum (uint n, uint... ns)
context<>
{
    n + sum(ns...)
}

// reshape

template <domain D, type T, dim N>
context<>
function D T[[size...(ns)]] reshape (D T[[N]] arr, const uint... ns)
context<>
//@ requires sum(ns...) == size(arr);
{
    __builtin("core.reshape",arr,ns...) :: D T[[size...(ns)]]
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

template <domain D, dim N { N > 0 }>
context<>
D bool[[N]] operator && (D bool[[N]] x,D bool[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D bool[[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] && y[i];
    }
    return ret;
}

template <domain D, dim N { N > 0 } >
context<>
D bool[[N]] operator || (D bool[[N]] x,D bool[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D bool [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] || y[i];
    }
    return ret;
}

// unary array subtraction

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator - (D T[[N]] x)
context<>
{
    D T [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = - x[i];
    }
    return ret;
}

// array subtraction

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator - (D T[[N]] x,D T[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D T [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] - y[i];
    }
    return ret;
}

// array addition

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator + (D T[[N]] x,D T[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D T [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] + y[i];
    }
    return ret;
}

// array multiplication

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator * (D T[[N]] x,D T[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D T [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] * y[i];
    }
    return ret;
}

// array division

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator / (D T[[N]] x,D T[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D T [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] / y[i];
    }
    return ret;
}

// array modulo

template <domain D, type T, dim N { N > 0 } >
context<>
D T[[N]] operator % (D T[[N]] x,D T[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D T [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] % y[i];
    }
    return ret;
}

// array greater

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator > (D T[[N]] x,D T[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D bool [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] > y[i];
    }
    return ret;
}

// array smaller

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator < (D T[[N]] x,D T[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D bool [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] < y[i];
    }
    return ret;
}

// array greater or equal

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator >= (D T[[N]] x,D T[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D bool [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] >= y[i];
    }
    return ret;
}

// array greater

template <domain D, type T, dim N { N > 0 } >
context<>
D bool[[N]] operator <= (D T[[N]] x, D T[[N]] y)
context<>
//@ requires shape(x) == shape(y);
{
    D bool [[N]] ret (shape(x)...);
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = x[i] <= y[i];
    }
    return ret;
}
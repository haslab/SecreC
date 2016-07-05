    
module builtin;

// we support ghost equality over any type
//@ template<domain D, type T, dim N>
//@ function D bool operator == (D T[[N]] x,D T[[N]] y) {
//@     __builtin("core.eq",x,y) :: D bool
//@ } 

//@ template<domain D>
//@ function D bool operator || (D bool x,D bool y) {
//@     __builtin("core.bor",x,y) :: D bool
//@ }

//@ template <nonpublic kind K,domain D : K,type T,dim N>
//@ function D T[[N]] classify (public T[[N]] x) {
//@     __builtin("core.classify",x) :: D T[[N]]
//@ }

//@ template <domain D, type T, dim N>
//@ function uint size (D T[[N]] x) {
//@     __builtin("core.size",x)
//@ }

//@ template <domain D>
//@ function D bool operator ==> (D bool x,D bool y) {
//@     __builtin("core.implies",x,y) :: D bool
//@ }

//@ template <domain D>
//@ function D bool operator <==> (D bool x,D bool y) {
//@     __builtin("core.eq",x,y) :: D bool
//@ }

//@ template<domain D>
//@ function D bool operator && (D bool x,D bool y) {
//@     __builtin("core.band",x,y) :: D bool
//@ }

//@ template <domain D, type T, dim N>
//@ function uint[[1]] shape (D T[[N]] arr) {
//@     __builtin("core.shape",arr) :: uint[[1]]
//@ }

// classify
template <domain D,type T,dim N { N > 0} >
D T[[N]] classify (public T[[N]] x)
//@ free ensures \result == classify(x);
{
    havoc D T[[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1)
    {
        ret[i] = classify(x[i]);
    }
    return ret;
}

//@ template <nonpublic kind K,domain D : K,type T,dim N>
//@ function public T[[N]] declassify (D T[[N]] x) {
//@     __builtin("core.declassify",x) :: public T[[N]]
//@ }

// declassify
template <domain D,type T,dim N { N > 0 }>
public T[[N]] declassify (D T[[N]] x)
//@ free ensures \result == declassify(x);
{
    havoc public T[[N]] ret;
    for (uint i = 0; i < shape(x)[0]; i=i+1) {
        ret[i] = declassify(x[i]);
    }
    return ret;
}

// strlen

function uint strlen (string str) {
    __builtin("core.strlen",str)
}

// tostring

template <type T>
function string tostring (public T x) {
    __builtin("core.tostring",x)
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

//@ template <domain D,type T,dim N>
//@ function D T[[N]] cat (D T[[N]] x, D T[[N]] y) {
//@     cat(x,y,0) :: D T[[N]]
//@ }

template <domain D, type T, dim N>
function D T[[N]] cat (D T[[N]] x, D T[[N]] y, const uint n)
//@ requires n < N;
{

    __builtin("core.cat", x,y,n) :: D T[[N]]
}

//@ template <domain D,type T,dim N>
//@ function D T[[N]] cat (D T[[N]] x, D T[[N]] y, const uint n)
//@ requires n < N;
//@ {
//@     __builtin("core.cat",x,y,n) :: D T[[N]]
//@ }

// reshape

template <domain D, type T, dim N>
function D T[[size...(ns)]] reshape (D T[[N]] arr, uint... ns) {
    __builtin("core.reshape",arr,ns) :: D T[[size...(ns)]]
}

//this repeat is a STUB 
template <domain D,type T,dim N>
function D T[[N]] repeat (D T x) {
    __builtin("core.repeat",x) :: D T [[N]]
}

template <domain D,type T,dim N>
function D T[[N]] repeat (D T x, uint sz) {
    __builtin("core.repeat",x,sz) :: D T [[N]]
}

// size

template <domain D, type T, dim N>
function uint size (D T[[N]] x) {
    __builtin("core.size",x)
}

// logical operators

function bool operator ==> (bool x,bool y) {
    __builtin("core.implies",x,y)
}

function bool operator <==> (bool x,bool y) {
    __builtin("core.eq",x,y)
}

function bool operator && (bool x,bool y) {
    __builtin("core.band",x,y)
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

function bool operator || (bool x,bool y) {
    __builtin("core.bor",x,y)
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

function int8 operator - (int8 x) {
    __builtin("core.neg",x)
} 
function int16 operator - (int16 x) {
    __builtin("core.neg",x)
} 
function int32 operator - (int32 x) {
    __builtin("core.neg",x)
} 
function int64 operator - (int64 x) {
    __builtin("core.neg",x)
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

function int8 operator - (int8 x,int8 y) {
    __builtin("core.sub",x,y)
} 
function int16 operator - (int16 x,int16 y) {
    __builtin("core.sub",x,y)
} 
function int32 operator - (int32 x,int32 y) {
    __builtin("core.sub",x,y)
} 
function int64 operator - (int64 x,int64 y) {
    __builtin("core.sub",x,y)
}
function uint8 operator - (uint8 x,uint8 y) {
    __builtin("core.sub",x,y)
} 
function uint16 operator - (uint16 x,uint16 y) {
    __builtin("core.sub",x,y)
} 
function uint32 operator - (uint32 x,uint32 y) {
    __builtin("core.sub",x,y)
} 
function uint64 operator - (uint64 x,uint64 y) {
    __builtin("core.sub",x,y)
} 
function float32 operator - (float32 x,float32 y) {
    __builtin("core.sub",x,y)
} 
function float64 operator - (float64 x,float64 y) {
    __builtin("core.sub",x,y)
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

//@ template<domain D>
//@ function D int8 operator + (D int8 x,D int8 y) {
//@     __builtin("core.add",x,y) :: D int8
//@ } 
//@ template<domain D>
//@ function D int16 operator + (D int16 x,D int16 y) {
//@     __builtin("core.add",x,y) :: D int16
//@ } 
//@ template<domain D>
//@ function D int32 operator + (D int32 x,D int32 y) {
//@     __builtin("core.add",x,y) :: D int32
//@ } 
//@ template<domain D>
//@ function D int64 operator + (D int64 x,D int64 y) {
//@     __builtin("core.add",x,y) :: D int64
//@ }
//@ template<domain D>
//@ function D uint8 operator + (D uint8 x,D uint8 y) {
//@     __builtin("core.add",x,y) :: D uint8
//@ } 
//@ template<domain D>
//@ function D uint16 operator + (D uint16 x,D uint16 y) {
//@     __builtin("core.add",x,y) :: D uint16
//@ } 
//@ template<domain D>
//@ function D uint32 operator + (D uint32 x,D uint32 y) {
//@     __builtin("core.add",x,y) :: D uint32
//@ } 
//@ template<domain D>
//@ function D uint64 operator + (D uint64 x,D uint64 y) {
//@     __builtin("core.add",x,y) :: D uint64
//@ } 
//@ template<domain D>
//@ function D float32 operator + (D float32 x,D float32 y) {
//@     __builtin("core.add",x,y) :: D float32
//@ } 
//@ template<domain D>
//@ function D float64 operator + (D float64 x,D float64 y) {
//@     __builtin("core.add",x,y) :: D float64
//@ }

function int8 operator + (int8 x,int8 y) {
    __builtin("core.add",x,y)
} 
function int16 operator + (int16 x,int16 y) {
    __builtin("core.add",x,y)
} 
function int32 operator + (int32 x,int32 y) {
    __builtin("core.add",x,y)
} 
function int64 operator + (int64 x,int64 y) {
    __builtin("core.add",x,y)
}
function uint8 operator + (uint8 x,uint8 y) {
    __builtin("core.add",x,y)
} 
function uint16 operator + (uint16 x,uint16 y) {
    __builtin("core.add",x,y)
} 
function uint32 operator + (uint32 x,uint32 y) {
    __builtin("core.add",x,y)
} 
function uint64 operator + (uint64 x,uint64 y) {
    __builtin("core.add",x,y)
} 
function float32 operator + (float32 x,float32 y) {
    __builtin("core.add",x,y)
} 
function float64 operator + (float64 x,float64 y) {
    __builtin("core.add",x,y)
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

function int8 operator * (int8 x,int8 y) {
    __builtin("core.mul",x,y)
} 
function int16 operator * (int16 x,int16 y) {
    __builtin("core.mul",x,y)
} 
function int32 operator * (int32 x,int32 y) {
    __builtin("core.mul",x,y)
} 
function int64 operator * (int64 x,int64 y) {
     __builtin("core.mul",x,y)
}
function uint8 operator * (uint8 x,uint8 y) {
    __builtin("core.mul",x,y)
} 
function uint16 operator * (uint16 x,uint16 y) {
    __builtin("core.mul",x,y)
} 
function uint32 operator * (uint32 x,uint32 y) {
    __builtin("core.mul",x,y)
} 
function uint64 operator * (uint64 x,uint64 y) {
    __builtin("core.mul",x,y)
} 
function float32 operator * (float32 x,float32 y) {
    __builtin("core.mul",x,y)
} 
function float64 operator * (float64 x,float64 y) {
    __builtin("core.mul",x,y)
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

function int8 operator / (int8 x,int8 y) {
    __builtin("core.div",x,y)
} 
function int16 operator / (int16 x,int16 y) {
    __builtin("core.div",x,y)
} 
function int32 operator / (int32 x,int32 y) {
    __builtin("core.div",x,y)
} 
function int64 operator / (int64 x,int64 y) {
    __builtin("core.div",x,y)
}
function uint8 operator / (uint8 x,uint8 y) {
    __builtin("core.div",x,y)
} 
function uint16 operator / (uint16 x,uint16 y) {
    __builtin("core.div",x,y)
} 
function uint32 operator / (uint32 x,uint32 y) {
    __builtin("core.div",x,y)
} 
function uint64 operator / (uint64 x,uint64 y) {
    __builtin("core.div",x,y)
} 
function float32 operator / (float32 x,float32 y) {
    __builtin("core.div",x,y)
} 
function float64 operator / (float64 x,float64 y) {
    __builtin("core.div",x,y)
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

function int8 operator % (int8 x,int8 y) {
    __builtin("core.mod",x,y)
} 
function int16 operator % (int16 x,int16 y) {
    __builtin("core.mod",x,y)
} 
function int32 operator % (int32 x,int32 y) {
    __builtin("core.mod",x,y)
} 
function int64 operator % (int64 x,int64 y) {
    __builtin("core.mod",x,y)
}
function uint8 operator % (uint8 x,uint8 y) {
    __builtin("core.mod",x,y)
} 
function uint16 operator % (uint16 x,uint16 y) {
    __builtin("core.mod",x,y)
} 
function uint32 operator % (uint32 x,uint32 y) {
    __builtin("core.mod",x,y)
} 
function uint64 operator % (uint64 x,uint64 y) {
    __builtin("core.mod",x,y)
} 
function float32 operator % (float32 x,float32 y) {
    __builtin("core.mod",x,y)
} 
function float64 operator % (float64 x,float64 y) {
    __builtin("core.mod",x,y)
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

//@ template<domain D>
//@ function D bool operator > (D int8 x,D int8 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator > (D int16 x,D int16 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator > (D int32 x,D int32 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator > (D int64 x,D int64 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ }
//@ template<domain D>
//@ function D bool operator > (D uint8 x,D uint8 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator > (D uint16 x,D uint16 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator > (D uint32 x,D uint32 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator > (D uint64 x,D uint64 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator > (D float32 x,D float32 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator > (D float64 x,D float64 y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator > (D bool x,D bool y) {
//@     __builtin("core.gt",x,y) :: D bool
//@ } 

function bool operator > (int8 x,int8 y) {
    __builtin("core.gt",x,y)
} 
function bool operator > (int16 x,int16 y) {
    __builtin("core.gt",x,y)
} 
function bool operator > (int32 x,int32 y) {
    __builtin("core.gt",x,y)
} 
function bool operator > (int64 x,int64 y) {
    __builtin("core.gt",x,y)
}
function bool operator > (uint8 x,uint8 y) {
    __builtin("core.gt",x,y)
} 
function bool operator > (uint16 x,uint16 y) {
    __builtin("core.gt",x,y)
} 
function bool operator > (uint32 x,uint32 y) {
    __builtin("core.gt",x,y)
} 
function bool operator > (uint64 x,uint64 y) {
    __builtin("core.gt",x,y)
} 
function bool operator > (float32 x,float32 y) {
    __builtin("core.gt",x,y)
} 
function bool operator > (float64 x,float64 y) {
    __builtin("core.gt",x,y)
} 
function bool operator > (bool x,bool y) {
    __builtin("core.gt",x,y)
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

//@ template<domain D>
//@ function D bool operator < (D int8 x,D int8 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator < (D int16 x,D int16 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator < (D int32 x,D int32 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator < (D int64 x,D int64 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ }
//@ template<domain D>
//@ function D bool operator < (D uint8 x,D uint8 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator < (D uint16 x,D uint16 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator < (D uint32 x,D uint32 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator < (D uint64 x,D uint64 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator < (D float32 x,D float32 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator < (D float64 x,D float64 y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator < (D bool x,D bool y) {
//@     __builtin("core.lt",x,y) :: D bool
//@ } 

function bool operator < (int8 x,int8 y) {
    __builtin("core.lt",x,y)
} 
function bool operator < (int16 x,int16 y) {
    __builtin("core.lt",x,y)
} 
function bool operator < (int32 x,int32 y) {
    __builtin("core.lt",x,y)
} 
function bool operator < (int64 x,int64 y) {
    __builtin("core.lt",x,y)
}
function bool operator < (uint8 x,uint8 y) {
    __builtin("core.lt",x,y)
} 
function bool operator < (uint16 x,uint16 y) {
    __builtin("core.lt",x,y)
} 
function bool operator < (uint32 x,uint32 y) {
    __builtin("core.lt",x,y)
} 
function bool operator < (uint64 x,uint64 y) {
    __builtin("core.lt",x,y)
} 
function bool operator < (float32 x,float32 y) {
    __builtin("core.lt",x,y)
} 
function bool operator < (float64 x,float64 y) {
    __builtin("core.lt",x,y)
} 
function bool operator < (bool x,bool y) {
    __builtin("core.lt",x,y)
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

//@ template<domain D>
//@ function D bool operator >= (D int8 x,D int8 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator >= (D int16 x,D int16 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator >= (D int32 x,D int32 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator >= (D int64 x,D int64 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ }
//@ template<domain D>
//@ function D bool operator >= (D uint8 x,D uint8 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator >= (D uint16 x,D uint16 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator >= (D uint32 x,D uint32 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator >= (D uint64 x,D uint64 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator >= (D float32 x,D float32 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator >= (D float64 x,D float64 y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator >= (D bool x,D bool y) {
//@     __builtin("core.ge",x,y) :: D bool
//@ } 

function bool operator >= (int8 x,int8 y) {
    __builtin("core.ge",x,y)
} 
function bool operator >= (int16 x,int16 y) {
    __builtin("core.ge",x,y)
} 
function bool operator >= (int32 x,int32 y) {
    __builtin("core.ge",x,y)
} 
function bool operator >= (int64 x,int64 y) {
    __builtin("core.ge",x,y)
}
function bool operator >= (uint8 x,uint8 y) {
    __builtin("core.ge",x,y)
} 
function bool operator >= (uint16 x,uint16 y) {
    __builtin("core.ge",x,y)
} 
function bool operator >= (uint32 x,uint32 y) {
    __builtin("core.ge",x,y)
} 
function bool operator >= (uint64 x,uint64 y) {
    __builtin("core.ge",x,y)
} 
function bool operator >= (float32 x,float32 y) {
    __builtin("core.ge",x,y)
} 
function bool operator >= (float64 x,float64 y) {
    __builtin("core.ge",x,y)
} 
function bool operator >= (bool x,bool y) {
    __builtin("core.ge",x,y)
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

//@ template<domain D>
//@ function D bool operator <= (D int8 x,D int8 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator <= (D int16 x,D int16 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator <= (D int32 x,D int32 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator <= (D int64 x,D int64 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ }
//@ template<domain D>
//@ function D bool operator <= (D uint8 x,D uint8 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator <= (D uint16 x,D uint16 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator <= (D uint32 x,D uint32 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator <= (D uint64 x,D uint64 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator <= (D float32 x,D float32 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator <= (D float64 x,D float64 y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 
//@ template<domain D>
//@ function D bool operator <= (D bool x,D bool y) {
//@     __builtin("core.le",x,y) :: D bool
//@ } 

function bool operator <= (int8 x,int8 y) {
    __builtin("core.le",x,y)
} 
function bool operator <= (int16 x,int16 y) {
    __builtin("core.le",x,y)
} 
function bool operator <= (int32 x,int32 y) {
    __builtin("core.le",x,y)
} 
function bool operator <= (int64 x,int64 y) {
    __builtin("core.le",x,y)
}
function bool operator <= (uint8 x,uint8 y) {
    __builtin("core.le",x,y)
} 
function bool operator <= (uint16 x,uint16 y) {
    __builtin("core.le",x,y)
} 
function bool operator <= (uint32 x,uint32 y) {
    __builtin("core.le",x,y)
} 
function bool operator <= (uint64 x,uint64 y) {
    __builtin("core.le",x,y)
} 
function bool operator <= (float32 x,float32 y) {
    __builtin("core.le",x,y)
} 
function bool operator <= (float64 x,float64 y) {
    __builtin("core.le",x,y)
} 
function bool operator <= (bool x,bool y) {
    __builtin("core.le",x,y)
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

function bool operator == (int8 x,int8 y) {
    __builtin("core.eq",x,y)
} 
function bool operator == (int16 x,int16 y) {
    __builtin("core.eq",x,y)
} 
function bool operator == (int32 x,int32 y) {
    __builtin("core.eq",x,y)
} 
function bool operator == (int64 x,int64 y) {
    __builtin("core.eq",x,y)
}
function bool operator == (uint8 x,uint8 y) {
    __builtin("core.eq",x,y)
} 
function bool operator == (uint16 x,uint16 y) {
    __builtin("core.eq",x,y)
} 
function bool operator == (uint32 x,uint32 y) {
    __builtin("core.eq",x,y)
} 
function bool operator == (uint64 x,uint64 y) {
    __builtin("core.eq",x,y)
} 
function bool operator == (float32 x,float32 y) {
    __builtin("core.eq",x,y)
} 
function bool operator == (float64 x,float64 y) {
    __builtin("core.eq",x,y)
} 
function bool operator == (bool x,bool y) {
    __builtin("core.eq",x,y)
} 

// array equal

template <domain D, type T>
D bool[[1]] operator == (D T[[1]] x,D T[[1]] y)
//@ requires shape(x) == shape(y);
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

function bool operator != (int8 x,int8 y) {
    __builtin("core.neq",x,y)
} 
function bool operator != (int16 x,int16 y) {
    __builtin("core.neq",x,y)
} 
function bool operator != (int32 x,int32 y) {
    __builtin("core.neq",x,y)
} 
function bool operator != (int64 x,int64 y) {
    __builtin("core.neq",x,y)
}
function bool operator != (uint8 x,uint8 y) {
    __builtin("core.neq",x,y)
} 
function bool operator != (uint16 x,uint16 y) {
    __builtin("core.neq",x,y)
} 
function bool operator != (uint32 x,uint32 y) {
    __builtin("core.neq",x,y)
} 
function bool operator != (uint64 x,uint64 y) {
    __builtin("core.neq",x,y)
} 
function bool operator != (float32 x,float32 y) {
    __builtin("core.neq",x,y)
} 
function bool operator != (float64 x,float64 y) {
    __builtin("core.neq",x,y)
} 
function bool operator != (bool x,bool y) {
    __builtin("core.neq",x,y)
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
    return size(x) > 0 ? cat({!x[0]},!x[1:]) : {};
}

// casts

// to bool
function bool operator (bool) (bool x) {
    x
}
function bool operator (bool) (uint8 x) {
    __builtin("core.cast_uint8_bool",x)
}
function bool operator (bool) (uint16 x) {
    __builtin("core.cast_uint16_bool",x)
}
function bool operator (bool) (uint32 x) {
    __builtin("core.cast_uint32_bool",x)
}
function bool operator (bool) (uint64 x) {
    __builtin("core.cast_uint64_bool",x)
}
function bool operator (bool) (int8 x) {
    __builtin("core.cast_int8_bool",x)
}
function bool operator (bool) (int16 x) {
    __builtin("core.cast_int16_bool",x)
}
function bool operator (bool) (int32 x) {
    __builtin("core.castuint32_bool",x)
}
function bool operator (bool) (int64 x) {
    __builtin("core.cast_int64_bool",x)
}
function bool operator (bool) (float32 x) {
    __builtin("core.cast_float32_bool",x)
}
function bool operator (bool) (float64 x) {
    __builtin("core.cast_float64_bool",x)
}

// to uint8
function uint8 operator (uint8) (bool x) {
    __builtin("core.cast_bool_uint8",x)
}
function uint8 operator (uint8) (uint8 x) {
    x
}
function uint8 operator (uint8) (uint16 x) {
    __builtin("core.cast_uint16_uint8",x)
}
function uint8 operator (uint8) (uint32 x) {
    __builtin("core.cast_uint32_uint8",x)
}
function uint8 operator (uint8) (uint64 x) {
    __builtin("core.cast_uint64_uint8",x)
}
function uint8 operator (uint8) (int8 x) {
    __builtin("core.cast_int8_uint8",x)
}
function uint8 operator (uint8) (int16 x) {
    __builtin("core.cast_int16_uint8",x)
}
function uint8 operator (uint8) (int32 x) {
    __builtin("core.cast_int32_uint8",x)
}
function uint8 operator (uint8) (int64 x) {
    __builtin("core.cast_int64_uint8",x)
}
function uint8 operator (uint8) (float32 x) {
    __builtin("core.cast_float32_uint8",x)
}
function uint8 operator (uint8) (float64 x) {
    __builtin("core.cast_float64_uint8",x)
}

// to uint16
function uint16 operator (uint16) (bool x) {
    __builtin("core.cast_bool_uint16",x)
}
function uint16 operator (uint16) (uint8 x) {
    __builtin("core.cast_uint8_uint16",x)
}
function uint16 operator (uint16) (uint16 x) {
    x
}
function uint16 operator (uint16) (uint32 x) {
    __builtin("core.cast_uint32_uint16",x)
}
function uint16 operator (uint16) (uint64 x) {
    __builtin("core.cast_uint64_uint16",x)
}
function uint16 operator (uint16) (int8 x) {
    __builtin("core.cast_uint8_uint16",x)
}
function uint16 operator (uint16) (int16 x) {
    __builtin("core.cast_int16_uint16",x)
}
function uint16 operator (uint16) (int32 x) {
    __builtin("core.cast_int32_uint16",x)
}
function uint16 operator (uint16) (int64 x) {
    __builtin("core.cast_int64_uint16",x)
}
function uint16 operator (uint16) (float32 x) {
    __builtin("core.cast_float32_uint16",x)
}
function uint16 operator (uint16) (float64 x) {
    __builtin("core.cast_float64_uint16",x)
}

// to uint32
function uint32 operator (uint32) (bool x) {
    __builtin("core.cast_bool_uint32",x)
}
function uint32 operator (uint32) (uint8 x) {
    __builtin("core.cast_uint8_uint32",x)
}
function uint32 operator (uint32) (uint16 x) {
    __builtin("core.cast_uint16_uint32",x)
}
function uint32 operator (uint32) (uint32 x) {
    x
}
function uint32 operator (uint32) (uint64 x) {
    __builtin("core.cast_uint64_uint32",x)
}
function uint32 operator (uint32) (int8 x) {
    __builtin("core.cast_int8_uint32",x)
}
function uint32 operator (uint32) (int16 x) {
    __builtin("core.cast_int16_uint32",x)
}
function uint32 operator (uint32) (int32 x) {
    __builtin("core.cast_int32_uint32",x)
}
function uint32 operator (uint32) (int64 x) {
    __builtin("core.cast_int64_uint32",x)
}
function uint32 operator (uint32) (float32 x) {
    __builtin("core.cast_float32_uint32",x)
}
function uint32 operator (uint32) (float64 x) {
    __builtin("core.cast_float64_uint32",x)
}

// to uint64
function uint64 operator (uint64) (bool x) {
    __builtin("core.cast_uint64_uint64",x)
}
function uint64 operator (uint64) (uint8 x) {
    __builtin("core.cast_uint8_uint64",x)
}
function uint64 operator (uint64) (uint16 x) {
    __builtin("core.cast_uint16_uint64",x)
}
function uint64 operator (uint64) (uint32 x) {
    __builtin("core.cast_uint32_uint64",x)
}
function uint64 operator (uint64) (uint64 x) {
    x
}
function uint64 operator (uint64) (int8 x) {
    __builtin("core.cast_int8_uint64",x)
}
function uint64 operator (uint64) (int16 x) {
    __builtin("core.cast_int16_uint64",x)
}
function uint64 operator (uint64) (int32 x) {
    __builtin("core.cast_int32_uint64",x)
}
function uint64 operator (uint64) (int64 x) {
    __builtin("core.cast_int64_uint64",x)
}
function uint64 operator (uint64) (float32 x) {
    __builtin("core.cast_float32_uint64",x)
}
function uint64 operator (uint64) (float64 x) {
    __builtin("core.cast_float64_uint64",x)
}

// to int8
function int8 operator (int8) (bool x) {
    __builtin("core.cast_bool_int8",x)
}
function int8 operator (int8) (uint8 x) {
    __builtin("core.cast_uint8_int8",x)
}
function int8 operator (int8) (uint16 x) {
    __builtin("core.cast_uint16_int8",x)
}
function int8 operator (int8) (uint32 x) {
    __builtin("core.cast_uint32_int8",x)
}
function int8 operator (int8) (uint64 x) {
    __builtin("core.cast_uint64_int8",x)
}
function int8 operator (int8) (int8 x) {
    x
}
function int8 operator (int8) (int16 x) {
    __builtin("core.cast_int16_int8",x)
}
function int8 operator (int8) (int32 x) {
    __builtin("core.cast_int32_int8",x)
}
function int8 operator (int8) (int64 x) {
    __builtin("core.cast_int64_int8",x)
}
function int8 operator (int8) (float32 x) {
    __builtin("core.cast_float32_int8",x)
}
function int8 operator (int8) (float64 x) {
    __builtin("core.cast_float64_int8",x)
}

// to int16
function int16 operator (int16) (bool x) {
    __builtin("core.cast_bool_int16",x)
}
function int16 operator (int16) (uint8 x) {
    __builtin("core.cast_uint8_int16",x)
}
function int16 operator (int16) (uint16 x) {
    __builtin("core.cast_uint16_int16",x)
}
function int16 operator (int16) (uint32 x) {
    __builtin("core.cast_uint32_int16",x)
}
function int16 operator (int16) (uint64 x) {
    __builtin("core.cast_uint64_int16",x)
}
function int16 operator (int16) (int8 x) {
    __builtin("core.cast_int8_int16",x)
}
function int16 operator (int16) (int16 x) {
    x
}
function int16 operator (int16) (int32 x) {
    __builtin("core.cast_int32_int16",x)
}
function int16 operator (int16) (int64 x) {
    __builtin("core.cast_int64_int16",x)
}
function int16 operator (int16) (float32 x) {
    __builtin("core.cast_float32_int16",x)
}
function int16 operator (int16) (float64 x) {
    __builtin("core.cast_float64_int16",x)
}

// to int32
function int32 operator (int32) (bool x) {
    __builtin("core.cast_bool_int32",x)
}
function int32 operator (int32) (uint8 x) {
    __builtin("core.cast_uint8_int32",x)
}
function int32 operator (int32) (uint16 x) {
    __builtin("core.cast_uint16_int32",x)
}
function int32 operator (int32) (uint32 x) {
    __builtin("core.cast_uint32_int32",x)
}
function int32 operator (int32) (uint64 x) {
    __builtin("core.cast_uint64_int32",x)
}
function int32 operator (int32) (int8 x) {
    __builtin("core.cast_int8_int32",x)
}
function int32 operator (int32) (int16 x) {
    __builtin("core.cast_int32_int32",x)
}
function int32 operator (int32) (int32 x) {
    x
}
function int32 operator (int32) (int64 x) {
    __builtin("core.cast_int64_int32",x)
}
function int32 operator (int32) (float32 x) {
    __builtin("core.cast_float32_int32",x)
}
function int32 operator (int32) (float64 x) {
    __builtin("core.cast_float64_int32",x)
}

// to int64
function int64 operator (int64) (bool x) {
    __builtin("core.cast_bool_int64",x)
}
function int64 operator (int64) (uint8 x) {
    __builtin("core.cast_uint8_int64",x)
}
function int64 operator (int64) (uint16 x) {
    __builtin("core.cast_uint16_int64",x)
}
function int64 operator (int64) (uint32 x) {
    __builtin("core.cast_uint32_int64",x)
}
function int64 operator (int64) (uint64 x) {
    __builtin("core.cast_uint64_int64",x)
}
function int64 operator (int64) (int8 x) {
    __builtin("core.cast_int8_int64",x)
}
function int64 operator (int64) (int16 x) {
    __builtin("core.cast_int16_int64",x)
}
function int64 operator (int64) (int32 x) {
    __builtin("core.cast_int32_int64",x)
}
function int64 operator (int64) (int64 x) {
    x
}
function int64 operator (int64) (float32 x) {
    __builtin("core.cast_float32_int64",x)
}
function int64 operator (int64) (float64 x) {

    __builtin("core.cast_float64_int64",x)
    
}

// to float32
function float32 operator (float32) (bool x) {

    __builtin("core.cast_bool_float32",x)
    
}
function float32 operator (float32) (uint8 x) {

    __builtin("core.cast_uint8_float32",x)
    
}
function float32 operator (float32) (uint16 x) {

    __builtin("core.cast_uint16_float32",x)
    
}
function float32 operator (float32) (uint32 x) {

    __builtin("core.cast_uint32_float32",x)
    
}
function float32 operator (float32) (uint64 x) {

    __builtin("core.cast_uint64_float32",x)
    
}
function float32 operator (float32) (int8 x) {

    __builtin("core.cast_int8_float32",x)
    
}
function float32 operator (float32) (int16 x) {

    __builtin("core.cast_int16_float32",x)
    
}
function float32 operator (float32) (int32 x) {

    __builtin("core.cast_int32_float32",x)
    
}
function float32 operator (float32) (int64 x) {

    __builtin("core.cast_int64_float32",x)
    
}
function float32 operator (float32) (float32 x) {
    x
}
function float32 operator (float32) (float64 x) {

    __builtin("core.cast_float64_float32",x)
    
}

// to float64
function float64 operator (float64) (bool x) {

    __builtin("core.cast_bool_float64",x)
    
}
function float64 operator (float64) (uint8 x) {

    __builtin("core.cast_uint8_float64",x)
    
}
function float64 operator (float64) (uint16 x) {

    __builtin("core.cast_uint16_float64",x)
    
}
function float64 operator (float64) (uint32 x) {

    __builtin("core.cast_uint32_float64",x)
    
}
function float64 operator (float64) (uint64 x) {

    __builtin("core.cast_uint64_float64",x)
    
}
function float64 operator (float64) (int8 x) {

    __builtin("core.cast_int8_float64",x)
    
}
function float64 operator (float64) (int16 x) {

    __builtin("core.cast_int16_float64",x)
    
}
function float64 operator (float64) (int32 x) {

    __builtin("core.cast_int32_float64",x)
    
}
function float64 operator (float64) (int64 x) {

    __builtin("core.cast_int64_float64",x)
    
}
function float64 operator (float64) (float32 x) {

    __builtin("core.cast_float32_float64",x)
    
}
function float64 operator (float64) (float64 x) {
    x
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

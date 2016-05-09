
#OPTIONS_SECREC --simplify=False
    
module builtin;

// classify
template <domain D,type T,dim N { N > 0} >
D T[[N]] classify (public T[[N]] x) {
    D T[[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = classify(x[i]);
    }
    return ret;
}

// declassify
template <domain D,type T,dim N { N > 0 }>
public T[[N]] declassify (D T[[N]] x) {
    public T[[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = declassify(x[i]);
    }
    return ret;
}

// strlen

uint strlen (string str) {
    uint ret;
    __syscall("core.strlen",str,__return ret);
    return ret;
}

// tostring

template <type T>
string tostring (public T x) {
    string ret;
    __syscall("core.tostring",x,__return ret);
    return ret;
}

// shape

template <domain D, type T, dim N>
uint[[1]] shape (D T[[N]] arr) {
    uint[[1]] ret;
    __syscall("core.shape",arr,__return ret);
    return ret;
}

//cat

template <domain D, type T, dim N>
D T[[N]] cat (D T[[N]] x, D T[[N]] y) {
    return cat(x,y,0);
}

template <domain D, type T, dim N>
D T[[N]] cat (D T[[N]] x, D T[[N]] y, const uint n { n < N }) {

    D T[[N]] ret;
    __syscall("core.cat", x,y,n,__return ret);
    return ret;
}

// reshape

template <domain D, type T, dim N>
D T[[size...(ns)]] reshape (D T[[N]] arr, uint... ns) {
    D T[[size...(ns)]] ret;
    __syscall("core.reshape",arr,ns,__return ret);
    return ret;
}

//repeat is a STUB 
template <domain D,type T,dim N>
D T[[N]] repeat (D T x) {
    D T[[N]] ret;
    __syscall("core.repeat",x,__return ret);
    return ret;
}

template <domain D, type T, dim N>
uint size (D T[[N]] x) {
    uint ret;
    __syscall("core.size",x,__return ret);
    return ret;
}

// logical operators

bool operator ==> (bool x,bool y) {
    bool ret;
    __syscall("core.implies",x,y,__return ret);
    return ret;
}

bool operator <==> (bool x,bool y) {
    bool ret;
    __syscall("core.eq_bool",x,y,__return ret);
    return ret;
}

bool operator && (bool x,bool y) {
    bool ret;
    __syscall("core.band",x,y,__return ret);
    return ret;
}


template <domain D, dim N { N > 0 }>
D bool[[N]] operator && (D bool[[N]] x,D bool[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D bool[[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] && y[i];
    }
    return ret;
}

bool operator || (bool x,bool y) {
    bool ret;
    __syscall("core.bor",x,y,__return ret);
    return ret;
}

template <domain D, dim N { N > 0 } >
D bool[[N]] operator || (D bool[[N]] x,D bool[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D bool [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] || y[i];
    }
    return ret;
}

// unary subtraction

int8 operator - (int8 x) {
    int8 ret;
    __syscall("core.neg_int8",x,__return ret);
    return ret;
} 
int16 operator - (int16 x) {
    int16 ret;
    __syscall("core.neg_int16",x,__return ret);
    return ret;
} 
int32 operator - (int32 x) {
    int32 ret;
    __syscall("core.neg_int32",x,__return ret);
    return ret;
} 
int64 operator - (int64 x) {
    int64 ret;
    __syscall("core.neg_int64",x,__return ret);
    return ret;
}

// unary array subtraction

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator - (D T[[N]] x) {
    D T [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = - x[i];
    }
    return ret;
}

// subtraction

int8 operator - (int8 x,int8 y) {
    int8 ret;
    __syscall("core.sub_int8",x,y,__return ret);
    return ret;
} 
int16 operator - (int16 x,int16 y) {
    int16 ret;
    __syscall("core.sub_int16",x,y,__return ret);
    return ret;
} 
int32 operator - (int32 x,int32 y) {
    int32 ret;
    __syscall("core.sub_int32",x,y,__return ret);
    return ret;
} 
int64 operator - (int64 x,int64 y) {
    int64 ret;
    __syscall("core.sub_int64",x,y,__return ret);
    return ret;
}
uint8 operator - (uint8 x,uint8 y) {
    uint8 ret;
    __syscall("core.sub_uint8",x,y,__return ret);
    return ret;
} 
uint16 operator - (uint16 x,uint16 y) {
    uint16 ret;
    __syscall("core.sub_uint16",x,y,__return ret);
    return ret;
} 
uint32 operator - (uint32 x,uint32 y) {
    uint32 ret;
    __syscall("core.sub_uint32",x,y,__return ret);
    return ret;
} 
uint64 operator - (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.sub_uint64",x,y,__return ret);
    return ret;
} 
float32 operator - (float32 x,float32 y) {
    float32 ret;
    __syscall("core.sub_float32",x,y,__return ret);
    return ret;
} 
float64 operator - (float64 x,float64 y) {
    float64 ret;
    __syscall("core.sub_float64",x,y,__return ret);
    return ret;
} 

// array subtraction

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator - (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D T [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] - y[i];
    }
    return ret;
}

// addition

int8 operator + (int8 x,int8 y) {
    int8 ret;
    __syscall("core.add_int8",x,y,__return ret);
    return ret;
} 
int16 operator + (int16 x,int16 y) {
    int16 ret;
    __syscall("core.add_int16",x,y,__return ret);
    return ret;
} 
int32 operator + (int32 x,int32 y) {
    int32 ret;
    __syscall("core.add_int32",x,y,__return ret);
    return ret;
} 
int64 operator + (int64 x,int64 y) {
    int64 ret;
    __syscall("core.add_int64",x,y,__return ret);
    return ret;
}
uint8 operator + (uint8 x,uint8 y) {
    uint8 ret;
    __syscall("core.add_uint8",x,y,__return ret);
    return ret;
} 
uint16 operator + (uint16 x,uint16 y) {
    uint16 ret;
    __syscall("core.add_uint16",x,y,__return ret);
    return ret;
} 
uint32 operator + (uint32 x,uint32 y) {
    uint32 ret;
    __syscall("core.add_uint32",x,y,__return ret);
    return ret;
} 
uint64 operator + (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.add_uint64",x,y,__return ret);
    return ret;
} 
float32 operator + (float32 x,float32 y) {
    float32 ret;
    __syscall("core.add_float32",x,y,__return ret);
    return ret;
} 
float64 operator + (float64 x,float64 y) {
    float64 ret;
    __syscall("core.add_float64",x,y,__return ret);
    return ret;
} 

// array addition

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator + (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D T [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] + y[i];
    }
    return ret;
}

// multiplication

int8 operator * (int8 x,int8 y) {
    int8 ret;
     __syscall("core.mul_int8",x,y,__return ret);
    return ret;
} 
int16 operator * (int16 x,int16 y) {
    int16 ret;
     __syscall("core.mul_int16",x,y,__return ret);
    return ret;
} 
int32 operator * (int32 x,int32 y) {
    int32 ret;
     __syscall("core.mul_int32",x,y,__return ret);
    return ret;
} 
int64 operator * (int64 x,int64 y) {
    int64 ret;
     __syscall("core.mul_int64",x,y,__return ret);
    return ret;
}
uint8 operator * (uint8 x,uint8 y) {
    uint8 ret;
    __syscall("core.mul_uint8",x,y,__return ret);
    return ret;
} 
uint16 operator * (uint16 x,uint16 y) {
    uint16 ret;
    __syscall("core.mul_uint16",x,y,__return ret);
    return ret;
} 
uint32 operator * (uint32 x,uint32 y) {
    uint32 ret;
    __syscall("core.mul_uint32",x,y,__return ret);
    return ret;
} 
uint64 operator * (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.mul_uint64",x,y,__return ret);
    return ret;
} 
float32 operator * (float32 x,float32 y) {
    float32 ret;
    __syscall("core.mul_float32",x,y,__return ret);
    return ret;
} 
float64 operator * (float64 x,float64 y) {
    float64 ret;
    __syscall("core.mul_float64",x,y,__return ret);
    return ret;
} 

// array multiplication

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator * (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D T [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] * y[i];
    }
    return ret;
}

//uints

bool operator == (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.eq_uint64",x,y,__return ret);
    return ret;
} 

bool operator <= (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.le_uint64",x,y,__return ret);
    return ret;
} 
bool operator < (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.lt_uint64",x,y,__return ret);
    return ret;
} 



/* @ bool equal(uint[[1]] x, uint[[1]] y) {
   @    return (size(x) == size(y) && forall uint i; (0 <= i && i < size(x)) ==> (x[i] == y[i]));
   @ }
   @ */
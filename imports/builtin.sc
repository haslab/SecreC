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

// size

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


// division

int8 operator / (int8 x,int8 y) {
    int8 ret;
    __syscall("core.div_int8",x,y,__return ret);
    return ret;
} 
int16 operator / (int16 x,int16 y) {
    int16 ret;
    __syscall("core.div_int16",x,y,__return ret);
    return ret;
} 
int32 operator / (int32 x,int32 y) {
    int32 ret;
    __syscall("core.div_int32",x,y,__return ret);
    return ret;
} 
int64 operator / (int64 x,int64 y) {
    int64 ret;
    __syscall("core.div_int64",x,y,__return ret);
    return ret;
}
uint8 operator / (uint8 x,uint8 y) {
    uint8 ret;
    __syscall("core.div_uint8",x,y,__return ret);
    return ret;
} 
uint16 operator / (uint16 x,uint16 y) {
    uint16 ret;
    __syscall("core.div_uint16",x,y,__return ret);
    return ret;
} 
uint32 operator / (uint32 x,uint32 y) {
    uint32 ret;
    __syscall("core.div_uint32",x,y,__return ret);
    return ret;
} 
uint64 operator / (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.div_uint64",x,y,__return ret);
    return ret;
} 
float32 operator / (float32 x,float32 y) {
    float32 ret;
    __syscall("core.div_float32",x,y,__return ret);
    return ret;
} 
float64 operator / (float64 x,float64 y) {
    float64 ret;
    __syscall("core.div_float64",x,y,__return ret);
    return ret;
} 

// array division

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator / (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D T [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] / y[i];
    }
    return ret;
}

// modulo

int8 operator % (int8 x,int8 y) {
    int8 ret;
    __syscall("core.mod_int8",x,y,__return ret);
    return ret;
} 
int16 operator % (int16 x,int16 y) {
    int16 ret;
    __syscall("core.mod_int16",x,y,__return ret);
    return ret;
} 
int32 operator % (int32 x,int32 y) {
    int32 ret;
    __syscall("core.mod_int32",x,y,__return ret);
    return ret;
} 
int64 operator % (int64 x,int64 y) {
    int64 ret;
    __syscall("core.mod_int64",x,y,__return ret);
    return ret;
}
uint8 operator % (uint8 x,uint8 y) {
    uint8 ret;
    __syscall("core.mod_uint8",x,y,__return ret);
    return ret;
} 
uint16 operator % (uint16 x,uint16 y) {
    uint16 ret;
    __syscall("core.mod_uint16",x,y,__return ret);
    return ret;
} 
uint32 operator % (uint32 x,uint32 y) {
    uint32 ret;
    __syscall("core.mod_uint32",x,y,__return ret);
    return ret;
} 
uint64 operator % (uint64 x,uint64 y) {
    uint64 ret;
    __syscall("core.mod_uint64",x,y,__return ret);
    return ret;
} 
float32 operator % (float32 x,float32 y) {
    float32 ret;
    __syscall("core.mod_float32",x,y,__return ret);
    return ret;
} 
float64 operator % (float64 x,float64 y) {
    float64 ret;
    __syscall("core.mod_float64",x,y,__return ret);
    return ret;
} 

// array modulo

template <domain D, type T, dim N { N > 0 } >
D T[[N]] operator % (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D T [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] % y[i];
    }
    return ret;
}

// greater

bool operator > (int8 x,int8 y) {
    bool ret;
    __syscall("core.gt_int8",x,y,__return ret);
    return ret;
} 
bool operator > (int16 x,int16 y) {
    bool ret;
    __syscall("core.gt_int16",x,y,__return ret);
    return ret;
} 
bool operator > (int32 x,int32 y) {
    bool ret;
    __syscall("core.gt_int32",x,y,__return ret);
    return ret;
} 
bool operator > (int64 x,int64 y) {
    bool ret;
    __syscall("core.gt_int64",x,y,__return ret);
    return ret;
}
bool operator > (uint8 x,uint8 y) {
    bool ret;
    __syscall("core.gt_uint8",x,y,__return ret);
    return ret;
} 
bool operator > (uint16 x,uint16 y) {
    bool ret;
    __syscall("core.gt_uint16",x,y,__return ret);
    return ret;
} 
bool operator > (uint32 x,uint32 y) {
    bool ret;
    __syscall("core.gt_uint32",x,y,__return ret);
    return ret;
} 
bool operator > (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.gt_uint64",x,y,__return ret);
    return ret;
} 
bool operator > (float32 x,float32 y) {
    bool ret;
    __syscall("core.gt_float32",x,y,__return ret);
    return ret;
} 
bool operator > (float64 x,float64 y) {
    bool ret;
    __syscall("core.gt_float64",x,y,__return ret);
    return ret;
} 
bool operator > (bool x,bool y) {
    bool ret;
    __syscall("core.gt_bool",x,y,__return ret);
    return ret;
} 

// array greater

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator > (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D bool [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] > y[i];
    }
    return ret;
}

// smaller

bool operator < (int8 x,int8 y) {
    bool ret;
    __syscall("core.lt_int8",x,y,__return ret);
    return ret;
} 
bool operator < (int16 x,int16 y) {
    bool ret;
    __syscall("core.lt_int16",x,y,__return ret);
    return ret;
} 
bool operator < (int32 x,int32 y) {
    bool ret;
    __syscall("core.lt_int32",x,y,__return ret);
    return ret;
} 
bool operator < (int64 x,int64 y) {
    bool ret;
    __syscall("core.lt_int64",x,y,__return ret);
    return ret;
}
bool operator < (uint8 x,uint8 y) {
    bool ret;
    __syscall("core.lt_uint8",x,y,__return ret);
    return ret;
} 
bool operator < (uint16 x,uint16 y) {
    bool ret;
    __syscall("core.lt_uint16",x,y,__return ret);
    return ret;
} 
bool operator < (uint32 x,uint32 y) {
    bool ret;
    __syscall("core.lt_uint32",x,y,__return ret);
    return ret;
} 
bool operator < (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.lt_uint64",x,y,__return ret);
    return ret;
} 
bool operator < (float32 x,float32 y) {
    bool ret;
    __syscall("core.lt_float32",x,y,__return ret);
    return ret;
} 
bool operator < (float64 x,float64 y) {
    bool ret;
    __syscall("core.lt_float64",x,y,__return ret);
    return ret;
} 
bool operator < (bool x,bool y) {
    bool ret;
    __syscall("core.lt_bool",x,y,__return ret);
    return ret;
} 

// array smaller

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator < (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D bool [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] < y[i];
    }
    return ret;
}

// greater or equal

bool operator >= (int8 x,int8 y) {
    bool ret;
    __syscall("core.ge_int8",x,y,__return ret);
    return ret;
} 
bool operator >= (int16 x,int16 y) {
    bool ret;
    __syscall("core.ge_int16",x,y,__return ret);
    return ret;
} 
bool operator >= (int32 x,int32 y) {
    bool ret;
    __syscall("core.ge_int32",x,y,__return ret);
    return ret;
} 
bool operator >= (int64 x,int64 y) {
    bool ret;
    __syscall("core.ge_int64",x,y,__return ret);
    return ret;
}
bool operator >= (uint8 x,uint8 y) {
    bool ret;
    __syscall("core.ge_uint8",x,y,__return ret);
    return ret;
} 
bool operator >= (uint16 x,uint16 y) {
    bool ret;
    __syscall("core.ge_uint16",x,y,__return ret);
    return ret;
} 
bool operator >= (uint32 x,uint32 y) {
    bool ret;
    __syscall("core.ge_uint32",x,y,__return ret);
    return ret;
} 
bool operator >= (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.ge_uint64",x,y,__return ret);
    return ret;
} 
bool operator >= (float32 x,float32 y) {
    bool ret;
    __syscall("core.ge_float32",x,y,__return ret);
    return ret;
} 
bool operator >= (float64 x,float64 y) {
    bool ret;
    __syscall("core.ge_float64",x,y,__return ret);
    return ret;
} 
bool operator >= (bool x,bool y) {
    bool ret;
    __syscall("core.ge_bool",x,y,__return ret);
    return ret;
} 

// array greater or equal

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator >= (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D bool [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] >= y[i];
    }
    return ret;
}

// smaller or equal

bool operator <= (int8 x,int8 y) {
    bool ret;
    __syscall("core.le_int8",x,y,__return ret);
    return ret;
} 
bool operator <= (int16 x,int16 y) {
    bool ret;
    __syscall("core.le_int16",x,y,__return ret);
    return ret;
} 
bool operator <= (int32 x,int32 y) {
    bool ret;
    __syscall("core.le_int32",x,y,__return ret);
    return ret;
} 
bool operator <= (int64 x,int64 y) {
    bool ret;
    __syscall("core.le_int64",x,y,__return ret);
    return ret;
}
bool operator <= (uint8 x,uint8 y) {
    bool ret;
    __syscall("core.le_uint8",x,y,__return ret);
    return ret;
} 
bool operator <= (uint16 x,uint16 y) {
    bool ret;
    __syscall("core.le_uint16",x,y,__return ret);
    return ret;
} 
bool operator <= (uint32 x,uint32 y) {
    bool ret;
    __syscall("core.le_uint32",x,y,__return ret);
    return ret;
} 
bool operator <= (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.le_uint64",x,y,__return ret);
    return ret;
} 
bool operator <= (float32 x,float32 y) {
    bool ret;
    __syscall("core.le_float32",x,y,__return ret);
    return ret;
} 
bool operator <= (float64 x,float64 y) {
    bool ret;
    __syscall("core.le_float64",x,y,__return ret);
    return ret;
} 
bool operator <= (bool x,bool y) {
    bool ret;
    __syscall("core.le_bool",x,y,__return ret);
    return ret;
} 

// array greater

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator <= (D T[[N]] x, D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D bool [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] <= y[i];
    }
    return ret;
}

// equal

bool operator == (int8 x,int8 y) {
    bool ret;
    __syscall("core.eq_int8",x,y,__return ret);
    return ret;
} 
bool operator == (int16 x,int16 y) {
    bool ret;
    __syscall("core.eq_int16",x,y,__return ret);
    return ret;
} 
bool operator == (int32 x,int32 y) {
    bool ret;
    __syscall("core.eq_int32",x,y,__return ret);
    return ret;
} 
bool operator == (int64 x,int64 y) {
    bool ret;
    __syscall("core.eq_int64",x,y,__return ret);
    return ret;
}
bool operator == (uint8 x,uint8 y) {
    bool ret;
    __syscall("core.eq_uint8",x,y,__return ret);
    return ret;
} 
bool operator == (uint16 x,uint16 y) {
    bool ret;
    __syscall("core.eq_uint16",x,y,__return ret);
    return ret;
} 
bool operator == (uint32 x,uint32 y) {
    bool ret;
    __syscall("core.eq_uint32",x,y,__return ret);
    return ret;
} 
bool operator == (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.eq_uint64",x,y,__return ret);
    return ret;
} 
bool operator == (float32 x,float32 y) {
    bool ret;
    __syscall("core.eq_float32",x,y,__return ret);
    return ret;
} 
bool operator == (float64 x,float64 y) {
    bool ret;
    __syscall("core.eq_float64",x,y,__return ret);
    return ret;
} 
bool operator == (bool x,bool y) {
    bool ret;
    __syscall("core.eq_bool",x,y,__return ret);
    return ret;
} 

// array equal

template <domain D, type T>
D bool[[1]] operator == (D T[[1]] x,D T[[1]] y)
//@ requires equal(shape(x),shape(y));
{

    D bool[[1]] ret (size(x));
    for (uint i = 0; i < size(x); i++) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator == (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D bool [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] == y[i];
    }
    return ret;
}

// not equal

bool operator != (int8 x,int8 y) {
    bool ret;
    __syscall("core.neq_int8",x,y,__return ret);
    return ret;
} 
bool operator != (int16 x,int16 y) {
    bool ret;
    __syscall("core.neq_int16",x,y,__return ret);
    return ret;
} 
bool operator != (int32 x,int32 y) {
    bool ret;
    __syscall("core.neq_int32",x,y,__return ret);
    return ret;
} 
bool operator != (int64 x,int64 y) {
    bool ret;
    __syscall("core.neq_int64",x,y,__return ret);
    return ret;
}
bool operator != (uint8 x,uint8 y) {
    bool ret;
    __syscall("core.neq_uint8",x,y,__return ret);
    return ret;
} 
bool operator != (uint16 x,uint16 y) {
    bool ret;
    __syscall("core.neq_uint16",x,y,__return ret);
    return ret;
} 
bool operator != (uint32 x,uint32 y) {
    bool ret;
    __syscall("core.neq_uint32",x,y,__return ret);
    return ret;
} 
bool operator != (uint64 x,uint64 y) {
    bool ret;
    __syscall("core.neq_uint64",x,y,__return ret);
    return ret;
} 
bool operator != (float32 x,float32 y) {
    bool ret;
    __syscall("core.neq_float32",x,y,__return ret);
    return ret;
} 
bool operator != (float64 x,float64 y) {
    bool ret;
    __syscall("core.neq_float64",x,y,__return ret);
    return ret;
} 
bool operator != (bool x,bool y) {
    bool ret;
    __syscall("core.neq_bool",x,y,__return ret);
    return ret;
} 

// array not equal

template <domain D, type T, dim N { N > 0 } >
D bool[[N]] operator != (D T[[N]] x,D T[[N]] y)
//@ requires equal(shape(x),shape(y));
{
    D bool [[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = x[i] != y[i];
    }
    return ret;
}

bool operator ! (bool x) {
    if (x==false) return true;
    else return false;
}

template <domain D,dim N { N > 0 }>
D bool[[N]] operator ! (D bool[[N]] x) {
    return size(x) > 0 ? cat({!x[0]},!x[1:]) : {};
}

// casts

// to bool
bool operator (bool) (bool x) {
    return x;
}
bool operator (bool) (uint8 x) {
    bool ret;
    __syscall("core.cast_uint8_bool",x,__return ret);
    return ret;
}
bool operator (bool) (uint16 x) {
    bool ret;
    __syscall("core.cast_uint16_bool",x,__return ret);
    return ret;
}
bool operator (bool) (uint32 x) {
    bool ret;
    __syscall("core.cast_uint32_bool",x,__return ret);
    return ret;
}
bool operator (bool) (uint64 x) {
    bool ret;
    __syscall("core.cast_uint64_bool",x,__return ret);
    return ret;
}
bool operator (bool) (int8 x) {
    bool ret;
    __syscall("core.cast_int8_bool",x,__return ret);
    return ret;
}
bool operator (bool) (int16 x) {
    bool ret;
    __syscall("core.cast_int16_bool",x,__return ret);
    return ret;
}
bool operator (bool) (int32 x) {
    bool ret;
    __syscall("core.castuint32_bool",x,__return ret);
    return ret;
}
bool operator (bool) (int64 x) {
    bool ret;
    __syscall("core.cast_int64_bool",x,__return ret);
    return ret;
}
bool operator (bool) (float32 x) {
    bool ret;
    __syscall("core.cast_float32_bool",x,__return ret);
    return ret;
}
bool operator (bool) (float64 x) {
    bool ret;
    __syscall("core.cast_float64_bool",x,__return ret);
    return ret;
}

// to uint8
uint8 operator (uint8) (bool x) {
    uint8 ret;
    __syscall("core.cast_bool_uint8",x,__return ret);
    return ret;
}
uint8 operator (uint8) (uint8 x) {
    return x;
}
uint8 operator (uint8) (uint16 x) {
    uint8 ret;
    __syscall("core.cast_uint16_uint8",x,__return ret);
    return ret;
}
uint8 operator (uint8) (uint32 x) {
    uint8 ret;
    __syscall("core.cast_uint32_uint8",x,__return ret);
    return ret;
}
uint8 operator (uint8) (uint64 x) {
    uint8 ret;
    __syscall("core.cast_uint64_uint8",x,__return ret);
    return ret;
}
uint8 operator (uint8) (int8 x) {
    uint8 ret;
    __syscall("core.cast_int8_uint8",x,__return ret);
    return ret;
}
uint8 operator (uint8) (int16 x) {
    uint8 ret;
    __syscall("core.cast_int16_uint8",x,__return ret);
    return ret;
}
uint8 operator (uint8) (int32 x) {
    uint8 ret;
    __syscall("core.cast_int32_uint8",x,__return ret);
    return ret;
}
uint8 operator (uint8) (int64 x) {
    uint8 ret;
    __syscall("core.cast_int64_uint8",x,__return ret);
    return ret;
}
uint8 operator (uint8) (float32 x) {
    uint8 ret;
    __syscall("core.cast_float32_uint8",x,__return ret);
    return ret;
}
uint8 operator (uint8) (float64 x) {
    uint8 ret;
    __syscall("core.cast_float64_uint8",x,__return ret);
    return ret;
}

// to uint16
uint16 operator (uint16) (bool x) {
    uint16 ret;
    __syscall("core.cast_bool_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (uint8 x) {
    uint16 ret;
    __syscall("core.cast_uint8_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (uint16 x) {
    return x;
}
uint16 operator (uint16) (uint32 x) {
    uint16 ret;
    __syscall("core.cast_uint32_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (uint64 x) {
    uint16 ret;
    __syscall("core.cast_uint64_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (int8 x) {
    uint16 ret;
    __syscall("core.cast_uint8_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (int16 x) {
    uint16 ret;
    __syscall("core.cast_int16_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (int32 x) {
    uint16 ret;
    __syscall("core.cast_int32_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (int64 x) {
    uint16 ret;
    __syscall("core.cast_int64_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (float32 x) {
    uint16 ret;
    __syscall("core.cast_float32_uint16",x,__return ret);
    return ret;
}
uint16 operator (uint16) (float64 x) {
    uint16 ret;
    __syscall("core.cast_float64_uint16",x,__return ret);
    return ret;
}

// to uint32
uint32 operator (uint32) (bool x) {
    uint32 ret;
    __syscall("core.cast_bool_uint32",x,__return ret);
    return ret;
}
uint32 operator (uint32) (uint8 x) {
    uint32 ret;
    __syscall("core.cast_uint8_uint32",x,__return ret);
    return ret;
}
uint32 operator (uint32) (uint16 x) {
    uint32 ret;
    __syscall("core.cast_uint16_uint32",x,__return ret);
    return ret;
}
uint32 operator (uint32) (uint32 x) {
    return x;
}
uint32 operator (uint32) (uint64 x) {
    uint32 ret;
    __syscall("core.cast_uint64_uint32",x,__return ret);
    return ret;
}
uint32 operator (uint32) (int8 x) {
    uint32 ret;
    __syscall("core.cast_int8_uint32",x,__return ret);
    return ret;
}
uint32 operator (uint32) (int16 x) {
    uint32 ret;
    __syscall("core.cast_int16_uint32",x,__return ret);
    return ret;
}
uint32 operator (uint32) (int32 x) {
    uint32 ret;
    __syscall("core.cast_int32_uint32",x,__return ret);
    return ret;
}
uint32 operator (uint32) (int64 x) {
    uint32 ret;
    __syscall("core.cast_int64_uint32",x,__return ret);
    return ret;
}
uint32 operator (uint32) (float32 x) {
    uint32 ret;
    __syscall("core.cast_float32_uint32",x,__return ret);
    return ret;
}
uint32 operator (uint32) (float64 x) {
    uint32 ret;
    __syscall("core.cast_float64_uint32",x,__return ret);
    return ret;
}

// to uint64
uint64 operator (uint64) (bool x) {
    uint64 ret;
    __syscall("core.cast_uint64_uint64",x,__return ret);
    return ret;
}
uint64 operator (uint64) (uint8 x) {
    uint64 ret;
    __syscall("core.cast_uint8_uint64",x,__return ret);
    return ret;
}
uint64 operator (uint64) (uint16 x) {
    uint64 ret;
    __syscall("core.cast_uint16_uint64",x,__return ret);
    return ret;
}
uint64 operator (uint64) (uint32 x) {
    uint64 ret;
    __syscall("core.cast_uint32_uint64",x,__return ret);
    return ret;
}
uint64 operator (uint64) (uint64 x) {
    return x;
}
uint64 operator (uint64) (int8 x) {
    uint64 ret;
    __syscall("core.cast_int8_uint64",x,__return ret);
    return ret;
}
uint64 operator (uint64) (int16 x) {
    uint64 ret;
    __syscall("core.cast_int16_uint64",x,__return ret);
    return ret;
}
uint64 operator (uint64) (int32 x) {
    uint64 ret;
    __syscall("core.cast_int32_uint64",x,__return ret);
    return ret;
}
uint64 operator (uint64) (int64 x) {
    uint64 ret;
    __syscall("core.cast_int64_uint64",x,__return ret);
    return ret;
}
uint64 operator (uint64) (float32 x) {
    uint64 ret;
    __syscall("core.cast_float32_uint64",x,__return ret);
    return ret;
}
uint64 operator (uint64) (float64 x) {
    uint64 ret;
    __syscall("core.cast_float64_uint64",x,__return ret);
    return ret;
}

// to int8
int8 operator (int8) (bool x) {
    int8 ret;
    __syscall("core.cast_bool_int8",x,__return ret);
    return ret;
}
int8 operator (int8) (uint8 x) {
    int8 ret;
    __syscall("core.cast_uint8_int8",x,__return ret);
    return ret;
}
int8 operator (int8) (uint16 x) {
    int8 ret;
    __syscall("core.cast_uint16_int8",x,__return ret);
    return ret;
}
int8 operator (int8) (uint32 x) {
    int8 ret;
    __syscall("core.cast_uint32_int8",x,__return ret);
    return ret;
}
int8 operator (int8) (uint64 x) {
    int8 ret;
    __syscall("core.cast_uint64_int8",x,__return ret);
    return ret;
}
int8 operator (int8) (int8 x) {
    return x;
}
int8 operator (int8) (int16 x) {
    int8 ret;
    __syscall("core.cast_int16_int8",x,__return ret);
    return ret;
}
int8 operator (int8) (int32 x) {
    int8 ret;
    __syscall("core.cast_int32_int8",x,__return ret);
    return ret;
}
int8 operator (int8) (int64 x) {
    int8 ret;
    __syscall("core.cast_int64_int8",x,__return ret);
    return ret;
}
int8 operator (int8) (float32 x) {
    int8 ret;
    __syscall("core.cast_float32_int8",x,__return ret);
    return ret;
}
int8 operator (int8) (float64 x) {
    int8 ret;
    __syscall("core.cast_float64_int8",x,__return ret);
    return ret;
}

// to int16
int16 operator (int16) (bool x) {
    int16 ret;
    __syscall("core.cast_bool_int16",x,__return ret);
    return ret;
}
int16 operator (int16) (uint8 x) {
    int16 ret;
    __syscall("core.cast_uint8_int16",x,__return ret);
    return ret;
}
int16 operator (int16) (uint16 x) {
    int16 ret;
    __syscall("core.cast_uint16_int16",x,__return ret);
    return ret;
}
int16 operator (int16) (uint32 x) {
    int16 ret;
    __syscall("core.cast_uint32_int16",x,__return ret);
    return ret;
}
int16 operator (int16) (uint64 x) {
    int16 ret;
    __syscall("core.cast_uint64_int16",x,__return ret);
    return ret;
}
int16 operator (int16) (int8 x) {
    int16 ret;
    __syscall("core.cast_int8_int16",x,__return ret);
    return ret;
}
int16 operator (int16) (int16 x) {
    return x;
}
int16 operator (int16) (int32 x) {
    int16 ret;
    __syscall("core.cast_int32_int16",x,__return ret);
    return ret;
}
int16 operator (int16) (int64 x) {
    int16 ret;
    __syscall("core.cast_int64_int16",x,__return ret);
    return ret;
}
int16 operator (int16) (float32 x) {
    int16 ret;
    __syscall("core.cast_float32_int16",x,__return ret);
    return ret;
}
int16 operator (int16) (float64 x) {
    int16 ret;
    __syscall("core.cast_float64_int16",x,__return ret);
    return ret;
}

// to int32
int32 operator (int32) (bool x) {
    int32 ret;
    __syscall("core.cast_bool_int32",x,__return ret);
    return ret;
}
int32 operator (int32) (uint8 x) {
    int32 ret;
    __syscall("core.cast_uint8_int32",x,__return ret);
    return ret;
}
int32 operator (int32) (uint16 x) {
    int32 ret;
    __syscall("core.cast_uint16_int32",x,__return ret);
    return ret;
}
int32 operator (int32) (uint32 x) {
    int32 ret;
    __syscall("core.cast_uint32_int32",x,__return ret);
    return ret;
}
int32 operator (int32) (uint64 x) {
    int32 ret;
    __syscall("core.cast_uint64_int32",x,__return ret);
    return ret;
}
int32 operator (int32) (int8 x) {
    int32 ret;
    __syscall("core.cast_int8_int32",x,__return ret);
    return ret;
}
int32 operator (int32) (int16 x) {
    int32 ret;
    __syscall("core.cast_int32_int32",x,__return ret);
    return ret;
}
int32 operator (int32) (int32 x) {
    return x;
}
int32 operator (int32) (int64 x) {
    int32 ret;
    __syscall("core.cast_int64_int32",x,__return ret);
    return ret;
}
int32 operator (int32) (float32 x) {
    int32 ret;
    __syscall("core.cast_float32_int32",x,__return ret);
    return ret;
}
int32 operator (int32) (float64 x) {
    int32 ret;
    __syscall("core.cast_float64_int32",x,__return ret);
    return ret;
}

// to int64
int64 operator (int64) (bool x) {
    int64 ret;
    __syscall("core.cast_bool_int64",x,__return ret);
    return ret;
}
int64 operator (int64) (uint8 x) {
    int64 ret;
    __syscall("core.cast_uint8_int64",x,__return ret);
    return ret;
}
int64 operator (int64) (uint16 x) {
    int64 ret;
    __syscall("core.cast_uint16_int64",x,__return ret);
    return ret;
}
int64 operator (int64) (uint32 x) {
    int64 ret;
    __syscall("core.cast_uint32_int64",x,__return ret);
    return ret;
}
int64 operator (int64) (uint64 x) {
    int64 ret;
    __syscall("core.cast_uint64_int64",x,__return ret);
    return ret;
}
int64 operator (int64) (int8 x) {
    int64 ret;
    __syscall("core.cast_int8_int64",x,__return ret);
    return ret;
}
int64 operator (int64) (int16 x) {
    int64 ret;
    __syscall("core.cast_int16_int64",x,__return ret);
    return ret;
}
int64 operator (int64) (int32 x) {
    int64 ret;
    __syscall("core.cast_int32_int64",x,__return ret);
    return ret;
}
int64 operator (int64) (int64 x) {
    return x;
}
int64 operator (int64) (float32 x) {
    int64 ret;
    __syscall("core.cast_float32_int64",x,__return ret);
    return ret;
}
int64 operator (int64) (float64 x) {
    int64 ret;
    __syscall("core.cast_float64_int64",x,__return ret);
    return ret;
}

// to float32
float32 operator (float32) (bool x) {
    float32 ret;
    __syscall("core.cast_bool_float32",x,__return ret);
    return ret;
}
float32 operator (float32) (uint8 x) {
    float32 ret;
    __syscall("core.cast_uint8_float32",x,__return ret);
    return ret;
}
float32 operator (float32) (uint16 x) {
    float32 ret;
    __syscall("core.cast_uint16_float32",x,__return ret);
    return ret;
}
float32 operator (float32) (uint32 x) {
    float32 ret;
    __syscall("core.cast_uint32_float32",x,__return ret);
    return ret;
}
float32 operator (float32) (uint64 x) {
    float32 ret;
    __syscall("core.cast_uint64_float32",x,__return ret);
    return ret;
}
float32 operator (float32) (int8 x) {
    float32 ret;
    __syscall("core.cast_int8_float32",x,__return ret);
    return ret;
}
float32 operator (float32) (int16 x) {
    float32 ret;
    __syscall("core.cast_int16_float32",x,__return ret);
    return ret;
}
float32 operator (float32) (int32 x) {
    float32 ret;
    __syscall("core.cast_int32_float32",x,__return ret);
    return ret;
}
float32 operator (float32) (int64 x) {
    float32 ret;
    __syscall("core.cast_int64_float32",x,__return ret);
    return ret;
}
float32 operator (float32) (float32 x) {
    return x;
}
float32 operator (float32) (float64 x) {
    float32 ret;
    __syscall("core.cast_float64_float32",x,__return ret);
    return ret;
}

// to float64
float64 operator (float64) (bool x) {
    float64 ret;
    __syscall("core.cast_bool_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (uint8 x) {
    float64 ret;
    __syscall("core.cast_uint8_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (uint16 x) {
    float64 ret;
    __syscall("core.cast_uint16_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (uint32 x) {
    float64 ret;
    __syscall("core.cast_uint32_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (uint64 x) {
    float64 ret;
    __syscall("core.cast_uint64_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (int8 x) {
    float64 ret;
    __syscall("core.cast_int8_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (int16 x) {
    float64 ret;
    __syscall("core.cast_int16_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (int32 x) {
    float64 ret;
    __syscall("core.cast_int32_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (int64 x) {
    float64 ret;
    __syscall("core.cast_int64_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (float32 x) {
    float64 ret;
    __syscall("core.cast_float32_float64",x,__return ret);
    return ret;
}
float64 operator (float64) (float64 x) {
    return x;
}

// array casts
template <domain D, dim N { N > 0 }, type X, type Y>
D Y[[N]] operator (Y) (D X[[N]] x) {
    D Y[[N]] ret (varray(shape(x),N)...);
    for (uint i = 0; i < shape(x)[0]; i++) {
        ret[i] = (Y) x[i];
    }
    return ret;
}

/* @ bool equal(uint[[1]] x, uint[[1]] y) {
   @    return (size(x) == size(y) && forall uint i; (0 <= i && i < size(x)) ==> (x[i] == y[i]));
   @ }
   @ */

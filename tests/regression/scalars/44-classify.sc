// set of legal implicit classifications
kind additive3pp;
domain sharemind_test_pd additive3pp;


sharemind_test_pd uint classify (uint x) {
    havoc sharemind_test_pd uint y;
    return y;
}
sharemind_test_pd bool classify (bool x) {
    havoc sharemind_test_pd bool y;
    return y;
}

sharemind_test_pd uint operator - (sharemind_test_pd uint x) {
    // stub
    havoc sharemind_test_pd uint ret;
    return ret;
}
sharemind_test_pd bool operator ! (sharemind_test_pd bool x) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}

sharemind_test_pd uint operator + (sharemind_test_pd uint x,sharemind_test_pd uint y) {
    // stub
    havoc sharemind_test_pd uint ret;
    return ret;
}
sharemind_test_pd uint operator * (sharemind_test_pd uint x,sharemind_test_pd uint y) {
    // stub
    havoc sharemind_test_pd uint ret;
    return ret;
}
sharemind_test_pd uint operator - (sharemind_test_pd uint x,sharemind_test_pd uint y) {
    // stub
    havoc sharemind_test_pd uint ret;
    return ret;
}

sharemind_test_pd bool operator && (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator || (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}

sharemind_test_pd bool operator > (sharemind_test_pd uint x,sharemind_test_pd uint y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator < (sharemind_test_pd uint x,sharemind_test_pd uint y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator >= (sharemind_test_pd uint x,sharemind_test_pd uint y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator <= (sharemind_test_pd uint x,sharemind_test_pd uint y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator == (sharemind_test_pd uint x,sharemind_test_pd uint y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator > (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator < (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator >= (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator <= (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}
sharemind_test_pd bool operator == (sharemind_test_pd bool x,sharemind_test_pd bool y) {
    // stub
    havoc sharemind_test_pd bool ret;
    return ret;
}

void main () {
    sharemind_test_pd uint p1;
    public uint x;

    sharemind_test_pd bool p2;
    public bool y;

    p1 = x;
    p1 = p1;
    p2 = y;
    p2 = p2;
    
    p1 = - x;
    p1 = - p1;
    p2 = ! y;
    p2 = ! p2;
    
    p1 = p1 + p1;
    p1 = p1 - p1;
    p1 = p1 * p1;
    p1 = p1 + x;
    p1 = p1 - x;
    p1 = p1 * x;
    p1 = x + p1;
    p1 = x - p1;
    p1 = x * p1;
    p1 = x + x;
    p1 = x - x;
    p1 = x * x;
    
    p2 = p2 && p2;
    p2 = p2 || p2;
    p2 = p2 && y;
    p2 = p2 || y;
    p2 = y && p2;
    p2 = y || p2;
    p2 = y && y;
    p2 = y || y;
    
    p2 = p1 <  p1;
    p2 = p1 >  p1;
    p2 = p1 <= p1;
    p2 = p1 >= p1;
    p2 = p1 == p1;
    p2 = p1 <  x;
    p2 = p1 >  x;
    p2 = p1 <= x;
    p2 = p1 >= x;
    p2 = p1 == x;
    p2 = x <  p1;
    p2 = x >  p1;
    p2 = x <= p1;
    p2 = x >= p1;
    p2 = x == p1;
    p2 = x <  x;
    p2 = x >  x;
    p2 = x <= x;
    p2 = x >= x;
    p2 = x == x;
}

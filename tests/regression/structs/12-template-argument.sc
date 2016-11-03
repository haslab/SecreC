#OPTIONS_SECREC --implicitcoercions=defaultsc

kind additive3p;
domain pd_a3p additive3p;

template <type T>
pd_a3p T classify (public T x) {
    //stub
    havoc pd_a3p T ret;
    return ret;
}

template <type T>
public T declassify (pd_a3p T x) {
    //stub
    havoc public T ret;
    return ret;
}

pd_a3p uint operator + (pd_a3p uint x,pd_a3p uint y) {
    //stub
    havoc pd_a3p uint ret;
    return ret;
}
pd_a3p uint operator * (pd_a3p uint x,pd_a3p uint y) {
    //stub
    havoc pd_a3p uint ret;
    return ret;
}
pd_a3p bool operator == (pd_a3p uint x,pd_a3p uint y) {
    //stub
    havoc pd_a3p bool ret;
    return ret;
}

template <domain D>
struct point {
    D uint x;
    D uint y;
}

template <domain D>
D uint sqrLen (point<D> p) {
    return p.x*p.x + p.y*p.y;
}

template <domain D>
point<D> get () {
    public point<D> result;
    result.x = 1;
    result.y = 1;
    return result;
}

void main () {
    public point<public> p1 = get ();
    public point<pd_a3p> p2 = get ();
    uint l1 = sqrLen (p1);
    pd_a3p uint l2 = sqrLen (p2);
    assert (l1 == 2);
    assert (declassify (l2 == 2));
    return;
}

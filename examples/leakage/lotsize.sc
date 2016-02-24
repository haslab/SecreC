
/*
Joint economic lot size example.
*/

//@ leaks b;
//@ leaks c;
//@ leaks d;
//@ leaks i;
public int lot_size_alice (public int fvA, public int cA, public int hvA, private int fbB, private int hbB, public int yd) {
    public int a = 2 * yd;
    private int b = a * fvA;
    private int c = yd / cA;
    private int d = c * hvA;
    
    public int e = 2 * yd;
    private int f = e * fbB;
    
    private int g = f + b;
    private int h = hbB + d;
    private int i = g / h;
    
    return sqrt(i); //assuming that secrec implements integer square root
}

//@ leaks f;
//@ leaks i;
public int lot_size_bob (private int fvA, private int cA, private int hvA, public int fbB, public int hbB, public int yd) {
    public int a = 2 * yd;
    private int b = a * fvA;
    private int c = yd / cA;
    private int d = c * hvA;
    
    public int e = 2 * yd;
    private int f = e * fbB;
    
    private int g = f + b;
    private int h = hbB + d;
    private int i = g / h;
    
    return sqrt(i); //assuming that secrec implements integer square root
}

// b,c,d are proven ok by the type-checker
// knowledge inference must prove that i can leak
public int lot_size_alice_opt (public int fvA, public int cA, public int hvA, private int fbB, private int hbB, public int yd) {
    public int a = 2 * yd;
    public int b = a * fvA;
    public int c = yd / cA;
    public int d = c * hvA;
    
    public int e = 2 * yd;
    private int f = e * fbB;
    
    private int g = f + b;
    private int h = hbB + d;
    public int i = declassify(g / h);
    
    return sqrt(i);
}
// f is proven ok by the type-checker
// knowledge inference must prove that i can leak
public int lot_size_bob_opt (private int fvA, private int cA, private int hvA, public int fbB, public int hbB, public int yd) {
    public int a = 2 * yd;
    private int b = a * fvA;
    private int c = yd / cA;
    private int d = c * hvA;
    
    public int e = 2 * yd;
    public int f = e * fbB;
    
    private int g = f + b;
    private int h = hbB + d;
    public int i = declassify(g / h);
    
    return sqrt(i);
}
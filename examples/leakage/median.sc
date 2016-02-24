/*
Secure median example.
SecreC is party-independent. For knowledge inference purposes, we can use n methods to infer knowledge of n parties.
For this example, if we assumed two input/result parties Alice and Bob are their inputs, we could actually perform the median publicly.
*/

kind additive3pp;
domain private additive3pp;

/* To simulate a two-party protocol where Alice knows both a1 and a2.
Given Alice's knowledge, the intermediate median comparisons leak.
*/
//@ requires a1 < a2;
//@ requires b1 < b2;
//@ requires distinct(a1,a2,b1,b2);
//@ leaks median_comparisons (a1,a2,b1,b2);
int median_alice (public int a1, public int a2, private int b1, private int b2) {
    return median(a1,a2,b1,b2);
}

/* To simulate a two-party protocol where Bob knows both b1 and b2.
Given Bob's knowledge, the intermediate median comparisons leak.
*/
//@ requires a1 < a2;
//@ requires b1 < b2;
//@ requires distinct(a1,a2,b1,b2);
//@ leaks median_comparisons (a1,a2,b1,b2);
int median_bob (private int a1, private int a2, public int b1, public int b2) {
    return median(a1,a2,b1,b2);
}

// This brings back the context-sensitivity concern of Cybernetica's analysis. We can only infer that it is fine to declassify the comparisons if we inspect the body of the 'median' function.
int median_bob_2 (private int a1, private int a2, public int b1, public int b2) {
    declassify(median_comparisons(a1,a2,b1,b2));
    return median(a1,a2,b1,b2);
}

// the median by itself does not leak anything
int median (private int a1, private int a2, private int b1, private int b2) {
    private int a;
    private int b;
    if (a1 <= b1) {
        a = a2;
        b = b1;
    }
    else {
        a = a1;
        b = b2;
    }
    private int res;
    if (a <= b) {res = a;} else {res = b;}
    return declassify(res);
}

// auxiliary method to expose the intermediate comparisons
private int[[1]](2) median_comparisons (private int a1, private int a2, private int b1, private int b2) {
    private int a;
    private int b;
    if (a1 <= b1) {
        a = a2;
        b = b1;
    }
    else {
        a = a1;
        b = b2;
    }
    return { a1 <= b1, a <= b };
}


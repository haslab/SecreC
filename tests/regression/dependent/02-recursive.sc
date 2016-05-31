#OPTIONS_SECREC --checkassertions

uint f (uint n {n > 0}) {
    if (n > 1) { return f(n-1); }
    else { return n; }
}
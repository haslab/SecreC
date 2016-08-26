#OPTIONS_SECREC --verify

uint f (uint n)
//@ requires n > 0;
{
    if (n > 1) { uint r = f(n-1); return r; }
    else { return n; }
}
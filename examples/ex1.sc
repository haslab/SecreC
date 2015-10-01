
import stdlib; // import stdlib
import additive3pp; // import additive 3-party scheme
domain pd_a3p additive3pp; // declare a new private domain

void main ()
{
    pd_a3p uint a, b, c; // private data
    a = b + c; // private computation
    public uint d; // public data
    d = declassify (a); // private -> public
    publish (d); // send to client
}
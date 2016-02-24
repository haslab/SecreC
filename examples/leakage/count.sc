
kind additive3pp;
domain private additive3pp;

// the comparisons are not inferrable, since they reveal information about the position of the elements.
// this example would be more interesting if we first shuffled the input.
//@ leaks xs == z;
uint count (private uint[[1]] xs, private uint z) {
    bool[[1]] bs = declassify (xs == z);
    uint[[1]] cs = (uint) bs;
    public uint count = 0;
    for (uint i = 0; i < size(cs); ++i)
    {
        count += cs[i];
    }
    return count;
}
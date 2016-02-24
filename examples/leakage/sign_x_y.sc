module sign_x_y;

import stdlib;

kind additive3pp;
domain private additive3pp;

// We specify a leakage annotation in JML-like syntax. This function leaks the private comparison between the inputs.
//@ leaks x <= y;
public uint sign_x_y (private uint x, public uint y) {
    private bool b = x <= y;
    private uint r = (2 * y * (uint)!b) - (y * (uint)b);
    return declassify(r);
}

// knowledge inference must prove that the comparison can be computed from the public intput/output.
public uint sign_x_y_opt (private uint x, public uint y) {
    public bool b = declassify(x <= y);
    public uint r = (2 * y * (uint)!b) - (y * (uint)b);
    return r;
}
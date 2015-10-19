module sign_x_y;

import stdlib;

public uint sign_x_y ( private uint x, public uint y ) {
    private bool b = x <= y;
    private uint r = (2 * y * (uint)!b) - (y * (uint)b);
    return declassify(r);
}

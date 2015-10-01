import stdlib;
import additive3pp;
domain private additive3pp;

public uint sign_x_y ( private uint x, public uint y ) {
    private b = x <= y;
    if (b) return -y; else return y;
}

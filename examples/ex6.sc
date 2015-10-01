import stdlib;
import shared3p;
domain private shared3p;

public uint sign_x_y ( private uint x, public uint y ) {
    private b = x <= y;
    return (y * !b) - (y * b);
}

module sign_x_y;

import stdlib;
import shared3p;

// * Domain declarations (These should probably be builtins)

domain private shared3p;

function int declassify(private int x) {
    __builtin("core.declassify",x) :: int
}
function uint declassify(private uint x) {
    __builtin("core.declassify",x) :: uint
}
function bool declassify(private bool x) {
    __builtin("core.declassify",x) :: bool
}
function private int classify(int x) {
    __builtin("core.classify",x) :: private int
}
function private uint classify(uint x) {
    __builtin("core.classify",x) :: private uint
}
function private bool classify(bool x) {
    __builtin("core.classify",x) :: private bool
}

function private bool operator <= (private uint x,private uint y) {
    __builtin("core.le",x,y) :: private bool
}
function private uint operator - (private uint x,private uint y) {
    __builtin("core.sub",x,y) :: private uint
}
function private bool operator == (private bool x,private bool y) {
    __builtin("core.eq",x,y) :: private bool
}
function private bool operator ! (private bool x) {
    x == false
}
function private uint operator (uint) (private bool x) {
    __builtin("core.cast_bool_uint64",x)
}

//* Code

// We specify a leakage annotation in JML-like syntax. This function leaks the private comparison between the inputs.
//x //@ leaks x <= y;
public uint sign_x_y (private uint x, public uint y) {
    private bool b = x <= y;
    private uint r = x * y; //(2 * y * (uint)!b) - (y * (uint)b);
    return declassify(r);
}

//// knowledge inference must prove that the comparison can be computed from the public intput/output.
//public uint sign_x_y_opt (private uint x, public uint y) {
//    public bool b = declassify(x <= y);
//    public uint r = (2 * y * (uint)!b) - (y * (uint)b);
//    return r;
//}
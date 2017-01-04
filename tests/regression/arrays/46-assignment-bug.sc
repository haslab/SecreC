#OPTIONS_SECREC --implicitcoercions=defaultsc --backtrack=fullb --matching=gorderedm --promote=nop

void main () {
    int [[2]] arr (2, 2);
    arr[:,0] = arr[0,:]; // OK
    return;
}

#OPTIONS_SECREC --implicitcoercions=offc --backtrack=fullb --matching=gorderedm --promote=nop

void main () {
    uint [[1]] x (10);
    x[0] = 0;
    assert (size (x) == 10);
}

#OPTIONS_SECREC --implicitcoercions=onc --backtrack=fullb --matching=gorderedm --promote=nop

kind additive3p;
domain private additive3p;

void main () {
    private int [[1]] x (1);
    ++ x[0];
    ++ x;
    x[0] ++;
    x ++;
}

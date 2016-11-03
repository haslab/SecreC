#OPTIONS_SECREC --implicitcoercions=defaultsc

struct weird {
    int[[1]] a;
}

void main () {
    weird w;
    int[[1]] r;
    r = w.a;
    r = w.a;
}

#OPTIONS_SECREC --implicitcoercions=onc --backtrack=fullb --matching=gorderedm --promote=nop

void main () {
    int [[2]] arr (2, 2);

    {
        int [[1]] brr;
        brr = ++ arr [:,0];
        brr = arr [0,:] ++;
        brr = -- arr [:,1];
        brr = arr [1,:] --;
    }

    {
        int[[2]] brr;
        brr = ++ arr [:,:];
        brr = arr [:,:] ++;
        brr = -- arr [:,:];
        brr = arr [:,:] --;
    }

    assert (true);
}

#OPTIONS_SECREC --implicitcoercions=defaultsc --backtrack=tryb --matching=gorderedm --promote=nop

bool all (bool[[1]] vec) {
    uint n = size (vec);
    for (uint i = 0; i<n; ++i) {
        if (!vec[i]) {
            return false;
        }
    }
    return true;
}

// \todo causes "double free or corruption" on pop_frame
// it looks like bug in VM, but could easily be code gen
void main () {
  bool [[1]] t (5);
  int [[1]] t2 (5);
  //hpacheco: changed "t" to "all t" to pass typechecker
  assert (size(all(t) ? t2 : t2) == 5);
}


kind a3p;
domain private a3p;

private bool classify (public bool x) {
    private bool y;
    return y;
}

public bool declassify (private bool x) {
    public bool y;
    return y;
}

void main () {
  private bool t = true;
  assert (declassify (t));
}

struct infinite {
    infinite x;
    int y;
}

void main () {
    infinite i;
    i.x = i;
    i.x.x = i;
    i.y = 1;
}
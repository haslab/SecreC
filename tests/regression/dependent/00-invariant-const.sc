#OPTIONS_SECREC --verify --implicitcoercions=offc

uint bar (const uint n)
//@ requires n > 0;
{
   return 0; 
}
void foo () {
    uint n = 1 + 3;
    bar(n);
}
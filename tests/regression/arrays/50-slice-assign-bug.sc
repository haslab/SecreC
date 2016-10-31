#OPTIONS_SECREC --implicitcoercions=offc

void main() {
    uint8 [[1]] src(1);
    uint8 [[1]] dest(1);
    const uint m = 1; // hpacheco: added const to allow static size checking
    dest[: 0 + m] = src[:];
}

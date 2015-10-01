
import stdlib;
template <domain D>
D uint count (D uint32[[1]] data, D uint32 value) {
    return sum (data == value);
}
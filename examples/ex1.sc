
module matrix;

//import stdlib;

template <domain D, type T>
D T[[1]] _sum (D T[[1]] vec, uint k) {
    //uint n = size(vec);
    //assert(k > 0 && n % k == 0);
    D T[[1]] sumsOfSubArrs (k);
    //uint subArrLen = n/k;
    //uint subArrStartIdx = 0;
    //for (uint i = 0; i<k; ++i) {
    //    sumsOfSubArrs[i] = sum(vec[subArrStartIdx : subArrStartIdx+subArrLen]);
    //    subArrStartIdx += subArrLen;
    //}
    return sumsOfSubArrs;
}


//template <domain D, type T, dim N>
//D T[[1]] flatten (D T[[N]] arr) {
//    return reshape(arr,size(arr));
//}

template <domain D, type T>
D T[[1]] _rowSums (D T[[2]] mat) {
    return _sum(mat[0],0);
    //return sum(flatten(mat), shape(mat)[0]);
}


//template <domain D>
//D float64[[1]] rowSums (D float64[[2]] mat) {
//    return _rowSums (mat);
//}
//
//template <domain D, type T>
//D T[[1]] _dotProduct (D T[[2]] x, D T[[2]] y) {
//    assert (shapesAreEqual (x,y));
//    return rowSums(x * y);
//}
//
//
//template <domain D>
//D float64[[1]] dotProduct (D float64[[2]] x, D float64[[2]] y) {
//    return _dotProduct (x, y);
//}
//
//
//float64[[1]] vecLength (float64[[2]] x) {
//    return sqrt (dotProduct (x, x));
//}

void main() {
    havoc float64[[2]] mat;
    _rowSums(mat);
}

Algorithm:
Gaussian elimination with pivoting

SecreC:
An abstract permutation performed on the input.

Assumptions:
Properties of shuffle, that rely on distributions, need to be proved separately.
Namely, of we shuffle an array together with a permutation, and declassify the permutation and apply the shuffled public permutation to the shuffled array, leaking nothing.

Execute:
secrec examples/leakage/gaussian/gaussian.sc --debugtransformation --debugtypechecker --debugverification --progress

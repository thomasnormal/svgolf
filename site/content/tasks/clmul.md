Multiply two polynomials over GF(2): bit `k` of the `2N-1`-bit result is the XOR, over all `i + j = k`,
of `a[i] AND b[j]`. This is multiplication with the carries removed, the operation behind GHASH, CRCs and
binary-field cryptography. The proof covers every `N ≥ 1`; the score is taken at `N = 16`.

Run-time `+ - *` are banned. The proved `N × N` AND/XOR array has 3429.5 µm² and a 1.11 ns critical
path on sky130 (772.267 GE, depth 6). It is the first task whose best known designs are recursive: an
unproved Karatsuba circuit is about a fifth smaller, 2756.4 µm², but slower, 1.80 ns (621.959 GE, depth 8).

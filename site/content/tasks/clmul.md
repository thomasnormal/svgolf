Multiply two polynomials over GF(2): bit `k` of the `2N-1`-bit result is the XOR, over all `i + j = k`,
of `a[i] AND b[j]`. This is multiplication with the carries removed, the operation behind GHASH, CRCs and
binary-field cryptography. The proof covers every `N ≥ 1`; the score is taken at `N = 16`.

Run-time `+ - * / % **` and the ordering comparisons `< <= > >=` are banned. The proved `N × N` AND/XOR array has {{clmul_n.area}} and a {{clmul_n.time}}
critical path on sky130 ({{clmul_n.ge}}, depth {{clmul_n.depth}}). It is the first task whose best known designs
are recursive: an unproved Karatsuba circuit is about a fifth smaller, {{kara_b4_16.area}}, but slower,
{{kara_b4_16.time}} ({{kara_b4_16.ge}}, depth {{kara_b4_16.depth}}).

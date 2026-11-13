Multiply two unsigned `N`-bit numbers: `p = a * b`, all `2N` bits of the product, for every `N ≥ 1`,
scored at `N = 16`.

Run-time `+ - * / % **` and the ordering comparisons `< <= > >=` are banned, so the multiplier is built from partial products and adders made of
gates. Par is the proved array multiplier: {{mul_n.area}} and a {{mul_n.time}} critical path on sky130
({{mul_n.ge}}, depth {{mul_n.depth}}), {{mul_n.score}}. Carry-save trees (Wallace's, Dadda's) are much faster
for a little more area.

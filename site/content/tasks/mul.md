Multiply two unsigned `N`-bit numbers: `p = a * b`, all `2N` bits of the product, for every `N ≥ 1`,
scored at `N = 16`.

Run-time `+ - * / % **` are banned, so the multiplier is built from partial products and adders made of
gates. The proved array multiplier has {{mul_n.area}} and a {{mul_n.time}} critical path on sky130
({{mul_n.ge}}, depth {{mul_n.depth}}). The proved tree references are much faster for a little more area:
par is the tree `mul_tree_h`, {{mul_tree_h.area}} at {{mul_tree_h.time}}, {{mul_tree_h.score}}. An unproved
Dadda tree with a ripple final adder is both smaller and faster than par, {{dadda_rc_16.area}} at
{{dadda_rc_16.time}} ({{dadda_rc_16.score}}): proving a tree like it is the open challenge.

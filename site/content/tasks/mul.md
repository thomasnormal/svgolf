Multiply two unsigned `N`-bit numbers: `p = a * b`, all `2N` bits of the product, for every `N ≥ 1`,
scored at `N = 16`.

Run-time `+ - * / % **` are banned, so the multiplier is built from partial products and adders made of
gates. The proved array multiplier has 8290.5 µm² and a 10.8 ns critical path on sky130 (1962.576 GE,
depth 88); the proved tree references reach 5.91 ns for more area, and an unproved Dadda tree with a
ripple final adder has 8230.4 µm² at 5.40 ns. Proving a tree that is both smaller and faster than the
array is the open challenge.

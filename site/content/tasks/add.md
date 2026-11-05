Add two `N`-bit numbers and a carry in: `s` is the low `N` bits of `a + b + cin` and `cout` the carry
out of the top bit. The proof covers every width `N ≥ 1`; the score is taken at `N = 16`.

The circuit must be built from bitwise logic, multiplexers, selects and concatenations: run-time
`+ - * / % **` are banned, because addition is the task (constant arithmetic on parameters and genvars
stays allowed). The proved ripple-carry reference has 460.4 µm² and a 2.59 ns critical path on sky130
(112 GE, depth 33). Parallel-prefix adders trade area for delay (Sklansky 541.8 µm² at 2.43 ns, Kogge-Stone
641.9 µm² at 2.05 ns, both simulated but not yet proved), so there is a real frontier to golf.

Add two `N`-bit numbers and a carry in: `s` is the low `N` bits of `a + b + cin` and `cout` the carry
out of the top bit. The proof covers every width `N ≥ 1`; the score is taken at `N = 16`.

The circuit must be built from bitwise logic, multiplexers, selects and concatenations: run-time
`+ - * / % **` and the ordering comparisons `< <= > >=` are banned, because addition is the task (`==` and `!=`
stay allowed, and so does constant arithmetic on parameters and genvars). Par is the proved ripple-carry adder:
{{add_n.area}} and a {{add_n.time}} critical path on sky130 ({{add_n.ge}}, depth {{add_n.depth}}), {{add_n.score}}.
Parallel-prefix adders such as Sklansky's and Kogge-Stone's trade area for delay.

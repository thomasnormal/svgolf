Add two `N`-bit numbers and a carry in: `s` is the low `N` bits of `a + b + cin` and `cout` the carry
out of the top bit. The proof covers every width `N ≥ 1`; the score is taken at `N = 16`.

The circuit must be built from bitwise logic, multiplexers, selects and concatenations: run-time
`+ - * / % **` and the ordering comparisons `< <= > >=` are banned, because addition is the task (`==` and `!=`
stay allowed, and so does constant arithmetic on parameters and genvars). The proved ripple-carry reference has {{add_n.area}} and a {{add_n.time}} critical path on
sky130 ({{add_n.ge}}, depth {{add_n.depth}}), {{add_n.score}}: par. Parallel-prefix adders trade area for
delay (Sklansky {{add_n_sklansky.area}} at {{add_n_sklansky.time}}, Kogge-Stone {{add_n_kogge_stone.area}} at
{{add_n_kogge_stone.time}}, both simulated but not yet proved); on sky130's area × time neither is ahead of the ripple
yet ({{add_n_sklansky.score}} and {{add_n_kogge_stone.score}}).

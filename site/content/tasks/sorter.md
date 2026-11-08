Take `N` unsigned `W`-bit values, one per cycle, and give them back in ascending order, one per cycle,
duplicates kept. The design has a clock, a synchronous reset and a stream handshake: `start`, then
`in_valid` and `in_data` in, `out_valid` and `out_data` out. The proof covers every `N, W ≥ 1` with `N·W < 2^31` and proves
the latency the submission declares; the score is taken at `N = 8, W = 8`.

No operator is banned but run-time `/ % **`, as in every task: comparisons are the task. The score is the
area times the time, the latency in cycles times the clock period. No design can finish before `2N - 1` cycles, because the smallest value
depends on the last input; the proved reference, an insertion-cell array, takes `2N` (16 cycles at the
scoring point) for {{sorter_ins.ge}}.

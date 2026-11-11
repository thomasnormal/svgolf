Take `N` unsigned `W`-bit values, one per cycle, and give them back in ascending order, one per cycle,
duplicates kept, behind a stream handshake: `start`, then `in_valid` and `in_data` in, `out_valid` and `out_data`
out. `out_data` is claimed only at the cycles where `out_valid` = 1, which show the sorted values in order;
`out_valid` is known at every cycle from the release and 0 until the first start. The proof covers every `N, W ≥ 1` with `N·W < 2^31` and proves
the latency the submission declares; the score is taken at `N = 8, W = 8`.

The design is clocked by `clk` alone, on its rising edge, with the synchronous reset `rst`: no asynchronous
process, and `clk` is never read as data. No output may depend combinationally on an input; the claims hold from every power-up value of every register,
the first reset included; no construct may create an unknown value, and a register that is never loaded is
refused. No operator is banned but run-time `/ % **`, as in every task: comparisons are the task. Any schedule is
allowed, and [the score](#score) prices it: an insertion array, a sorting network behind serial-parallel buffers,
a merge structure. No design can finish before `2N - 1` cycles, because the smallest value
depends on the last input; the proved reference, an insertion-cell array, takes `2N` (16 cycles at the
scoring point) for {{sorter_ins.ge}}.

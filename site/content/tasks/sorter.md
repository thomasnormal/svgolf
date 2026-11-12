Take `N` unsigned `W`-bit values, one per cycle, and give them back in ascending order, one per cycle,
duplicates kept, behind a stream handshake: the environment raises `start` only while the design is idle,
then drives `in_valid` = 1 with one value on `in_data` in exactly the `N` cycles after it, and the design
answers on `out_valid` and `out_data`, every value out at most its declared latency after the cycle that
samples `start` (cycle 0).

`out_data` is claimed only at the cycles where `out_valid` = 1, which show the sorted values in order;
`out_valid` is known at every cycle from the release and 0 until the first start. The proof covers every
`N, W ≥ 1` with `N·W < 2^31` and proves the latency the submission declares; the score is taken at `N = 8, W = 8`.

The design is clocked by `clk` alone, on its rising edge, with the synchronous reset `rst`: no asynchronous
process, and `clk` is never read as data. No output may depend combinationally on an input; the claims hold from every power-up value of every register,
the first reset included; no construct may create an unknown value, and a register that is never loaded is
refused. No operator is banned but run-time `/ % **`, as in every task: comparisons are the task. Any schedule is
allowed, and [the score](#score) prices it: an insertion array, a sorting network behind serial-parallel buffers,
a merge structure. No design can finish before `2N - 1` cycles, because the smallest value
depends on the last input.

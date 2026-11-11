Multiply two `N × N` matrices of signed `W`-bit entries: `C = A · B`, every sum wrapping at `AccW` bits.
A handshake frames each product: the design reads `A` and `B` when `start` is pulsed, and after each start raises
`done` once `C` holds the product. `C` is claimed only from the first `done` = 1 after a start until the next
start, where it must hold the product; at every other cycle it may show anything, while `done` is known at every
cycle from the release and 0 until the first start. The proof covers every `N, W, AccW ≥ 1` with `N·N·W < 2^31` and `N·N·AccW < 2^31` and proves the
latency the submission declares; the score is taken at `N = 4, W = 8, AccW = 32`.

The design is clocked by `clk` alone, on its rising edge, with the synchronous reset `rst`: no asynchronous
process, and `clk` is never read as data. No output may depend combinationally on an input; the claims hold from every power-up value of every register,
the first reset included; no construct may create an unknown value, and a register that is never loaded is
refused. Every operator but run-time `/ % **` (banned in every task) is allowed, `*` included, so the task is the
schedule, which [the score](#score) prices: how many multipliers, how many cycles and how short a cycle. Any
schedule is allowed: `N²` multiply-accumulate units at once, fewer units over more cycles, a systolic array.
The proved reference, `N²` multiply-accumulate units stepping through `k`, takes `N` cycles (4 at the
scoring point) for {{matmul_g1.ge}}.

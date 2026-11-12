Multiply two `N × N` matrices of signed `W`-bit entries: `C = A · B`, every sum wrapping at `AccW` bits.
A handshake frames each product: the environment raises `start` only while the design is idle and holds `A`
and `B` from `start` until `done` rises, and after each start the design raises `done` once `C` holds the
product, at most its declared latency after the cycle that samples `start` (cycle 0).

`C` is claimed only from the first `done` = 1 after a start until the next start, where it must hold the
product; at every other cycle it may show anything, while `done` is known at every cycle from the release and 0
until the first start. The proof covers every `N, W, AccW ≥ 1` with `N·N·W < 2^31` and `N·N·AccW < 2^31` and
proves the latency the submission declares; the score is taken at `N = 4, W = 8, AccW = 32`.

The design is clocked by `clk` alone, on its rising edge, with the synchronous reset `rst`: no asynchronous
process, and `clk` is never read as data. No output may depend combinationally on an input; the claims hold
from every power-up value of every register, the first reset included; no construct may create an unknown
value, and a register that is never loaded is refused. Every operator but run-time `/ % **` (banned in every
task) is allowed, `*` included, and any schedule goes: `N²` multiply-accumulate units at once, fewer units
over more cycles, a systolic array. [The score](#score) prices the schedule.

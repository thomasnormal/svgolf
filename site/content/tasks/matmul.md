Multiply two `N × N` matrices of signed `W`-bit entries: `C = A · B`, every sum wrapping at `AccW` bits.
The design has a clock, a synchronous reset and a handshake: it reads `A` and `B` when `start` is pulsed,
and raises `done` when `C` holds the product. The proof covers every `N, W, AccW ≥ 1` with `N·N·W < 2^31` and `N·N·AccW < 2^31` and proves the
latency the submission declares; the score is taken at `N = 4, W = 8, AccW = 32`.

Every operator but run-time `/ % **` (banned in every task) is allowed, `*` included, so the task is the
schedule: how many multipliers, how many cycles and how short a cycle. The score is the area times the
time, the latency in cycles times the clock period.
The proved reference, `N²` multiply-accumulate units stepping through `k`, takes `N` cycles (4 at the
scoring point) for {{matmul_g1.ge}}.

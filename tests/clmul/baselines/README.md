# Proved designs of task `clmul` besides the reference: entries

Every design here comes with a kernel-checked proof of the task's statement for every `N` in range, its `.lean`
beside it (decided 2026-11-12: every design the site shows is proved). None uses a banned operator, so each is an
ENTRY (decided 2026-11-12: par is one design per task, the simplest algorithm, `leaderboard/par.json`: here the array
`clmul_n`; every other proved design is an entry), recorded on the board under a handle of its own like any
player's, and shown on the site once that record exists; `clmul_tree` scores below par. `tests/run.py`,
step `baseline-proofs`, checks each proof through `check.py` (accepted, standard axioms only); the scores at
`N = 4, 8, 16, 32` are in `tests/expected.json` and re-measured by `tests/run.py`.

* `clmul_tree.sv` + `clmul_tree.lean`: the schoolbook product, all `N^2` partial products, each output column `k`
  summed by an XOR tree, written once for every `N`: one 2-D array `T` holds a TAPE per column (its first `N`
  positions the zero-padded partial products, XOR node `g` at position `N + g` from positions `2g` and `2g + 1`,
  the root at `2N - 2`). Proved with the `sv_comb` tactics (a window invariant by induction on `g`). It is the
  parametric form of the one-width generated `school_tree_<N>.sv` (`tests/clmul/unproved/`): the same XOR trees in
  every column at `N = 1, 2, 4, 8, 16, 32` (pairing in heap order elsewhere, at most one level deeper than
  balanced).
* `kara_lv.sv` + `kara_lv.lean`: Karatsuba with a 4-bit schoolbook base, written level by level for every `N`:
  operands padded to `P = 4 * 2^L`, `L = $clog2((N + 3) / 4)`, level `l` with `3^l` nodes whose children take the
  low half, the high half and their XOR, each higher level combining its children column by column. Proved by
  hand (the tactics refuse `**` in a localparam). The parametric form of `kara_b4_<N>.sv`: the same expression
  trees at `N <= 4` and `N = 8, 16, 32` (another assign order, so ABC's result differs a little: +10.2 % in area x
  time at `N = 8`, -0.7 % at 16, -5.7 % at 32, measured against the generated files).
* `clmul_k1.sv` + `clmul_k1.lean`: one level of Karatsuba for every `N` (`H = (N + 1) / 2`, three `H x H`
  schoolbook arrays `L`, `Hh`, `M` and a combination layer; the same file as
  `design/tasks-week2/clmul/karatsuba/clmul_k1u.sv`), proved with the tactics.

Validation: Verilator (`tests/clmul/validate/sim.py DESIGN --plan quick` in `tests/run.py`, the full plan with
`--full`: exhaustive at `N = 1..8`, 100 000 random vectors at ten widths up to 64).

| design | N = 4 | N = 8 | N = 16 | N = 32 |
|---|---|---|---|---|
| reference array (`tasks/clmul/reference/clmul_n.sv`, proved) | 38.329 / 3 | 179.649 / 4 | 772.267 / 6 | 3214.731 / 7 |
| `clmul_tree.sv` | 38.329 / 3 | 179.649 / 4 | 772.267 / 5 | 3222.057 / 6 |
| `kara_lv.sv` | 38.329 / 3 | 166.32 / 6 | **616.626 / 8** | **2056.88 / 10** |
| `clmul_k1.sv` | 43.663 / 4 | 167.32 / 6 | 651.95 / 7 | 2556.137 / 8 |

(area in NAND2 GE / depth in gates; every number, with its gate mix, is in `tests/expected.json`, which
`tests/run.py` checks.) At `N = 16` the Karatsuba recursion is about a fifth smaller than the array and deeper.
The one-width generated netlists (the schoolbook trees and the 2-bit, 4-bit, 8-bit and full-depth Karatsuba
recursions of `gen_clmul.py`) were baselines here until 2026-11-12: they are test material in
`tests/clmul/unproved/` now, shown nowhere on the site; their numbers are in `tasks/clmul/README.md`.

# Task `_example`: N-bit bitwise AND

A toy task. It exists to exercise the whole svGolf pipeline (statement,
proof, checker, banlist, scoring) on a design whose optimum is obvious, and
to serve as the template for real tasks.

## The circuit

Write a module with exactly this header (port names, directions, widths and
order matter; the parameter must be called `N`):

```systemverilog
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
```

It must compute `y = a & b`, bit by bit, combinationally.

## The statement (`Spec.lean`, trusted)

```lean
def task : CombTask where
  inRange N := 1 ≤ N ∧ N < 2 ^ 31
  inputs N := [("a", N), ("b", N)]
  outputs N := [("y", N)]
  fn _ := fun (a, b, ()) => (a &&& b, ())

abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement
```

For every `N` with `1 ≤ N < 2^31`: the design's ports are exactly `a`, `b` (inputs, `N`
bits) and `y` (output, `N` bits); there is no combinational loop; every run terminates under every schedule
and stimulus; and every cycle whose stimulus drives `a` and `b` with known
values ends with `y = a &&& b`. `SvGolf/Task.lean` defines `CombTask` and
explains why the statement cannot be met vacuously.

The range ends below `2^31` (decided 2026-11-06): the port widths are `int` expressions of `N`
(`[N-1:0]`), and an `int` holds no value of `2^31` or more. Every task's range keeps every width it
implies below `2^31`.

## Rules for this task

* Banned run-time operators: `+ - * / % **` (only to exercise the banlist;
  constant arithmetic such as `N-1` or a genvar loop is fine). As in every
  task that bans `+` or `-`, run-time ordering comparisons (`< <= > >=`)
  are banned too (decided 2026-11-05): Yosys's `alumacc` builds each as an
  `$alu`, its own adder, and the backstop rejects the `$alu` cells it
  builds. Equality (`== !=`) and comparisons over parameters stay allowed.
* Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `bv_decide` (not
  supported, the repository's `README.md`, "`bv_decide`"; `tests/run.py` `bv_decide_subgoal_*`).
* Proof time limit: 300 CPU s, the one limit of every task (svGolf `README.md`, "Proof effort": the references compile in at most 3.3 CPU s, three cold runs each, 2026-11-06; it was 600 s, then 120 s of wall clock).
* Scored at `N = 16`, no depth budget. The one ranked number is area x
  time on sky130 A0' (A0' decided 2026-11-03, the product 2026-11-05; svGolf
  `README.md`, "Scoring"): the cell area in um^2 times the critical-path
  delay of the scored netlist of the pinned two-stage flow, weighed by
  `score/ppa.py` (`sky130_a0_v3`). Par, the reference `band`, is
  100.096 um^2 x 280 ps = 28.03 um2*ns, and it is optimal. The Pareto
  frontier of area and time, area in NAND2 gate equivalents and depth in
  gates are extra columns, for exploring. `python3.12 score/ppa.py
  solution.sv --task tasks/_example --no-mapped` measures a design in about
  a second, with no Lean. The score is deterministic, the same file always
  scoring the same: names, comments, whitespace and the file name never
  change it, while operand order, gate forms and the order of statements can,
  and trying them is golf (svGolf `README.md`, "Scoring"). Every number can be
  reproduced bit for bit: score/PPA.md, "Reproduce a score".
* Post-synthesis check (`task.json` `postsynth`): ls-sv's reading and the
  scored netlist must agree on the fixed corners, the harvested comparison
  constants and 4000 seeded random vectors (4130 vectors, 0.3 s measured).
* No x or z value may arise (README.md, "Rules"): no x/z literal digit
  outside a casez/casex item wildcard (the source gate), and no parameter
  with unknown bits, out-of-range select or undriven net at `N = 16` (the
  `fourstate` stage). `tests/_example/attacks/` has the designs these rules
  exist for, each computing `a & b` in ls-sv and something else in Yosys: a
  `1'bx` case item (0 GE), complementary `z` items, a constant `1 / 0`, an
  undriven net, an out-of-range read; with the static rules bypassed, the
  post-synthesis check rejects each of them except `oob_rare.sv`, whose
  difference is one input pair in 2^32.
* **Input drive** (the sky130 score, `sky130_a0_v3`): every primary input is driven by `sky130_fd_sc_hd__buf_8`,
  the default (`task.json` names no `input_drive`), standing for the on-chip bus or register that feeds the block; the
  record says so in `ppa.setup.input_drive` (score/PPA.md, "The input drive").

## Reference

`reference/band.sv` (`assign y = a & b;`) with the for-all-`N` proof
`reference/band.lean`: 16 AND gates, **100.096 um^2, 280 ps** on sky130 A0'
(its record `leaderboard/data/_example/`, re-weighed by `leaderboard.py
verify`), 21.328 GE, depth 1 in the extra columns (checked by `tests/run.py`
against `tests/expected.json`).

**The short proof, and the one to start from:** `reference/band_tactics.lean`
proves the same statement for the same design (`reference/band_tactics.sv` is
`band.sv`, byte for byte) with the `sv_comb` tactics, in 38 code lines against
`band.lean`'s 159 (`leaderboard.py`'s `lean_code_lines`). It follows the route
of the first real task's proof, `tasks/add/reference/add_n.lean`:
`sv_structure` proves the comb profile and acyclicity (rank 0: the one assign
reads only the inputs), `sv_interface` the ports, and `sv_equations` states
the assign bit by bit (`eq_y_1 k`: bit `k` of `y` is the AND of bit `k` of `a`
and of `b`), so the arithmetic is one short bullet. Accepted by a full
`check.py` run (solution stage 7.2 s, 2026-11-05). The site's walk-through
copies this pair. `band.lean` is the same statement without tactics: it walks
the design's instantiation by hand, the recipe the tactics automate.

A further accepted solution, `reference/band_lp.sv` with
`reference/band_lp.lean` (all three are listed in `task.json` `references`),
declares localparams in the header (`W = N`, sizing the ports) and in the
body (`MSB = W - 1`): the task's parameter list is `N` only, and localparams
are the design's own business. Same score: on the board it is an entry that ties par.

The checker's source gate applies here as everywhere: no `` `ifdef ``, no
attributes, no `// synopsys ...` pragmas, no `unique`/`priority` case
(`README.md` at the svGolf root, "Rules"); `tests/run.py` runs the gate's
fixtures against this task.

## Negative designs

`tests/_example/negative/README.md` lists designs that must fail, with
kernel-checked refutations in `tests/_example/negative/Refute.lean`.

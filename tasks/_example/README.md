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
  inRange N := 1 ≤ N
  inputs N := [("a", N), ("b", N)]
  outputs N := [("y", N)]
  fn _ := fun (a, b, ()) => (a &&& b, ())

abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement
```

For every `N ≥ 1`: the design's ports are exactly `a`, `b` (inputs, `N`
bits) and `y` (output, `N` bits); every run terminates under every schedule
and stimulus; and every cycle whose stimulus drives `a` and `b` with known
values ends with `y = a &&& b`. `SvGolf/Task.lean` defines `CombTask` and
explains why the statement cannot be met vacuously.

## Rules for this task

* Banned run-time operators: `+ - * / % **` (only to exercise the banlist;
  constant arithmetic such as `N-1` or a genvar loop is fine).
* Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `bv_decide` (not
  supported, `svgolf/README.md`, "`bv_decide`"; `tests/run.py` `bv_decide_subgoal_*`).
* Proof time limit: 120 s (the floor of the rule in the svGolf `README.md`, "Proof effort": the references compile in 2.1 s; it was 600 s).
* Scored at `N = 16`, no depth budget. The ranked score is sky130 A0'
  (decided 11/03; svGolf `README.md`, "Scoring"): the cell area in um^2 and
  the critical-path delay in ps of the scored netlist of the pinned
  two-stage flow, weighed by `score/ppa.py` (`sky130_a0_v3`); the
  leaderboard keeps their Pareto frontier. Area in NAND2 gate equivalents
  and depth in gates are extra columns. The score depends on the circuit,
  not on its layout or names. Every number can be reproduced bit for bit: score/PPA.md, "Reproduce a score".
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

A second accepted solution, `reference/band_lp.sv` with
`reference/band_lp.lean` (both are listed in `task.json` `references`),
declares localparams in the header (`W = N`, sizing the ports) and in the
body (`MSB = W - 1`): the task's parameter list is `N` only, and localparams
are the design's own business. Same score.

The checker's source gate applies here as everywhere: no `` `ifdef ``, no
attributes, no `// synopsys ...` pragmas, no `unique`/`priority` case
(`README.md` at the svGolf root, "Rules"); `tests/run.py` runs the gate's
fixtures against this task.

## Negative designs

`tests/_example/negative/README.md` lists designs that must fail, with
kernel-checked refutations in `tests/_example/negative/Refute.lean`.

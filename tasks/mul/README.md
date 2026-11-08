# Task `mul`: N-bit unsigned multiplier

The main svGolf challenge: build an `N × N → 2N` unsigned multiplier out of
bitwise logic, prove it correct for EVERY width `N ≥ 1`, and make it small
and fast at `N = 16`.

**Par** is the proved two-row-leaf tree `mul_tree_h`: **8563.2128 um^2 x 5992 ps =
51 310.8 um2*ns**. The one ranked number is area x time, the sky130 A0' cell area
in um^2 times the critical-path delay (decided 11/05; the svGolf README,
"Scoring"); to beat par is to be accepted with a smaller product. The Pareto
frontier of area and time, the GE area and the depth are extra columns, for
exploring.

## Start a new design

A new multiplier is your own `solution.sv` (the header below; `+ - * / % **` are banned at run time) and a
`Solution.lean` that proves it for every `N ≥ 1`. Find the design without Lean, then check it once
without a proof:

```bash
python3.12 score/ppa.py solution.sv --task tasks/mul --no-mapped     # area and delay, about two seconds
python3.12 check.py tasks/mul solution.sv --unproved --tactics --stage-dir stage
```

The second command runs every stage that needs no proof, the task's oracle included (a wrong circuit is
named there, not deep in a proof), says whether the proof tactics read the design (`tactics.in_fragment`)
and leaves it staged in `stage/` for probe files ([PROVING.md, section 0](../../PROVING.md#0-the-loop)).

**The route: the `sv_comb` tactics, then the arithmetic of your rows** ([PROVING.md, sections
1 to 3](../../PROVING.md#1-the-shape-of-a-proof); complete proofs: `reference/mul_n.lean`, the array, 70 code
lines; `reference/mul_wallace.lean`, a Wallace tree as a tape of rows, 264; `reference/mul_tree_h.lean`, par):

1. `sv_structure (lexRank := key N)`: one driver per bit and no combinational loop (`CombDesign ∧ Acyclic`),
   ordered by your key, a lexicographic triple per site (`mulKey` in `mul_n.lean`: row, column, phase).
2. `sv_interface`: the ports, one line.
3. `sv_equations`: each assign as an equation over `Bool` and every driven bit known; 2-D signals are read
   as `st.cell "T" W r c`, and each field of your arithmetic lemma is one `sv_bridge eq_…` line.
4. The arithmetic, in plain Lean: the rows give `p = a * b`. An array is `CombLib.MulNetlistView` and
   `ideal_mul_view`; a tree proves the value of its leaf rows and that its reduction keeps the sum. A
   radix-4 Booth multiplier (accepted 2026-11-05) proved each Booth row's value, the recoding identity by
   induction on the rows, and reused the Wallace tape of `mul_wallace.lean` for the reduction.

**Lay the design out so the tactics take it** (what they refuse, with the messages: [PROVING.md, section
4](../../PROVING.md#4-what-the-tactics-accept-and-what-they-refuse)):

* continuous `assign`s of gates (`& | ^ ~`, `?:` and the other operators section 4 lists) in at most two
  nested `generate for` loops, every index and loop bound affine in `N` and the genvars;
* rows as the rows of 2-D arrays, `T[r][c]`; `sv_cover` finds the assign that writes a read by solving one
  unknown per index equation, so a read whose writer needs `r = i / W` and `c = i % W` is not covered;
* counts derived from `N` as integer localparams (`mul_tree_h.sv`'s `localparam integer H = (N + 1) / 2;`; a
  2-state `int` with `/` or `%` is refused);
* every declared bit driven at `N = 16`; a constant row gets a literal;
* a read of a zero-padded copy of an input keeps every index affine where a row starts at a moving column
  (the tree references' `ae`, read as `ae[c + 2*N - 1 - j] & b[j]`).

**What `sv_equations` prints**, the shapes the arithmetic lemma is written against (`sv_equations?` in a
probe file lists them for your design):

* a part select `bb[N:1] = b` as `bb (Int.toNat 1 + k) = b k`; a cell of row 0, `T[0][c]`, as the flat cell
  `T c` (`sv_bridge` matches it);
* a family that writes a constant row in a column loop leaves a `True ∧ …` that `omega` refuses after
  `sv_rowmajor`: close the structure goals with `first | omega | (simp only [true_and, and_true] at *; omega)`;
* write `T 0 c = (x || y)` with the parentheses: `=` binds tighter than `||`, and Lean accepts the
  unparenthesized hypothesis silently (as a `decide`), which `sv_bridge` then reports as different shapes.

**The skeleton** (`reference/mul_n.lean` is it, filled in for the array):

```lean
import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

namespace Submission
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

set_option maxHeartbeats 400000 in
theorem my_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (lexRank := myKey N)           -- your key, a `def` above (mul_n.lean's `mulKey`)
  all_goals (intros; sv_rowmajor; omega)

theorem my_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by
  sv_interface

-- your arithmetic: the rows' equations in, the product out (a structure of fields, as `MulNetlistView`)

set_option maxHeartbeats 400000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := my_struct N hN'
  refine CombTask.satisfiedAt_of_comb (my_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · -- the main goal: your arithmetic lemma, one `sv_bridge eq_…` per field (mul_n.lean)
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | sv_cover

end Submission
```

**Library lemmas that exist today** (the tables: [PROVING.md, section 6](../../PROVING.md#6-tips-the-library)):

* `LeanModels.Sv.CombLib`: `MulNetlistView`, `ideal_mul` and `ideal_mul_view` (the array's equations give the
  product), the bit-function value `bfVal` and its lemmas, `fullAdder_arith`, `ripple_row` (a final ripple
  adder), `sum_split`, `bitvec_eq_ofNat_of_val`, `rowMajor_inj`, `lexLt`;
* `LeanModels.Sv.Lib.XFVal`: `val_csa` (a carry-save row: sum plus twice the carry is the three inputs) and
  the value of windows, concatenations, extensions and constants;
* `SvState.cell`, `sv_bridge` and `sv_rowmajor`; `rmN` and `Key` (`LeanModels/Sv/CombViewArith.lean`) and
  `LeanModels.Sv.Lib.RowMajor`; the port bridges `SvState.lookup_eq_ofBitVec_bv`, `SvState.boolAt_ofBitVec`,
  `inKnown_ofBitVec`;
* the reductions are proved inside the references (a task ships no library: copy them): `mul_wallace.lean`'s
  `csa_row`, `csum` and `tape_mul`; `mul_tree_h.lean`'s `node_sum`, `lane_val` (a row read from the padded
  copy) and `heap_mul`.

Planned, not in the library yet: the Booth multiplier's generic carry-save tape theorem (any leaf rows on a
Wallace tape sum to the leaves modulo `2^W`) and its `bfVal` lemmas for rows built from windows and single
bits.

## The circuit

Write a module with exactly this header (port names, directions, widths and
order matter; the parameter must be called `N`):

```systemverilog
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
```

It must compute the full product `p = a * b` of the two unsigned inputs,
combinationally. Nothing is truncated: `p` has `2N` bits and every product
of two `N`-bit numbers fits.

## The statement (`Spec.lean`, trusted)

```lean
def task : CombTask where
  inRange N := 1 ≤ N ∧ N < 2 ^ 30
  inputs N := [("a", N), ("b", N)]
  outputs N := [("p", 2 * N)]
  fn N := fun (a, b, ()) => (BitVec.ofNat (2 * N) (a.toNat * b.toNat), ())

abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement
```

For every `N` with `1 ≤ N < 2^30`: the design's ports are exactly `a`, `b` (inputs, `N`
bits) and `p` (output, `2N` bits); no process is clocked (`Unclocked`) and
there is no combinational loop; every run terminates under every schedule and stimulus; and every cycle whose stimulus drives `a` and `b` with known
values ends with `p` holding the natural-number product `a * b` as a
`2N`-bit vector. `Spec.lean` also proves that this really is the untruncated
product (`fn_toNat`) and that it equals `BitVec` multiplication at double
width (`fn_eq_mul`). `SvGolf/Task.lean` defines `CombTask` and explains
why the statement cannot be met vacuously.

The range ends below `2^30`, not `2^31` (decided 2026-11-06): the port widths are `int` expressions of
`N` (`[2*N-1:0]`), and an `int` holds no value of `2^31` or more, so at `N ≥ 2^30` the elaborated
`2*N` wraps and the output port is not `2N` bits wide. Every task's range keeps every width it implies
below `2^31`.

## Rules for this task

* **Banned run-time operators: `+ - * / % **`**, including compound
  assignments (`+=`), `++`/`--` on signals, unary minus, and the system
  functions Yosys builds from adders (`$countones`, ...). Yosys's `alumacc`
  merges `+` chains into the same `$macc` cell as `*`, so all arithmetic is
  banned, not just `*`. The check is `score/banlist.py`: a pyslang
  front check on the source and a Yosys backstop (`$add $sub $neg $mul $macc
  $alu ...` cells after `proc; opt`) at `N = 1, 2, 8, 16`.
* **Run-time ordering comparisons (`< <= > >=`) are banned too** (decided
  2026-11-05): Yosys's `alumacc` builds each one as an `$alu`, its own adder,
  so after `proc; opt` the backstop also runs `alumacc` and rejects every
  `$alu`/`$macc` cell it builds, at the comparison's source line. Equality
  (`== != === !==`), comparisons over parameters and genvars (folded as
  constants) and a comparator built from `& | ^ ~` stay allowed.
* **Constant arithmetic is fine**: parameter expressions (`2*N-1`),
  localparams, genvar index arithmetic (`s[i-1][j+1]`), constant functions.
  Run-time index arithmetic is not (`x[sel+1]` with a signal `sel` builds an
  `$add`).
* **Genvar loops step by one.** `i++`, `i = i + 1`, `i += 1` and their
  decrementing forms are read; a stride (`i += 2`) or a parameter amount
  (`i = i + K`) is refused at the `design` stage (an ls-sv limit, not a rule).
* Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `bv_decide` (it runs an
  external SAT solver, which the checker does not support: `svgolf/README.md`,
  "`bv_decide`"; fixed-size subgoals can use `decide +kernel`), no `native_decide`,
  no `sorry`.
* Proof time limit: 300 CPU s (`task.json`), the one limit of every task (svGolf `README.md`,
  "Proof effort"; `score/time_limits.py` checks it against `score/time_limits.json`).
  Measured 2026-11-06 in CPU seconds, three cold runs each (`score/time_limits.json`): `mul_tree`
  37.1, 34.8 and 34.9, `mul_tree_h` 32.7, 32.3 and 33.7, `mul_wallace` 31.6, 30.1 and 28.7,
  `mul_n` 16.4, 16.9 and 16.1, `mul_n_byhand` 14.1, 14.6 and 13.8 CPU s, all under the 150 CPU s target.
  Before, in wall-clock seconds: `mul_tree` was the slowest reference of any task in these wall-clock runs, over the
  60 s target of the former 120 s limit.
  Measured 2026-10-30, three cold runs each (`check.py`'s `solution` stage, on a shared
  machine under `LEAN_NUM_THREADS=2`): the single-row tree reference (`mul_tree.lean`, 594 code
  lines) 87.1, 86.8 and 100.0 s; the two-row-leaf tree
  (`mul_tree_h.lean`, 546 code lines, with a localparam) 71.3, 69.2, 71.3 s; the Wallace tape
  (`mul_wallace.lean`, 446 code lines) 42.2 s; the tactic array reference (`mul_n.lean`, 235 code
  lines) 37.3 s; the by-hand one (`mul_n_byhand.lean`, 1385 code lines) 12.4 s
  (`tests/mul/results/check.json` is an older record of the by-hand one: 8.4 s). The limit was
  900 s (ten times the slowest, 83.6 s then); it will be re-set after the proof-speed package.
* **Scoring at `N = 16`**, no depth budget. The ranked number is area x time
  on sky130 A0' (A0' decided 11/03, the product 11/05; svGolf `README.md`,
  "Scoring"): the cell area in um^2 times the critical-path delay of the
  scored netlist of the pinned two-stage Yosys + ABC flow, weighed by
  `score/ppa.py` (`sky130_a0_v3`). The Pareto frontier of area and time (the
  array reference 8290.4512 um^2 at 10907 ps is on it,
  `score/tests/ppa/expected_ppa.json`), area in NAND2 gate equivalents and
  depth in gates are extra columns, for exploring. The score is deterministic,
  the same file always scoring the same: names, comments, blank lines,
  whitespace and the file name never change it, while operand order, how a
  chain of gates is grouped, gate forms and the order of statements do, and
  trying them is golf (svGolf `README.md`, "Scoring"; moving one generate
  block of a proved multiplier ahead of another moved its area 12.6% and its
  delay 41%, measured 2026-11-05). Every number can be reproduced bit for bit:
  score/PPA.md, "Reproduce a score". `N = 8` and `N = 32` are reported
  alongside (not scored).
* Post-synthesis check (`task.json` `postsynth`): ls-sv's reading and the
  scored netlist must agree on the fixed corners (130 vectors), the
  harvested comparison constants and 200 seeded random vectors at `N = 16`.
  The budget is small because ls-sv's `run2` takes about 130 ms per vector
  (both schedules) on the 1026-process array multiplier: 47 s measured for
  the reference (83 s and 162 s for the 16-bit Dadda baselines), the slowest
  stage of its check after the build. That is the FULL mode (what
  competitions, `leaderboard.py add`/`verify` and `tests/run.py` run); `check.py`'s default,
  the LIGHT mode for local feedback, runs a subset of 40 of the 330 vectors
  (`light_vectors`): 5.6 s on `mul_tree_h`, 6.1 s on `mul_n`, 15 s on `mul_wallace` and
  21 s on `mul_tree` (the full stage: 41, 44, 119 and 167 s; README.md, "Checking"). The
  32-bit Dadda baselines are not
  checked: `run2` takes seconds per vector there, and even the fixed corners
  overran the 900 s cap (`tests/expected.json`, `postsynth_why`).
* No x or z value may arise (README.md, "Rules"): no x/z literal digit
  outside a casez/casex item wildcard (the source gate), and no parameter
  with unknown bits, out-of-range select, undriven net or logic loop at
  `N = 16` (the `fourstate` stage, 0.55 s for the reference). A run-time
  index into a partial-product or carry array must stay in the declared
  range for every value its type allows: pad the array to a power of two
  or narrow the index. The reference and every baseline pass both.
* **Input drive** (the sky130 score, `sky130_a0_v3`): every primary input is driven by `sky130_fd_sc_hd__buf_8`,
  the default (`task.json` names no `input_drive`), standing for the on-chip bus or register that feeds the block; the
  record says so in `ppa.setup.input_drive` (score/PPA.md, "The input drive").

## What counts as a solution

A file `solution.sv` with the module above, and a Lean file
`Solution.lean` that imports `Submission.Design` and proves

```lean
theorem Submission.solution : Submission.Goal
```

(inside `namespace Submission`, as every reference writes it: `theorem solution :
Goal`), where `Submission.Goal` is `SvGolf.Tasks.Mul.Statement design.sem` for the
design the checker extracts from `solution.sv` (the svGolf `README.md`,
"Submitting"; file names and paths are free). Check it with

```bash
python3.12 check.py tasks/mul solution.sv Solution.lean
```

## Reference solution

`reference/mul_n.sv` is the classic array multiplier: partial products
`pp[i][j] = a[j] & b[i]`, then `N - 1` rows of `N`-bit ripple-carry adders
built from full adders in generate loops (row `i` adds the upper `N` bits of
row `i - 1` to `pp[i]`); output bit `i < N` is bit 0 of row `i`, the top
`N` bits are the upper bits of the last row. It is the `mul2d` design of
lean-surfaces (`Examples/system-verilog/mul2d`) under the task's header.

The statement is proved **for every `N ≥ 1`** (standard axioms only; nothing
unrolled, nothing bit-blasted) twice for this design, and once more for each of two
tree-shaped designs (`reference/mul_tree.sv` and `reference/mul_wallace.sv`, below). The array
multiplier's two proofs are for the same design
(`reference/mul_n_byhand.sv` is a byte-identical copy of `reference/mul_n.sv`
that goes with the by-hand proof; `tests/run.py` checks the bytes):

* `reference/mul_n.lean` (70 code lines, 213 before WP-P3/P4) uses the `sv_comb` tactics of
  lean-surfaces: `sv_structure` (`CombDesign ∧ Acyclic` in one theorem, goals closed by
  `intros; sv_rowmajor; omega`, from a 12-line lexicographic key `(row, column, phase)`
  and `maxHeartbeats 400000`), `sv_interface` (the ports), `sv_equations` (the eleven equations of the 2-D
  netlist, one `eq_*` per group of assigns, and their knownness), and the
  library `LeanModels.Sv.CombLib` (`MulNetlistView`, `ripple_row`, the row
  induction `ideal_mul_view`). `sv_cover` closes the six coverage goals of the nested 2-D reads
  (`cover_2`, `cover_4` to `cover_8`) by solving the loop indices of each writer from the read (its 2-D
  rule, WP-P4; before it they were closed by hand, about 75 lines), and `sv_bridge` closes the twelve
  fields of `MulNetlistView` from the printed equations (WP-P3; before it `mul_final`, about 80 lines,
  restated every equation and cast its indices).
  [PROVING.md](../../PROVING.md), section 3, walks through the file.
* `reference/mul_n_byhand.lean` (1385 code lines) proves it with no tactic. Its
  docstring is the map; in short:

  1. **arithmetic**: the row sums `R 0 = x·y₀`, `R (i+1) = R i / 2 + x·y_{i+1}`
     satisfy `x * (y mod 2^(i+1)) = 2^i * R i + L` with `L < 2^i`, so bit
     `k < N` of the product is bit 0 of row `k`, and bit `N + j` is bit
     `j + 1` of the last row;
  2. **the design at symbolic `N`**: the process list of `design.sem N`
     (adapted from `mul2d/gen.lean`);
  3. **comb profile and acyclicity**: write windows from the one-driver rule,
     a row-major rank certificate checked reader by reader;
  4. **the settled state**: by induction on the row, then on the bit inside a
     row, row `i` of `s` holds `R i` (carries are core's `BitVec.carry`, sums
     `BitVec.getLsbD_add`); `CombTask.satisfiedAt_of_comb` closes the
     statement.

### A third reference: a carry-save tree (`mul_tree`)

`reference/mul_tree.sv` is a **log-depth tree** of full adders, parametric in `N`, with a
ripple-carry final adder. The `N` partial-product rows are the `N` leaves (nodes `N-1 .. 2N-2`) of a
binary HEAP: node `k` has the children `2k+1` and `2k+2`, the root is node 0, and the `N-1` internal
nodes `0 .. N-2` are the tree. A leaf is one row of the product (`S = a·b_j·2^j`, `C = 0`); an
internal node whose children are both leaves (`2k+1 ≥ N-1`) just pairs them, `(S, C) = (S[2k+1],
S[2k+2])`, and every other internal node is a 4:2 compressor, two stacked rows of 3:2 counters
(`X`/`Y`, then `S`/`C`), on its children's pairs. Which nodes pair and which compress is a
multiplexer whose select is a CONSTANT (`th[2k+1]`, a thermometer vector `th[x] = (x ≥ N-1)` built by
two generate loops), so synthesis removes the pairing nodes' compressors. The carry-save part has
`⌈log₂ N⌉ - 1` levels of two full adders each; constant-zero operands (the triangular shape of the
shifted rows, a leaf's zero carry row) turn full adders into half adders and wires in synthesis, which
is where the 2:2 counters come from. It is not a column-by-column Wallace or Dadda tree (those need a
stage count and column heights computed from `N`: `$clog2`, `N/2`, a 3-D array, conditional
generate), but it is a log-depth carry-save reduction with a carry-propagate adder at the end, and it
needs none of that: **no localparam, no division, no conditional generate and no stage loop**,
because the heap numbering replaces the stage index and a constant vector replaces the
conditional. Two choices keep every index and bound AFFINE in `N` and the genvars, which is what
`sv_structure` reads: the shifted partial products are GATHER reads of `ae`, a zero-padded copy of
`a` (`S[N-1+j][c] = ae[c+2N-1-j] & b[j]`), so no write ever leaves its vector, and every sum is taken
modulo `2^(2N)`, exactly the product width, so the dropped top carries need no argument.

The proof (`reference/mul_tree.lean`, 322 code lines since WP-P3/P4, 571 before; standard axioms; PROVING.md, section 8) is
the tactic proof of the array multiplier with a different arithmetic core. By part: `sv_structure`
(40 goals for `CombDesign`, 69 for `Acyclic`, all `intros; sv_rowmajor; omega`, and a
13-line lexicographic key `(stage, node order, phase)`; 20 lines), the ports (`sv_interface`), `sv_equations` (20 equations, 18 of them used by the glue, and 38 obligations, of
which `cover_2` to `cover_8` are the coverage goals of the heap reads, closed by `sv_cover`; until WP-P4 one
macro per kind of read, `covS`, `covC`, `covX`, `covY`, `covT`, `covR`, named the writer and left the window
arithmetic to `cov_leaf`, 99 lines with the cases), the printed equations to clean Boolean facts (18
`sv_bridge eq_x` lines in `solution`; until WP-P3 `tree_final`, 173 lines, restated every equation and
had one `show` / `rw` / `exact` per field), and 250 lines of plain
Lean for the arithmetic: a row of 3:2 counters preserves the column-weighted sum (`csa_row`), so a 4:2
node preserves the value of its two pairs (`node_sum`), so the sum of the node values over the CUT
`{t, …, 2t}` of the heap is invariant modulo `2^(2N)` while `t` runs from `N-1` (the leaves: `a · b`
exactly) down to 0 (the root): node `t` has exactly the children `2t+1` and `2t+2`, the two elements by
which the cut `{t+1, …, 2t+2}` exceeds `{t+1, …, 2t}` (a pairing node preserves the value exactly, its
children having zero carry rows). One change to the tactic library was needed: the loops run over
`2*N` columns, and the generate-fuel obligation of `sv_structure` was `count ≤ N + 60` (the real fuel,
`PDesign.surfaceFuel`, is `(N+2)² + 64`); it is now `count ≤ 4N + 60`.

### A fourth reference: a Wallace tree as a tape (`mul_wallace`)

`reference/mul_wallace.sv` is a **Wallace tree**: the rows of partial products are reduced by
groups of three, each group replaced by its sum row and its (shifted) carry row, a row of 3:2
counters (a carry-save adder, CSA), until two rows are left, which a ripple-carry adder adds. It is
parametric in `N` and inside the tactics' fragment because the schedule is a TAPE, a queue of rows
in ONE 2-D packed array `T` (`logic [3*N-2:0][2*N-1:0] T`, `3N-1` rows of `2N` bits). Rows
`0 .. N-1` are the partial products (row `j` is `(a & {N{b[j]}}) << j`, written as a GATHER read of
the zero-padded copy `ae` of `a`, as in `mul_tree.sv`) and row `N` is an all-zero DUMMY row, so
`N+1` rows are live at the start (and the formulas below also hold for `N = 1`). CSA number `g`
(`g = 0 .. N-2`) reads the three oldest live rows `3g`, `3g+1`, `3g+2` and APPENDS two rows: the sum
row `x ^ y ^ z` at position `N+1+2g` and the carry row `maj(x, y, z) << 1` (bit 0 is `1'b0`) at
position `N+2+2g`. Each CSA consumes three live rows and appends two, so after the `N-1` CSAs
exactly two rows remain, at positions `3N-3` and `3N-2` (the tape has `N+1+2(N-1) = 3N-1` rows),
and a `2N`-bit ripple-carry adder adds them. Every row is `2N` bits wide and its top carry is
dropped (all sums are modulo `2^(2N)`, the width of the product). The reads are well ordered because
CSA `g` reads position `3g+k`, which for `3g+k ≥ N+1` was written by CSA `⌊(3g+k-N-1)/2⌋ < g`
(as `g ≤ N-2`): the order of `g` is the rank. Constant-zero operands (the triangular shape of the
shifted rows, the dummy row, the zero low bit of a carry row) turn counters into half adders and
wires in synthesis, so no column is pruned by hand. There is no localparam, no division, no
conditional generate and no stage counter: the tape position replaces the stage index, and every
index and bound (`3*g+k`, `N+1+2*g`, `N+2+2*g`, `3*N-3`) is affine in `N` and the genvars. Two
generate nesting levels (the CSA loop over `g`, the column loops inside it), six labelled blocks
(`g_leaf`, `g_lc`, `g_csa`, `g_sum`, `g_car`, `g_fin`).

The proof (`reference/mul_wallace.lean`, 264 code lines since WP-P3/P4, 423 before; standard axioms; PROVING.md, section 9) has
the same five parts as the tree's, with a simpler arithmetic core. By part: `sv_structure` (35 goals
for `CombDesign`, 61 for `Acyclic`, all `intros; sv_rowmajor; omega`, and a 9-line lexicographic
key `(stage, g)`; 18 lines), the ports (`sv_interface`), `sv_equations` (11 equations, all bridged to clean
Boolean facts by 11 `sv_bridge eq_x` lines in `solution`, and 25 obligations: 18 one-liners,
`cover_1` by `sv_cover`, `inputsKnown_1-2`, and four coverage goals, `cover_2` to `cover_5`, the reads of
the tape, closed by `sv_cover`, which solves the adder `g := ((r - N - 1) / 2).toNat` from the row and
leaves the parity to `omega`). Until WP-P3/P4 the glue was `tape_final` (115 lines) and the coverage the
macros `covT` (the position of the row and its parity) and `covK`, 60 lines with the cases. About 200 lines of plain Lean for the arithmetic: a row of 3:2 counters preserves
the column-weighted sum (`csa_row`), so replacing the rows `3g, 3g+1, 3g+2` of the live WINDOW
`[3g, N+1+2g)` of the tape by the two rows appended by CSA `g` preserves the window's sum modulo
`2^(2N)` (`tape_mul`, an induction on `g` from `g = 0`, the partial products and the dummy row, whose
sum is `a · b`, to `g = N-1`, the two last rows). No change to the tactic library was needed (the
`4 · sum + 60` generate-fuel bound is the one introduced for `mul_tree`).

### A fifth reference: a tree with two-row leaves and a localparam (`mul_tree_h`)

`reference/mul_tree_h.sv` is the carry-save tree of `mul_tree.sv` with its leaves taken TWO partial
products at a time: `H = ceil(N/2)` leaves, each already a carry-save pair `(S, C) = (pp[2j], pp[2j+1])`,
in a heap of `2H-1` nodes (root 0, node `k` has the children `2k+1`, `2k+2`, the leaves are the nodes
`H-1 .. 2H-2`), every internal node a 4:2 compressor, a ripple final adder on the root. There is no
pairing node and no constant select (`th` / `nth`): with `H` a node never has to be told apart from its
siblings. `H` is `localparam integer H = (N + 1) / 2;`, **the first reference with a localparam**: the
`sv_comb` tactics read an integer-constant-expression localparam as one more named constant of `N`
(PROVING.md, section 4), so `H` is inlined into every window and bound as `(↑N + 1) / 2`, which `omega`
decides. `b` is zero-extended to `2H+1` bits (`bb`, with `assign bb[2*H:N] = '0`), so the last leaf
of an odd `N` has a zero row. (It must be `integer`: a 2-state `localparam int` with a `/` is wrapped at
2^31 by the elaborated design, and the tactics refuse it.)

The proof (`reference/mul_tree_h.lean`, 307 code lines since WP-P3/P4, 522 before; standard axioms; PROVING.md, section 10) has the
five parts of the tree's: `sv_structure` (39 goals for `CombDesign`, 65 for `Acyclic`, all `intros;
sv_rowmajor; omega`; an 11-line key; 18 lines), the ports (`sv_interface`: the valuation of a design with
localparams, `Summary.val`, is the tactic's business), `sv_equations` (36 obligations: 28
one-liners, `inputsKnown_1-2` and six coverage goals closed by `sv_cover`; its 16 equations are bridged
by 16 `sv_bridge eq_x` lines in `solution`) and 237 lines of plain
Lean for the arithmetic (`heap_mul`: the same cut-sum induction, with no pairing case and two gated
lanes per leaf). The library change behind it is the localparam extension itself
(`LeanModels/Sv/CombView.lean`, `CombViewTactic.lean`, `CombEqTactic.lean`; additive, the three other
references and the examples build unchanged).

### Proof effort (the measured baseline)

| | by hand (`mul_n_byhand.lean`) | tactics (`mul_n.lean`) | tactics, tree (`mul_tree.lean`) | tactics, Wallace tape (`mul_wallace.lean`) | tactics, two-row leaves (`mul_tree_h.lean`) |
|---|---|---|---|---|---|
| code lines (WP-P3/P4: 70, 322, 264, 307; before: 213, 571, 423, 522) | 1385 | 70 | 322 | 264 | 307 |
| elaboration, best of two (wall s / CPU s) | 7.5 / 13.3 | 30.0 / 31.0 | 79.3 / 80.9 | 36.9 / 41.1 | 86.5 / 79.9 |
| `check.py` `solution` stage (s) | 11.3 | 30.2 | 74.4 | 40.9 | 83.6 |
| axioms (the comparator's report) | `propext`, `Classical.choice`, `Quot.sound` | the same | the same | the same | the same |

Code lines and elaboration are measured as in the svGolf `README.md`
("Proof effort"); the tactic proof took about 2.3 times the CPU time (the elaboration and `check.py` rows are the
measurements before WP-P; PROVING.md section 11 has the later ones) and is now a twentieth of the length
(`mul_n`). What the tactic proof leaves to the player, as
`sv_structure?` and `sv_equations?` print it:

* `sv_structure` (`CombDesign`): 24 goals, `inRange_1-9` and
  `driverDisjoint_1-15`, each `intros; sv_rowmajor; omega`. For `Acyclic`: the
  key (`mulKey`, 12 lines) and 51 goals, the same 24 and `rankDecreases_1-27`.
* `sv_equations`: the main goal (the arithmetic: `ideal_mul_view` with one
  `sv_bridge` per field of `MulNetlistView`) and 22
  obligations: `inRange_1-9`, `width_1-2`, `bitRead` and `cover_3`
  (`intros; omega`), `cover_1`, `cover_2` and `cover_4-8` (`sv_cover`; the 2-D ones solve
  the writer's loop indices from the read, until WP-P4 by hand: name the writer, then `cov_leaf`) and
  `inputsKnown_1-2` (`inKnown_ofBitVec`).

Validation (`tests/mul/validate/`): Verilator exhaustive at `N = 1..8` and
100 000 random vectors (plus corners) at `N = 12, 16, 24, 32` (`sim.py --plan
full`, no mismatch); ls-sv's own `run2` on the extracted envelope, exhaustive
at `N = 1..5` and 303 / 43 random vectors at `N = 8 / 16` (`RunAgree.lean`, no
disagreement; the proof covers every `N` anyway). History (before 10/29, when
svGolf still simulated with Icarus 12): Icarus did the exhaustive points and
only 300 random vectors at `N = 12, 16`, because it is impractically slow on
this design at large `N` (every bit write to a packed 2-D array wakes every
reader of the array); Verilator did the large ones. `tests/run.py` runs the
quick plan (`sim.py --plan quick`: exhaustive `N = 1..4`, 100 random vectors
at `N = 8`) every time, the full one with `--full`.

`reference/mul_tree.sv` is validated the same way: `sim.py --plan full` (exhaustive at `N = 1..8`,
100 005 random vectors at `N = 12, 16, 24, 32`) and `sim.py --width N` at every `N = 1..33`
(exhaustive up to 8, 20 005 vectors above), no mismatch; `tests/run.py` runs its quick plan
(`VALIDATION`) every time. The checker's `postsynth` stage compares ls-sv and the scored netlist on
330 vectors at `N = 16` (about 170 s). `reference/mul_wallace.sv` is validated the same way (`sim.py
--plan full` and `--width N` at every `N = 1..33`, no mismatch; its `postsynth` stage takes about
120 s of ls-sv time for the same 330 vectors). `reference/mul_tree_h.sv` too (`sim.py --width N` at every
`N = 1..33`: exhaustive up to 8, 20 005 vectors above, no mismatch; its `postsynth` stage, 330 vectors at
`N = 16`, takes about 40 s).

`tests/mul/results/check.json` is `check.py`'s full output on the reference:
accepted, axioms `propext`, `Quot.sound`, `Classical.choice`, score
1962.576 GE / depth 88 at `N = 16`. The scores at the scoring point and at
the reported points `N = 8, 32` are in `tests/expected.json`, which
`tests/run.py` checks.

## Scores

The ranked numbers at `N = 16` (sky130 A0', `score/tests/ppa/expected_ppa.json`, re-measured by
`tests/run.py`'s `ppa` step):

| design | area (um^2) | delay (ps) | area x time (um2*ns, ranked) |
|---|---|---|---|
| `reference/mul_tree_h.sv` (par) | 8563.2128 | 5992 | **51 310.8** |
| `reference/mul_tree.sv` | 8603.2512 | 6129 | 52 729.3 |
| `reference/mul_wallace.sv` | 8966.0992 | 5982 | 53 635.2 |
| `reference/mul_n.sv` (the array; `mul_n_byhand` the same) | 8290.4512 | 10907 | 90 424.0 |
| `tests/mul/baselines/dadda_rc_16.sv` (Dadda + ripple, simulation only) | 8230.3936 | 5461 | 44 946.2 |
| `tests/mul/baselines/dadda_ks_16.sv` (Dadda + Kogge-Stone, simulation only) | 8937.3216 | 5148 | 46 009.3 |
| `tests/mul/baselines/yosys_mul.sv` (Yosys's own `*`, banned) | 8825.9648 | 6261 | 55 259.4 |

Measure a design with the golfing inner loop, about 2 seconds and no Lean (it runs the source gate and
the pinned flow, not the banlist, the 4-state rules, ls-sv, the post-synthesis check or a proof, so
`check.py --unproved` must still pass before you prove):

```bash
python3.12 score/ppa.py solution.sv --task tasks/mul --no-mapped          # area_um2_sky130, delay_ps_sky130
python3.12 score/ppa.py solution.sv --task tasks/mul --no-mapped --path   # ... and the critical path, net by net
```

**What moves the score** (observations from trial runs, not promises; the pinned flow is the judge):

* The Boolean form of a cell moves both area and delay: the association of a three-input XOR, a `?:`
  majority, which input of a 4:2 compressor enters late.
* ABC restructures what you write: a structural trick that ABC can factor back into the plain form does
  not survive.
* Commuting the operands of one operator moves the A0' area by up to 11% and the delay by up to 32%
  (`score/PPA.md`, the two flows).
* `--path` names the critical path with each net's arrival time: read it before you guess.

The extra columns: pinned flow (`score.py`, the two-stage canonical flow, Yosys 0.53), area in
GE / depth in gates; every number is in `tests/expected.json` (with the gate
mix) and re-measured by `tests/run.py` (the canonical flow left all of them
unchanged):

| design | proved | N = 8 | N = 16 (scored) | N = 32 |
|---|---|---|---|---|
| reference array multiplier (`reference/mul_n.sv`) | yes, ∀ N (tactics and by hand) | 447.976 / 40 | **1962.576 / 88** | 8191.648 / 184 |
| reference carry-save tree (`reference/mul_tree.sv`, a heap of 4:2 compressors + ripple) | yes, ∀ N (tactics) | 451.310 / 30 | **2034.904 / 63** | 8453.626 / 126 |
| reference Wallace tape (`reference/mul_wallace.sv`, `N-1` CSA rows of 3:2 counters + ripple) | yes, ∀ N (tactics) | 482.974 / 30 | **2113.894 / 62** | 8767.595 / 124 |
| reference two-row-leaf tree (`reference/mul_tree_h.sv`, a heap of `⌈N/2⌉` pair leaves, 4:2 compressors + ripple, with a `localparam`) | yes, ∀ N (tactics) | 451.310 / 30 | **2025.905 / 62** | 8452.626 / 127 |
| Yosys's own `assign p = a * b;` (`tests/mul/baselines/yosys_mul.sv`; banlist lifted, NOT a legal entry) | – | 468.637 / 30 | 2081.227 / 59 | 8639.254 / 110 |
| Dadda tree + ripple final adder (`tests/mul/baselines/dadda_rc_*.sv`) | no | 445.978 / 29 | 1953.585 / 61 | 8153.020 / 125 |
| Dadda tree + Kogge-Stone final adder (`tests/mul/baselines/dadda_ks_*.sv`) | no | 484.290 / 24 | 2076.510 / 48 | not scored (the pinned flow exceeds 1800 s) |

The Dadda baselines are generated per width by
`tests/mul/baselines/gen_dadda.py` (flat netlists that keep the task header
but are correct only at the width they were generated for, so they are NOT
entries: the statement covers every `N`). They are simulation-validated
(exhaustive at `N = 4, 8`, 20 000 random vectors at `N = 16, 32`;
`tests/run.py` re-runs `N = 8` exhaustively and 2 000 random vectors at
`N = 16, 32`) and show where the frontier is: at `N = 16` the Dadda + ripple
design beats the reference on both axes, and Dadda + Kogge-Stone beats
Yosys's own multiplier on both. The proved tree (`reference/mul_tree.sv`, 2034.904 / 63 at
`N = 16`) is 4.2 % above Dadda + ripple in area and 2 gates deeper (the ripple final adder sets
the depth in both), 3.7 % above the array reference in area but 25 gates shallower, and 2.2 % below Yosys's
own multiplier in area (4 gates deeper). What it gives up against the Dadda tree is the column-wise
minimum of half adders. The proved Wallace tape (`reference/mul_wallace.sv`, 2113.894 / 62 at `N = 16`) is
8.2 % above Dadda + ripple in area and 1 gate deeper, 7.7 % above the array reference in area but 26
gates shallower, 1.6 % above Yosys's own multiplier (3 gates deeper) and 3.9 % above the carry-save tree
(1 gate shallower): the greedy row-wise grouping spends a half adder at both edges of every row
where a column-wise Dadda schedule spends almost none, and the ripple final adder again sets the
depth. (Three variations of the tape, in the same design space, did not beat it: the dummy row first,
the partial products in reverse order, and the carry row appended before the sum row; they measured
2184.557 / 62, 2121.229 / 64 and 2124.560 / 61 at `N = 16`.) The proved two-row-leaf tree (`reference/mul_tree_h.sv`, 2025.905 / 62 at `N = 16`) is 3.7 % above Dadda +
ripple in area and 1 gate deeper, 0.4 % below the single-row tree and one level shallower (and 2.7 %
below the Wallace tape): the pairing nodes of the single-row tree were already free after synthesis, so
the localparam buys a simpler design and proof more than area. A parametric, proved column-wise Dadda tree
(column heights computed from `N`) is still open: it needs the stage count `⌈log_{3/2}(N/2)⌉`, per-stage column heights
(an inner loop bound that mentions the outer genvar) and a full-adder / half-adder / wire choice per column
(a conditional generate), none of which the tactics read (PROVING.md, section 10).

## Negative designs

`tests/mul/negative/README.md` lists designs that must fail (an off-by-one
carry, a wrong bit, a narrowed output port, a design correct only at the
scoring point, and the banned `*`), with the evidence: kernel-checked
refutations in `tests/mul/negative/Refute.lean` where the instantiation is
cheap, interpreter-checked counterexamples (`#guard` on `run2`) elsewhere,
and the `check.py` stage each is rejected at (`tests/expected.json`, run by
`tests/run.py`).

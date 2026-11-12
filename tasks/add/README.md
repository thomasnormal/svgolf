# Task `add`: N-bit adder with carry in and carry out

The warm-up challenge. An adder is the smallest real svGolf task: the
function is one line, the obvious circuit (a ripple-carry chain) has a
complete for-every-width proof to start from (`reference/add_n.lean`), and
other circuits (carry-lookahead, parallel-prefix) trade area for delay.

**Par** is the proved ripple-carry reference `add_n`: **460.4416 um^2 x 2611 ps =
1202.2 um2*ns**. The one ranked number is area x time, the sky130 A0' cell area
in um^2 times the critical-path delay (decided 2026-11-05; the svGolf README,
"Scoring"); to beat par is to be accepted with a smaller product. The Pareto
frontier of area and time, the GE area and the depth below are extra columns,
for exploring.

## Proving a new design

A new adder is your own `solution.sv` (the header below; `+ - * / % **` are banned at run time) and a
`Solution.lean` that proves it for every `N ≥ 1`. Find the design without Lean, then check it once
without a proof:

```bash
python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped --path   # area, delay and the critical path, about a second
python3.12 check.py tasks/add solution.sv --unproved --tactics --stage-dir stage
```

The second command runs every stage that needs no proof, the task's oracle included (a wrong circuit is
named there, not deep in a proof), says whether the proof tactics read the design (`tactics.in_fragment`)
and leaves it staged in `stage/` for probe files ([PROVING.md, section 0](../../PROVING.md#0-the-loop)).

**The route: the `sv_comb` tactics, then one lemma of arithmetic** ([PROVING.md, section
1](../../PROVING.md#1-the-shape-of-a-proof); `reference/add_n.lean` is a complete proof, 84 code lines):

1. `sv_structure (rank := …)`: one driver per bit and no combinational loop (`CombDesign ∧ Acyclic`). The
   rank is yours: an assign that writes a bit ranks below every assign that reads it.
2. `sv_interface`: the ports, one line.
3. `sv_equations`: each assign as an equation over `Bool` and every driven bit known, under stable names
   (`eq_c_2` is the second assign that writes `c`, in source order).
4. The arithmetic, in plain Lean: those equations give `{cout, s} = a + b + cin`. Prove that the carry into
   each bit is the ripple carry (the structure `CombLib.AddView`: carry in, carry step, sum bits, carry out)
   and `CombLib.add_spec` gives the sum. A carry-select adder (accepted 2026-11-05) did exactly that: by
   induction on the block, its selected carries are the ripple carries.

**Lay the design out so the tactics take it** (what they refuse, with the messages: [PROVING.md, section
4](../../PROVING.md#4-what-the-tactics-accept-and-what-they-refuse)):

* continuous `assign`s of gates (`& | ^ ~`, `?:` and the other operators section 4 lists) in at most two
  nested `generate for` loops, every index and loop bound affine in `N` and the genvars;
* blocks as the rows of 2-D arrays, `c0[j][t]`, not a flat `c0[K*j + t]`: `sv_cover` finds the assign that
  writes a read by solving one unknown per index equation, and a flat read whose writer needs `j = i / K`
  and `t = i % K` is not covered;
* the block counts as integer localparams, `localparam integer Q = N / K;` and `localparam integer R = N % K;`
  (a 2-state `int` with `/` or `%` is refused), and a tail loop over the `R` leftover bits;
* every declared bit driven at `N = 16`: an unused row gets a literal (`assign c0[Q] = 7'b0;`);
* with nested loops, write the rank yourself, as a definition by cases on the site (`rippleRank` gives every
  site of a two-index family rank 0; `sv_structure` unfolds a named definition). The carry-select adder's:

```lean
def cselRank (N : Nat) : SiteId → Nat
  | .plain p => if p = 4 then N + 9 else if p = 5 then 3 * N + 30 else 0  -- module-level assign number p
  | .fam l p [i] =>                                                       -- assign p of loop l, index i
      if l = "g_pg" then 1
      else if l = "g_blk" then (if p ≤ 1 then 1 else 8 + i.toNat)
      else if l = "g_tail" then N + 10 + i.toNat
      else 3 * N + 30
  | .fam l p [j, t] => if l = "g_s" then 3 * N + 30 else if p ≤ 1 then t.toNat + 2 else 9 + j.toNat
  | .fam _ _ _ => 0
```

**What `sv_equations` prints**, the shapes the arithmetic lemma is written against (`sv_equations?` in a
probe file lists them for your design):

* a one-bit literal as `false` or `true`; the `width` goal of a literal row closes by `rfl`, not by
  `intros; omega`;
* a cell of a 2-D array, `c0[j][t]`, as `st.boolAt "c0" (rmN 7 ↑j ↑t)` (`rmN W r c`, the row-major offset).
  `sv_bridge` matches it against a flat `Nat` index in row 0 only; the carry-select proof bridged the other
  rows with `sv_bridge eq_c0_2 with rmN, toNatW, toNatK, Int.toNat_natCast` (its own `theorem toNatW :
  (7 : Int).toNat = 7 := rfl`, and `toNatK` for 6), falling back to its own lemma `rmN_flat`.

**The skeleton** (`reference/add_n.lean` is it, filled in for the ripple adder):

```lean
import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

namespace Submission
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

theorem my_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (rank := myRank N)            -- your rank, a `def` above
  all_goals (intros; omega)

theorem my_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface

-- your arithmetic: the printed equations in, the outputs out (add_n.lean's `add_final`)

theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := my_struct N hN'
  refine CombTask.satisfiedAt_of_comb (my_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  -- name the inputs `hA`, `hB`, `hCi`, as add_n.lean does
  sv_equations
  · -- the main goal: your arithmetic, its hypotheses the `eq_*` (or one `sv_bridge eq_*` each)
  all_goals first
    | (intros; omega)
    | rfl
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

end Submission
```

**Library lemmas that exist today** (the tables: [PROVING.md, section 6](../../PROVING.md#6-tips-the-library)):

* `LeanModels.Sv.CombLib`: `AddView`, `add_value` and `add_spec` (an adder's equations give the sum),
  `ripple_row`, `fullAdder_arith`, the bit-function value `bfVal` and its lemmas, `sum_split`,
  `bitvec_eq_ofNat_of_val`;
* `LeanModels.Sv.Lib.Prefix`, for parallel-prefix adders: the carry operator `pgOp` (associative,
  idempotent), the group generate and propagate `grpG` / `grpP` of a block of bits and how blocks combine,
  and `rippleCarry` (the carry into bit `k`, `rippleCarry_bv` its `BitVec` form);
* the bridges between ports and bits: `SvState.lookup_eq_ofBitVec_bv`, `SvState.boolAt_ofBitVec`,
  `inKnown_ofBitVec`; `sv_bridge`; `LeanModels.Sv.Lib.RowMajor` (`rmN` at natural coordinates).

Planned, not in the library yet: the carry-select adder's ripple-restart lemmas (a carry chain started at
any bit from any carry; restarting at the true carry changes nothing) and a flat form of `rmN`.

## The circuit

Write a module with exactly this header (port names, directions, widths and
order matter; the module must be called `add_n` and its only parameter `N`):

```systemverilog
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
```

It must compute, combinationally, `{cout, s} = a + b + cin`: `s` is the low
`N` bits of the sum and `cout` the carry out of the top bit.

## The statement (`Spec.lean`, trusted)

```lean
def task : CombTask where
  inRange N := 1 ≤ N
  inputs N := [("a", N), ("b", N), ("cin", 1)]
  outputs N := [("s", N), ("cout", 1)]
  fn N := fun (a, b, cin, ()) =>
    let t := a.toNat + b.toNat + cin.toNat
    (BitVec.ofNat N t, BitVec.ofNat 1 (t / 2 ^ N), ())

abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement
```

For every `N` with `1 ≤ N < 2^31`: the design's input ports are exactly `a`, `b` (`N` bits)
and `cin` (1 bit), its output ports exactly `s` (`N` bits) and `cout`
(1 bit), in that order; no process is clocked (no `always_ff`, no
`always @(posedge …)`); there is no combinational loop; every run terminates under every schedule and
stimulus; and every cycle whose stimulus drives `a`, `b`, `cin` with known
values ends with `s = (a + b + cin) mod 2^N` and `cout = (a + b + cin) / 2^N`,
the sum taken in the natural numbers. `Spec.lean` also proves `fn_arith`
(`cout · 2^N + s = a + b + cin`, so `{cout, s}` really is the `N+1`-bit
sum). `SvGolf/Task.lean` defines `CombTask` and explains why the statement
cannot be met vacuously (no settling, `x` values, extra or renamed ports,
history, a clock that never ticks, ...).

The range ends below `2^31` (decided 2026-11-06): the port widths are `int` expressions of `N`
(`[N-1:0]`), and an `int` holds no value of `2^31` or more. Every task's range keeps every width it
implies below `2^31`.

The "no clocked process" requirement closes a gap between ls-sv and every
other tool: ls-sv runs each `always_ff` once per cycle whatever its clock
signal holds, so a correct adder whose outputs are registered on a clock
nothing drives (or one tied to `1'b0`) holds the right sum in every ls-sv
snapshot, while an event-driven simulator sees a clock that never rises (Icarus
12, measured 2026-10-28: the outputs stay at `x`; Verilator is 2-state and keeps its
initial 0), and Yosys removes the flip-flops and scores the design at 0 GE.
`tests/add/negative/dead_clock.sv` and `tests/add/negative/dead_clock_tied.sv`
are those designs; `tests/add/negative/Refute.lean` refutes both through this requirement
(`not_satisfiedAt_of_clocked`: a family with a top-level clocked process
meets no combinational task at any `N`). The requirement can go once
ls-sv's sequential layer models clock edges.

## Rules for this task

* **Banned run-time operators: `+ - * / % **`.** Addition is the task, and
  Yosys's `alumacc` turns `+` and `-` chains into the same `$alu`/`$macc`
  cells as `*`, so all six are banned on run-time operands, together with
  compound assignments (`+=`), `++`/`--` on signals, unary minus, and the
  system functions Yosys builds from adders (`$countones`, ...). Build the
  adder from `& | ^ ~`, `?:`, selects and concatenations. The checker
  enforces the banlist twice (`score/banlist.py`: a pyslang front check on
  the source and a Yosys backstop that rejects
  `$add $sub $neg $mul $alu $macc $lcu $fa ...` cells).
* **Run-time ordering comparisons are banned too** (`< <= > >=` with a
  run-time operand; decided 2026-11-05). `a > ~b` IS the carry out of
  `a + b`, and Yosys's `alumacc` builds a run-time ordering comparison
  through an `$alu` (measured: `$gt` becomes `$alu`, on 1-bit operands too),
  i.e. Yosys's own carry logic. So the ban is at the Yosys level: after
  `proc; opt` the backstop also runs `alumacc` and rejects every `$alu` (or
  `$macc`, `$lcu`, `$fa`) cell it builds, naming the comparison's source
  line. Still allowed: equality (`== != === !==`: `alumacc` builds no
  `$alu` for it), comparisons over parameters and genvars (folded as
  constants: `i < N`, `N > 8`), and a comparator you build from `& | ^ ~`
  (and prove). `tests/add/baselines/cmp_carry.sv`, an adder whose every
  carry is such a comparison,
  `c[i] = (a[i-1:0] > ~b[i-1:0]) | ((a[i-1:0] == ~b[i-1:0]) & cin)`, is the
  design the rule is for: with Yosys's adder in every carry it scores
  195.975 GE, depth 17 at `N = 16`, lower depth than every proved design;
  it is a baseline scored with the banlist lifted, like Yosys's own `+`.
* **Constant arithmetic is fine**: parameter expressions (`N-1`,
  `$clog2(N+1)`), index arithmetic over genvars and parameters (`c[i+1]`,
  `g[l][((i >> l) << l) - 1]`, `i - (1 << l)`), generate conditions. Current
  ls-sv limits to know about: genvar steps are `i++` or `i = i + 1`
  (and the `--`/`- 1` forms; a stride or a parameter amount is refused), and keep run-time selects on `[N-1:0]`-style
  vectors (an ascending or offset range makes Yosys build a `$sub` for the
  index, which the backstop rejects). A third: procedural `for` loops bounded
  by `N` are refused by ls-sv's extractor for now. An `always_comb` ripple
  written as `for (int k = 0; k < N; k++) c[k+1] = ...` extracts as
  `Unsupported ForLoopStatement`, which ls-sv refuses loudly when it runs, so
  no proof of it exists; write carry chains with `generate for`. (A
  procedural counter that its loop body writes counts as a run-time value
  for the banlist.)
* **The proof is for every `N ≥ 1`**: the statement quantifies over `N`, so a
  proof at `N = 16` alone does not type-check against it. No unrolling at a
  fixed width; induction on the bit index is the intended route.
* Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `bv_decide` (it runs an
  external SAT solver, which the checker does not support: the repository's `README.md`,
  "`bv_decide`"), no `native_decide`, no `sorry`.
* Proof time limit: 300 CPU s (`task.json`), the one limit of every task (svGolf `README.md`,
  "Proof effort"). Measured 2026-11-06 in CPU seconds, three cold runs each
  (`check.py`'s `solution` stage, `score/time_limits.json`): `add_n` 5.7, 6.2 and 6.0,
  `add_proc` 8.2, 8.2 and 8.4, `add_proc_m` 12.3, 12.4 and 11.2, `add_mux`
  6.8, 7.0 and 6.5, the by-hand reference 4.2, 4.7 and 4.1 CPU s (in wall-clock
  seconds, 2026-10-30: the tactic reference 12.1, 9.6 and 9.5 s, the by-hand reference 3.0 s). It was 300 s
  of wall clock, then 120 s.
* Scored at `N = 16`, no depth budget. The ranked score is sky130 A0'
  (decided 2026-11-03; svGolf `README.md`, "Scoring"): the cell area in um^2 and
  the critical-path delay in ps of the scored netlist, weighed by
  `score/ppa.py` (`sky130_a0_v3`); the leaderboard ranks their product, area x
  time (decided 2026-11-05), and their Pareto frontier is an exploration view. Area
  in NAND2 gate equivalents and depth in gates, from the same pinned two-stage
  Yosys + ABC flow (`score/canon.ys`, `score/svgolf.ys`, `score/ge.json`), are
  extra columns. The score is deterministic, the same file always scoring the
  same: names, comments, blank lines, whitespace and the file name never change
  it, while operand order, how a chain of gates is grouped, gate forms and the
  order of statements do, and trying them is golf (svGolf `README.md`,
  "Scoring"; a carry-select adder scored 474.2 um^2 / 2479 ps with its sum
  assigns in loops of their own and 481.7 / 2609 with the same assigns inside
  the block loop, measured 2026-11-05). Every number can be reproduced bit for
  bit: score/PPA.md, "Reproduce a score". The tables below also report
  `N = 32` and `N = 64`, which are not scored.
* Post-synthesis check (`task.json` `postsynth`): ls-sv's reading and the
  scored netlist must agree on the fixed corners, the harvested comparison
  constants and 4000 seeded random vectors at `N = 16` (4132 vectors:
  1.3 s measured for the ripple reference, 15 s for the prefix adders, whose
  `run2` is slower).
* No x or z value may arise (README.md, "Rules"): no x/z literal digit
  outside a casez/casex item wildcard (the source gate), and no parameter
  with unknown bits, out-of-range select or undriven net at `N = 16` (the
  `fourstate` stage). `tests/add/attacks/z_case_item.sv` is why: a ripple
  sum behind `case (cin) 1'bz:` computes the sum in ls-sv on every vector
  (ls-sv never matches a `z` item, and neither did Icarus, measured 2026-10-28),
  so it looks provable, while
  Yosys reads the item as a don't-care and scores it at 0 GE. The
  post-synthesis check alone rejects it on every vector, but
  `tests/add/attacks/zpair_add_rare.sv` (complementary `z` items whose arms
  differ from the sum on one input pair in 2^32) passes that check: the
  source gate refuses both exactly.
* **Input drive** (the sky130 score, `sky130_a0_v3`): every primary input is driven by `sky130_fd_sc_hd__buf_8`,
  the default (`task.json` names no `input_drive`), standing for the on-chip bus or register that feeds the block; the
  record says so in `ppa.setup.input_drive` (score/PPA.md, "The input drive").

## What counts as a solution

Two files: the design `solution.sv` (module `add_n` as above) and a Lean file
`Solution.lean` that imports `Submission.Design` and proves

```lean
theorem Submission.solution : Submission.Goal
```

(inside `namespace Submission`, as `reference/add_n.lean` writes it: `theorem
solution : Goal`), where the checker defines `Submission.Goal` as
`SvGolf.Tasks.Add.Statement Submission.design.sem` for the design it extracts
from YOUR `.sv` (it never reads a player's envelope). The file names and paths
are free; the module name, the import and the theorem are fixed. A solution
counts when

```bash
python3.12 check.py tasks/add solution.sv Solution.lean
```

prints `"accepted": true`. Its ranked number is `ppa.area_um2_sky130` x
`ppa.delay_ps_sky130` (the last line on stderr says it, with par); the `score`
field holds the extra GE columns. The checker's
stages (source gate, extraction with the multi-point cross-check, banlist,
design load, timed proof build, comparator, `leanchecker`, scoring) are
described in the svGolf `README.md`. Run it with `--keep` once to get a staged
`Submission.Design` to develop the proof against (`dev_hint`).

The ripple-carry reference has two proofs of the same statement, for every
`N ≥ 1` (`reference/add_n_byhand.sv` is a byte-identical copy of
`reference/add_n.sv` that goes with the by-hand proof; `tests/run.py` checks the
bytes):

* `reference/add_n.lean` (84 code lines) uses the `sv_comb` tactics of
  Proglib (formerly lean-surfaces): `sv_structure` proves the comb profile and the acyclicity
  certificate (one theorem, `CombDesign ∧ Acyclic`, plus the rank), `sv_interface`
  proves the ports, `sv_equations` derives the
  netlist's four equations and the knownness of every driven bit from the real
  semantics, and the plain-Lean library `LeanModels.Sv.CombLib` (`AddView`,
  `ripple_row`) does the carry chain. The task statement also pins the ports
  (names, order, widths): `add_interface` is one line, `sv_interface`.
  [PROVING.md](../../PROVING.md) walks through the file.
* `reference/add_n_byhand.lean` (509 code lines) is the same statement proved with
  no tactic: it walks the generate loop symbolically, discharges the one-driver
  rule, the comb profile and an acyclicity certificate, and proves the settled
  state by induction on the bit index (the carry into bit `k` is core's
  `BitVec.carry k`). It is the baseline the tactics are measured against, and
  the route for a design they refuse (a prefix adder with a `$clog2` `localparam`, a
  design with `always_comb`). A new design needs new versions of the
  instantiation and settled-state steps; the reduction
  (`CombTask.satisfiedAt_of_comb`) and the `Nat` bridges at the end carry over.

## Proof effort (the measured baseline)

| | by hand (`add_n_byhand.lean`) | tactics (`add_n.lean`) |
|---|---|---|
| code lines | 509 | 84 |
| elaboration, best of two (wall s / CPU s) | 2.8 / 3.7 | 8.9 / 8.3 |
| `check.py` `solution` stage (s) | 2.8 | 14.2 |
| axioms (the comparator's report) | `propext`, `Classical.choice`, `Quot.sound` | the same |

Code lines are what is left after removing comments (line, block, doc) and
blank lines, `import` and `namespace` lines included (the leaderboard's
count). Elaboration is one `lake env lean` of the file against the staged
`Submission.Design`, `LEAN_NUM_THREADS=2`, `nice`, best of two single runs on a
16 GB laptop; the tactic proof takes about 2.3 times the CPU time of the
by-hand one (the tactics normalize large goals with `simp`), and is a fifth of
the length. What the tactic proof leaves to the player, as `sv_structure?` and
`sv_equations?` print it:

* `sv_structure` (`CombDesign`): 5 goals, `inRange_1-2` and `driverDisjoint_1-3`,
  each `intros; omega`. For `Acyclic` the rank (one line:
  `rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1)`)
  and 7 goals, the same five and `rankDecreases_1-2`, each `intros; omega`;
  the reference proves both in ONE theorem (`CombDesign ∧ Acyclic`), which
  returns those 7 goals.
* `sv_equations`: the main goal, with `eq_c_1`, `eq_cout_1`, `eq_s_1`,
  `eq_c_2` (stable aliases: target signal and ordinal; the generated names
  `eq_c_plain_0`, `eq_cout_plain_1`, `eq_s_g_bit_0`, `eq_c_g_bit_1` are copies)
  and the four `known_*` in the context (the
  arithmetic: `add_final`, about 45 lines), and 10 obligations: `inRange_1-2`
  and `bitRead_1-2` (`intros; omega`), `cover_1-3` (`sv_cover`) and
  `inputsKnown_1-3` (`inKnown_ofBitVec`).
* by hand: the 1-bit conversion of `cin` and the arithmetic (the ports are
  `sv_interface`, one line).

## Scores (the goalposts)

The ranked numbers at `N = 16` (sky130 A0', `score/tests/ppa/expected_ppa.json`, re-measured by
`tests/run.py`'s `ppa` step):

| design | area (um^2) | delay (ps) | area x time (um2*ns, ranked) |
|---|---|---|---|
| `reference/add_n.sv` (par; `add_proc`, `add_proc_m`, `add_mux` and `add_n_byhand` score the same) | 460.4416 | 2611 | **1202.2** |
| `tests/add/baselines/add_n_sklansky.sv` (simulation only) | 541.7696 | 2451 | 1327.9 |
| `tests/add/baselines/add_n_kogge_stone.sv` (simulation only) | 641.8656 | 2064 | 1324.8 |
| `tests/add/negative/plus.sv` (Yosys's own `+`, banned) | 497.9776 | 3143 | 1565.1 |
| `tests/add/baselines/cmp_carry.sv` (Yosys's `$alu` through run-time comparisons: banned since 2026-11-05, banlist lifted) | 857.072 | 1965 | 1684.1 |

The extra columns: pinned flow (the two-stage canonical flow of `score/score.py`), Yosys 0.53.
Area in GE, depth in gates. Every number here is in `tests/expected.json`
(with the gate mix) and re-measured by `tests/run.py`. The canonical flow
(2026-10-28) left every number here unchanged except `cmp_carry`'s
(181.977 / 393.287 / 838.22 GE and depth 17 / 25 / 32 under the old
one-process flow, whose results depended on the source's layout).

| design | N = 16 | N = 32 | N = 64 | correctness |
|---|---|---|---|---|
| `reference/add_n.sv`: ripple carry (gates in a generate loop) | **112.0 GE, depth 33** | 224.0, 65 | 448.0, 129 | proved for every `N ≥ 1` (`reference/add_n.lean` with the tactics, `reference/add_n_byhand.lean` by hand), both accepted by `check.py` |
| `reference/add_proc.sv`: the same ripple adder with the carry cell as an `always_comb` `if`/`else` | **112.0 GE, depth 33** | 224.0, 65 | 448.0, 129 | proved for every `N ≥ 1` (`reference/add_proc.lean`, PROVING.md section 12: the lowered shape of the tactics), accepted by `check.py` |
| `reference/add_proc_m.sv`: the same ripple adder with the carry cell AND the sum bit in ONE `always_comb` body that writes two windows | **112.0 GE, depth 33** | 224.0, 65 | 448.0, 129 | proved for every `N ≥ 1` (`reference/add_proc_m.lean`: `add_proc.lean`'s proof, character for character, because the stable aliases count the windows that write a signal), accepted by `check.py` |
| `reference/add_mux.sv`: the same ripple adder written with `~` and the conditional expression `?:` | **112.0 GE, depth 33** | 224.0, 65 | 448.0, 129 | proved for every `N ≥ 1` (`reference/add_mux.lean`, PROVING.md section 14: the second fragment), accepted by `check.py`; the same score as `add_n.sv` (the canonical flow maps the `?:` carry to the same netlist) |
| `tests/add/baselines/add_n_sklansky.sv`: Sklansky prefix | **127.658 GE, depth 28** | 296.639, 43 | 601.274, 80 | simulation only (`tests/add/validate/`) |
| `tests/add/baselines/add_n_kogge_stone.sv`: Kogge-Stone prefix | **149.652 GE, depth 24** | 325.296, 47 | 788.892, 66 | simulation only (`tests/add/validate/`) |
| `tests/add/negative/plus.sv`: Yosys's own `assign {cout, s} = a + b + cin;` (banned; banlist lifted to score it) | 117.994 GE, depth 33 | 251.982, 57 | 494.973, 121 | simulation only; the baseline to beat |
| `tests/add/baselines/cmp_carry.sv`: every carry a run-time comparison, i.e. Yosys's `$alu` (banned since 2026-11-05; banlist lifted to score it) | 195.975 GE, depth 17 | 391.952, 25 | 855.218, 30 | simulation only (Verilator, `run2`) |

At `N = 16` the frontier is ripple (112.0, 33), Sklansky (127.658, 28),
Kogge-Stone (149.652, 24); Yosys's own adder (117.994, 33) is dominated by
the ripple (`score.py --pareto` agrees). The frontier moves with `N`: at
`N = 32` Kogge-Stone (325.296, 47) is dominated by Sklansky (296.639, 43)
and Yosys's own adder (251.982, 57) is on it; at `N = 64` all four are.
`cmp_carry` (depth 17 / 25 / 30 at `N = 16 / 32 / 64`) is not a legal
design: its carries are Yosys's adder, built through comparisons (see
"Rules for this task").

The Pareto frontier of the sky130 A0' area and time at `N = 16` (an exploration view) is the same:
ripple 460.4416 um^2 at 2611 ps, Sklansky 541.7696 at 2451, Kogge-Stone 641.8656 at 2064. Of the two
banned baselines, Yosys's own adder (497.9776, 3143) is dominated by the ripple, and `cmp_carry`
(857.072, 1965), Yosys's adder behind comparisons, cannot be a record. On the ranked product, area x
time, neither prefix adder is ahead of the ripple.

The ripple is exactly 7 GE per bit (3 NAND + 2 XOR) and depth `2N + 1` at
every width measured (`N = 2, 4, 8, 16, 32, 64`). Gate mixes at `N = 16`:
ripple 48 NAND + 32 XOR; the prefix designs are mapped by ABC into
AND/NAND/OR/XOR mixes (`tests/expected.json`).

Things worth knowing when golfing: ABC restructures the netlist and maps
with its OWN gate costs, not the GE table (a `p ? c : a` multiplexer carry,
1 MUX = 2.333 GE per bit by the table, comes out as 3 NAND = 3 GE, exactly
the reference's 48 NAND + 32 XOR), and the pinned `abc -g` script does not
optimize for depth, so a prefix structure's textbook depth is not what `ltp`
reports. The score is
what the pinned flow measures; measure it with the golfing inner loop,

```bash
python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped          # area_um2_sky130, delay_ps_sky130
python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped --path   # ... and the critical path, net by net
```

(about 2 seconds, no Lean: it runs the source gate and the pinned flow, not the banlist, the 4-state
rules, ls-sv, the post-synthesis check or a proof, so `check.py --unproved` must still pass before you
prove; `score/score.py` gives the GE columns alone).

**What moves the score** (observations from trial runs, not promises; the pinned flow is the judge):

* ABC restructures what you write: a two-bit lookahead carry came back as the same ripple of NAND gates,
  and scored worse.
* Statement order and gate forms move both area and delay: the carry assign before the sum assign in
  the loop, and bit 0's carry written as a majority at module level with the loop from `i = 1`, each
  moved area x time by a few percent. Blank lines and signal or block names changed nothing.
* Commuting the operands of one operator moves the A0' area by up to 11% and the delay by up to 32%
  (`score/PPA.md`, the two flows).
* `--path` names the critical path with each net's arrival time: read it before you guess.

## Next goalposts

* **Beat par**: be accepted with area x time under 1202.2 um2*ns (`add_n`,
  460.4416 um^2 x 2611 ps at `N = 16`). Exploring, any move of the Pareto
  frontier of area and time counts as news too (above: the prefix adders).
  The comparison-built `tests/add/baselines/cmp_carry.sv` (1965 ps) does not
  count: its carries are Yosys's `$alu`, banned since 2026-11-05.
* **Prove a prefix adder.** The Sklansky and Kogge-Stone baselines
  (`tests/add/baselines/`) pass the
  source gate, the extraction with its multi-point cross-check, the banlist
  and ls-sv's loader (measured: `check.py` with a placeholder proof rejects
  them only at the `comparator` stage), and match `a + b + cin` in Verilator
  and `run2`; what they lack is the for-all-`N` proof. The route
  that should work: instantiate the nested generate loops (the level loop
  over `l < $clog2(N+1)`, the node loop, and the generate-if on bit `l` of
  the node, `GenItem.expand2_genIf_of_ne`/`_of_eq`); then prove by induction
  on the level `l` that `g[l][k]`, `p[l][k]` hold the group generate and
  propagate of a block of positions ending at `k` (the prefix operator
  `(g, p) ∘ (g', p') = (g | p & g', p & p')` is associative), and at the
  last level that the block is `[0, k]`, so `g[L][k]` is core's
  `BitVec.carry k a b cin`; from there the reference's step 4 carries over.
  The `sv_comb` tactics do not take these baselines as written
  (`sv_structure: outside the supported fragment — localparam `L`: `$clog2` is
  outside the v1 fragment ...`, and a conditional generate inside a generate loop
  is outside it too; [PROVING.md](../../PROVING.md), section 4), so the route
  above is the by-hand one of `reference/add_n_byhand.lean`, with `CombLib`'s
  bit functions for the arithmetic. (Even without the `$clog2` localparam, a prefix
  adder's index arithmetic, `((i >> l) << l) - 1` or `i - (1 << l)`, is not
  affine in the genvars, which the tactics' recognizer requires.)
  The Sklansky MATHEMATICS is proved for every `N`, waiting for the glue:
  `tests/add/baselines/add_n_sklansky_core.lean` (section `SklCore`, on the
  library's `LeanModels/Sv/Lib/Prefix.lean`) defines the recurrence as the
  source denotes it, proves the block invariant (after level `l`, position `i`
  holds the group generate and propagate of the aligned block from
  `(i >> l) << l` to `i`) and, from the netlist's equations stated per level
  and position with the generate-if's guard as a hypothesis, the `CombLib.AddView`
  that `CombLib.add_spec` turns into the task's `s` and `cout`. The source is
  not rewritten around the tactics: the `int`-typed `localparam L = $clog2(N + 1)`,
  the guarded generate family and the nonlinear partner index are for ls-sv to
  accept (decided 2026-11-05: the tactics are made more robust, designs are not
  rewritten around them).

## Validation

`tests/add/validate/validate.py` simulates every design of the task (the
reference, the baselines, the `+` baseline and the functional negatives) in
Verilator and runs ls-sv's `run2` on the same vectors (one cycle each,
both schedules `σ_src` and `σ_rev`), against `{cout, s} = a + b + cin`
computed in Python: every input combination for `N = 1..5`, and a fixed-seed
random sample plus corner cases for `N = 6, 7, 8, 13, 16, 31, 32, 33, 64`.
The reference and the baselines must match everywhere; the functional
negatives must be caught (wrong somewhere) with Verilator and `run2` agreeing
on every vector. `tests/add/validate/verilator.py` runs the three adders in
Verilator on big vector counts (exhaustively up to `N = 12`), and
`tests/add/validate/postsynth.py` simulates the netlists the pinned scoring
flow produces, so the scored circuit is checked too: no ls-sv/Yosys
disagreement was found. See `tests/add/validate/README.md` and the logs in
`tests/add/results/` for the last full runs; `tests/run.py` runs a quick plan
of `validate.py` and `postsynth.py` every time.

## Negative designs

`tests/add/negative/README.md` lists designs that must fail (wrong carry in,
an off-by-one carry out, a wrong carry gate, a design correct only at the
scoring point, two interface tricks, two registers on a dead clock, and the
banned `+`), with kernel-checked refutations in
`tests/add/negative/Refute.lean` and the checker stage each one is rejected
at (`tests/expected.json`, run by `tests/run.py`). The simulation-only
designs and the `+` baseline are `baselines` entries of `tests/expected.json`:
`tests/run.py` re-scores them and compares.

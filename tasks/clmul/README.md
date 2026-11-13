# Task `clmul`: N-bit carry-less multiplier

`mul` with the carries removed: AND for the partial products, XOR for the sums, no adder. The product of two
polynomials over GF(2), `PCLMULQDQ`, the core of GHASH and of every binary-field, CRC and BCH construction.
Build an `N × N → 2N-1` carry-less multiplier out of XOR/AND networks, prove it correct for EVERY width
`N ≥ 1`, and make it small (and shallow) at `N = 16`. It is the first task whose best known designs are
RECURSIVE (Karatsuba is 20 % smaller than the schoolbook array at `N = 16` and 36 % at `N = 32`, measured
below), so it is also the task that shows what the proof tactics need next. The reference array is **proved for
every `N`** with the `sv_comb` tactics (`reference/clmul_n.lean`, 238 code lines, `solution` stage about 8 s).

## Proving a new design

A new carry-less multiplier is your own `solution.sv` (the header below; `+ - * / % **` are banned at run time)
and a `Solution.lean` that proves it for every `N ≥ 1`. Find the design without Lean, then check it once
without a proof:

```bash
python3.12 score/ppa.py solution.sv --task tasks/clmul --no-mapped --path   # area, delay and the critical path, about a second
python3.12 check.py tasks/clmul solution.sv --unproved --tactics --stage-dir stage
```

The second command runs every stage that needs no proof, the task's oracle included (a wrong circuit is
named there, not deep in a proof), says whether the proof tactics read the design (`tactics.in_fragment`)
and leaves it staged in `stage/` for probe files ([PROVING.md, section 0](../../PROVING.md#0-the-loop)).

**The route: the `sv_comb` tactics, then the XOR arithmetic of your rows** ([PROVING.md, section
1](../../PROVING.md#1-the-shape-of-a-proof); `reference/clmul_n.lean` is a complete proof, 238 code lines):

1. `sv_structure (lexRank := key N)`: one driver per bit and no combinational loop (`CombDesign ∧ Acyclic`),
   ordered by your key, a lexicographic triple per site (`clmulKey`: the row first, the output bits last).
2. `sv_interface`: the ports, one line.
3. `sv_equations`: each assign as an equation over `Bool` and every driven bit known; the 2-D signal `r` is
   read as `st.cell "r" N i j`, and each field of your arithmetic lemma is one `sv_bridge eq_…` line.
4. The arithmetic, in plain Lean: the equations give the Spec's product. The reference's is a structure of
   five fields (`View`), a row invariant by induction on the row (`view_row`: row `i`, column `j` is the XOR
   over `t ≤ i` of `a t & b (i + j - t)`) and the collapse of the Spec's double sum (`view_spec`).

**Lay the design out so the tactics take it** (what they refuse, with the messages: [PROVING.md, section
4](../../PROVING.md#4-what-the-tactics-accept-and-what-they-refuse); the styles of real code and where each
stops: "How people write clmul" below):

* continuous `assign`s of `&` and `^` in at most two nested `generate for` loops that start at an integer
  literal, every index and loop bound affine in `N` and the genvars;
* partial sums as the rows of a 2-D array, `r[i][j]`; `sv_cover` finds the assign that writes a read by
  solving one unknown per index equation, so a read whose writer needs a quotient and a remainder of the
  index is not covered;
* every declared bit driven at `N = 16`;
* no module instances: the tactics cannot summarize them yet, so a Karatsuba multiplier (the smaller design)
  is written flat, as one module; no procedural `for` loop (`fourstate` refuses it).

**The skeleton** (`reference/clmul_n.lean` is it, filled in for the array):

```lean
import Submission.Design
import tasks.clmul.Spec
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

namespace Submission
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
open SvGolf.Tasks.Clmul

set_option maxHeartbeats 400000 in
theorem my_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (lexRank := myKey N)           -- your key, a `def` above (clmul_n.lean's `clmulKey`)
  all_goals (intros; sv_rowmajor; omega)

theorem my_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Clmul.task.Interface N (design.sem N) := by
  sv_interface

-- your arithmetic: the rows' equations in, the product's coefficients out (clmul_n.lean's `ClmulArith`)

set_option maxHeartbeats 400000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := my_struct N hN'
  refine CombTask.satisfiedAt_of_comb (my_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Clmul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · -- the main goal: your arithmetic lemma, one `sv_bridge eq_…` per field (clmul_n.lean)
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | sv_cover

end Submission
```

**Library lemmas that exist today** (the tables: [PROVING.md, section 6](../../PROVING.md#6-tips-the-library)):

* the XOR arithmetic is in the reference (a task ships no library: copy it): `bx` (the XOR of `f 0, …,
  f (n-1)`) with `bx_congr`, `bx_trunc`, `bx_pair`, `foldl_xor`; `coeff_eq` (the Spec's double sum as a
  nested `bx`), `getLsbD_ofBits`, `view_row`, `view_spec`;
* `LeanModels.Sv.CombLib`: the bit-function value `bfVal` and its lemmas, `rowMajor_inj`, `lexLt`;
* `SvState.cell`, `sv_bridge` and `sv_rowmajor`; `rmN` and `Key` (`LeanModels/Sv/CombViewArith.lean`) and
  `LeanModels.Sv.Lib.RowMajor`; the port bridges `SvState.lookup_eq_ofBitVec_bv`, `SvState.boolAt_ofBitVec`,
  `inKnown_ofBitVec`.

## The circuit

Write a module with exactly this header (port names, directions, widths and order matter; the parameter must
be called `N`):

```systemverilog
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
```

It must compute, combinationally, the product of the two polynomials over GF(2) that `a` and `b` encode (bit
`i` is the coefficient of `x^i`): for `0 ≤ k ≤ 2N-2`

    p[k] = XOR over all i, j in [0, N) with i + j = k of (a[i] AND b[j]).

The product of two polynomials of degree below `N` has degree at most `2N-2`, so `p` has `2N-1` bits (ONE bit
at `N = 1`: the AND of the inputs) and loses nothing. It is the UNREDUCED product: no modulus. Examples: `(x+1)^2
= x^2+1` (`N = 2`: `2'b11 (x) 2'b11 = 3'b101`); `(1+x+...+x^15)^2 = 1+x^2+...+x^30` (`N = 16`: `0xffff (x)
0xffff = 0x55555555`); FIPS 197 Section 4.2's `0x57 (x) 0x83 = 0x2b79`, which reduces modulo `0x11b` to
the standard's `{c1}`, and `0x57 (x) 0x13 = 0x0589`, which reduces to `{fe}`.

## The statement (`Spec.lean`, trusted)

```lean
def coeff (N : Nat) (a b : BitVec N) (k : Nat) : Bool :=
  (List.range N).foldl (fun acc i =>
    (List.range N).foldl (fun acc j => acc ^^ (decide (i + j = k) && a.getLsbD i && b.getLsbD j)) acc) false

def task : CombTask where
  inRange N := 1 ≤ N ∧ N < 2 ^ 30
  inputs N := [("a", N), ("b", N)]
  outputs N := [("p", 2 * N - 1)]
  fn N := fun (a, b, ()) => (ofBits (2 * N - 1) (coeff N a b), ())

abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement
```

(`ofBits n f` is the `n`-bit vector whose bit `k` is `f k`.) For every `N` with `1 ≤ N < 2^30`: the design's ports are exactly
`a`, `b` (inputs, `N` bits) and `p` (output, `2N-1` bits); no process is clocked (`Unclocked`) and there is no combinational loop; every run
terminates under every schedule and stimulus; and every cycle whose stimulus drives `a` and `b` with known
values ends with `p` holding `coeff`, the XOR of `a_i AND b_j` over `i + j = k`, at every bit `k`.
`SvGolf/Task.lean` defines `CombTask` and explains why the statement cannot be met vacuously; `REVIEW.md` is
the statement's review (what it says, where it is checked, the cheating surfaces and the questions for the
project owner).

The range ends below `2^30`, not `2^31` (decided 2026-11-06): the port widths are `int` expressions of
`N` (`[2*N-2:0]`), and an `int` holds no value of `2^31` or more, so at `N ≥ 2^30` the elaborated
`2*N` wraps and the output port is not `2N-1` bits wide. Every task's range keeps every width it implies
below `2^31`.

## Rules for this task

* **Banned run-time operators: `+ - * / % **`**, including compound assignments (`+=`), `++`/`--` on signals,
  unary minus and the system functions Yosys builds from adders. The task is to build the product from XOR and
  AND: `*` would build the integer product (or, by Kronecker substitution on bit-spread operands, this one),
  and a one-bit `+` is an XOR with the carry dropped. `/ % **` are banned as in EVERY task (since 2026-11-06;
  the svGolf README, "Rules"): not because they would build this function (`REVIEW.md` has the reasoning: none
  does) but because a zero divisor makes an x from known inputs, which ls-sv carries into a decision and Yosys
  builds as a defined value (`tests/clmul/attacks/div_zero_x.sv`: correct in ls-sv at every input, its scored
  netlist wrong on one input pair in 2^32, which the post-synthesis vectors miss; before the ban it passed every
  stage). The check is `score/banlist.py` (a pyslang front check and a Yosys backstop at `N = 1, 2, 3, 16`). Constant arithmetic is fine: parameter expressions (`2*N-2`), localparams,
  genvar index arithmetic (`r[i-1][j+1]`).
* **Run-time ordering comparisons (`< <= > >=`) are banned too**, as in every task that bans `+` or `-` (decided
  2026-11-05): Yosys's `alumacc` builds each one as an `$alu`, its own adder, so after `proc; opt` the backstop
  also runs `alumacc` and rejects every `$alu`/`$macc` cell it builds, at the comparison's source line. Equality
  (`== != === !==`), comparisons over parameters and genvars (folded as constants) and a comparator built from
  `& | ^ ~` stay allowed.
* **Genvar loops step by one** (`i++`, `i = i + 1`); a stride or a parameter amount is refused at the `design`
  stage (an ls-sv limit, not a rule). Loops with zero iterations (the upper half of the reference at `N = 1`)
  are fine.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`allow_bv_decide: false`: external solvers are not
  supported, 2026-11-01). No `native_decide`, no `sorry`.
* **Proof time limit: 300 CPU s** (`task.json`), the one limit of every task (svGolf `README.md`, "Proof effort"): three
  cold runs of the reference's `solution` stage, 2026-11-06, measured 10.4, 9.9 and 10.0 CPU s (`score/time_limits.json`; in wall-clock seconds, 2026-11-01: 7.42, 7.66 and 7.66 s); the other stages of
  `check.py` add the comparator (14 s) and `leanchecker` (13 to 14 s), which the limit does not count.
* **Scoring at `N = 16`**, no depth budget. The one ranked number is area x time on sky130 A0' (A0' decided 2026-11-03,
  the product 2026-11-05; svGolf `README.md`, "Scoring"): the cell area in um^2 times the critical-path delay of the
  scored netlist of the pinned two-stage Yosys + ABC flow, weighed by `score/ppa.py` (`sky130_a0_v3`, repaired by
  buffering only). Par, the proved array `clmul_n`, the simplest algorithm (one design per task, `leaderboard/par.json`, decided 2026-11-12), is 3429.5392 um^2 x 1114 ps = 3820.5
  um2*ns; the three designs under `tests/clmul/baselines/` are entries (the schoolbook tree `clmul_tree` 3323.2,
  13 % under par). The Pareto frontier
  of area and time, area in NAND2 gate equivalents and depth in gates are extra columns, for exploring, and the
  research flow A1' (`ppa.mapped`) is an unranked one; `python3.12 score/ppa.py solution.sv --task tasks/clmul
  --no-mapped [--path]` measures a design in seconds, with no Lean; the table below has them all. The score is deterministic, the same file always scoring the same: names,
  comments, blank lines, whitespace and the file name never change it, while operand order, how a chain of
  gates is grouped, gate forms and the order of statements do, and trying them is golf (svGolf `README.md`,
  "Scoring"; commuting the XOR of `clmul_n` moved its area 0.44%, measured 2026-11-05). Every number can be
  reproduced bit for bit: score/PPA.md, "Reproduce a score". `N = 8` and `N = 32` are reported alongside (not
  scored). The one-width generated netlists of `tests/clmul/unproved/` are in the generator's emission order, which
  is their canon.
* Post-synthesis check (`task.json` `postsynth`): ls-sv's reading and the scored netlist must agree on the fixed
  corners, the harvested comparison constants and seeded random vectors at `N = 16`.
* No x or z value may arise (README.md, "Rules"): no x/z literal digit (the source gate) and no out-of-range
  select, undriven net or logic loop at `N = 16` (the `fourstate` stage). Mind `N = 1`: `p` is one bit.
* **Input drive** (the sky130 score, `sky130_a0_v3`): every primary input is driven by `sky130_fd_sc_hd__buf_8`,
  the default (`task.json` names no `input_drive`), standing for the on-chip bus or register that feeds the block; the
  record says so in `ppa.setup.input_drive` (score/PPA.md, "The input drive").

## What counts as a solution

A file `solution.sv` with the module above, and a Lean file `Solution.lean` that imports `Submission.Design` and
proves `theorem Submission.solution : Submission.Goal`, where `Submission.Goal` is
`SvGolf.Tasks.Clmul.Statement design.sem` for the design the checker extracts from `solution.sv`:

```bash
python3.12 check.py tasks/clmul solution.sv Solution.lean
```

## Reference solution (`reference/clmul_n.sv`)

The array multiplier of `mul`, with XOR where `mul_n` has a full adder and no carries. Row `i` holds
`r[i][j] = XOR over t ≤ i of a[t] & b[i+j-t]` (a term whose `b` index reaches `N` is 0): the accumulator of the
first `i + 1` rows, shifted down by `i`. One 2-D packed array `r` of `N` rows of `N` bits, four generate loops:

```systemverilog
for (j = 0; j < N; j++) begin : g_row0
  assign r[0][j] = a[0] & b[j];
end
for (i = 1; i < N; i++) begin : g_row
  for (j = 0; j < N-1; j++) begin : g_bit
    assign r[i][j] = r[i-1][j+1] ^ (a[i] & b[j]);
  end
  assign r[i][N-1] = a[i] & b[N-1];
end
for (i = 0; i < N; i++) begin : g_lo
  assign p[i] = r[i][0];
end
for (m = 0; m < N-1; m++) begin : g_hi
  assign p[N+m] = r[N-1][m+1];
end
```

Output bit `i < N` is bit 0 of row `i`; the top `N-1` bits are the upper `N-1` bits of the last row. `N²` ANDs and
`(N-1)²` XORs, linear XOR depth `N` before synthesis (ABC re-balances: depth 6 at `N = 16`).

**The proof** (`reference/clmul_n.lean`, 238 code lines, 143 of them plain-Lean arithmetic; PROVING.md, section
3.1): `sv_structure (lexRank := clmulKey N)` with the rank `(row, 0, 0)` (through a partial classifier of the five
site families, with a theorem that it covers every site), `sv_interface`, `sv_equations`, `sv_cover`
(the coverage goals of the 2-D reads), one `sv_bridge` per equation into the fields of a `View` of the array, and
the mathematics: the row invariant `r i j = XOR over t ≤ i of a[t] & b[i+j-t]` by induction on the row, then the
collapse of the Spec's double sum over `i + j = k` for the low outputs (`k < N`) and the last row (`k ≥ N`). Axioms
`propext`, `Classical.choice`, `Quot.sound`; no `native_decide`. The reference array is invariant under the `canon`
step's layout, renaming and reordering variants (22 variants, byte-identical canonical RTLIL); swapping the
operands of every commutative operator gives 774.265 GE (recorded in `tests/expected.json`).

## Scores

Pinned flow (`score.py`, the two-stage canonical flow, Yosys 0.53), area in GE / depth in gates; every number is
in `tests/expected.json` (with the gate mix) and re-measured by `tests/run.py`. The last two columns are the
sky130 columns at `N = 16` (`score/ppa.py`, area um^2 / delay ps): A0' (`sky130_a0_v3`, the ranked sky130 score since
2026-11-03) = the scored netlist repaired by buffering only (no net of these designs is over its limits, so no buffer and no
resized cell) and weighed by sky130 cell areas and an STA with every input driven by the task's input drive,
`sky130_fd_sc_hd__buf_8` (the default); A1' = a real `abc -liberty` mapping (unranked). Re-measured 2026-11-04 (`ppa.py SV
--task tasks/clmul --no-mapped`): against `sky130_a0_v2` (inputs driven by `buf_1`) the A0' areas are unchanged and the
delays -53 to -171 ps, with the same orders and the same frontier (against the unrepaired `sky130_a0_v1`, v2's delays
were +9.5 to +35.8%). Re-measured again 2026-11-04 with every load pin read per edge (`sky130_a0_v3` before its release,
`ppa.score_and_weigh` with the mapping): areas unchanged, A0' delays +0 to +14 ps, A1' +0 to +17 ps, the same orders and
frontier.

| design | proved | N = 8 | N = 16 (scored) | N = 32 | A0' at 16 | A1' at 16 |
|---|---|---|---|---|---|---|
| reference array (`reference/clmul_n.sv`) | yes, ∀ N (tactics) | 179.649 / 4 | **772.267 / 6** | 3214.731 / 7 | 3429.5 / 1114 | 2941.6 / 957 |
| entry: schoolbook, XOR tree per column, for every `N` (`tests/clmul/baselines/clmul_tree.sv`) | yes, ∀ N (tactics) | 179.649 / 4 | 772.267 / 5 | 3222.057 / 6 | 3429.5 / 969 | 2936.6 / 753 |
| entry: Karatsuba, 4-bit schoolbook base, level by level for every `N` (`tests/clmul/baselines/kara_lv.sv`) | yes, ∀ N (by hand) | 166.32 / 6 | **616.626 / 8** | **2056.88 / 10** | 2732.6 / 1810 | 2437.3 / 1902 |
| entry: one level of Karatsuba for every `N` (`tests/clmul/baselines/clmul_k1.sv`) | yes, ∀ N (tactics) | 167.32 / 6 | 651.95 / 7 | 2556.137 / 8 | 2890.3 / 1424 | 2563.7 / 1595 |

Measured, not proved, not on the site (test material since 2026-11-12, `tests/clmul/unproved/`, generated per
width by `tests/clmul/unproved/gen_clmul.py`: flat netlists that keep the task header but are correct only at the
width they were generated for, so no proof of the statement, which covers every `N`, can exist for them):

| design | N = 8 | N = 16 | N = 32 | A0' at 16 | A1' at 16 |
|---|---|---|---|---|---|
| schoolbook, XOR tree per column (`school_tree_*`; `clmul_tree` above is its parametric form) | 179.649 / 4 | 770.935 / 5 | 3219.393 / 6 | 3419.5 / 969 | 2936.6 / 753 |
| Karatsuba, 4-bit schoolbook base (`kara_b4_*`; `kara_lv` above is its parametric form) | 166.986 / 5 | 621.959 / 8 | 2068.877 / 11 | 2756.4 / 1807 | 2479.9 / 1896 |
| Karatsuba, 8-bit base (`kara_b8_16`) | | 643.283 / 7 | | 2854.0 / 1372 | 2486.1 / 1287 |
| Karatsuba, 2-bit base (`kara_b2_16`) | | 672.635 / 10 | | 2960.3 / 2055 | 2800.2 / 2129 |
| Karatsuba all the way down (`kara_full_16`) | | 677.638 / 9 | | 2979.1 / 2089 | 2859.0 / 2011 |

The one-width netlists show where the frontier is: Karatsuba with a 4-bit base is 19.5 % smaller than the array at
`N = 16` and 35.7 % smaller at `N = 32`, for two and four more levels; the optimum in the base is interior (2
bits 672.6, 4 bits 622.0, 8 bits 643.3, all the way down 677.6), and the schoolbook with a per-column XOR
tree is the array's twin in area (770.9 against 772.3) and one level shallower.

### Beyond the reference (what a better entry needs)

The best designs here are recursive and the recursion has no parametric form in the proof fragment today: the
tactics read a FLAT top module (instances and recursion are `le-recursion`; PROVING.md, section 4), so a
for-every-`N` Karatsuba needs either instances, or a fixed number of levels unrolled by generate loops with a
padded split (`N` odd). The proofs of such designs are the bilinearity identity `(aL + x^m aH)(bL + x^m bH) =
L + x^m (M + L + H) + x^2m H` over coefficient functions. Published bars to beat (recalled, not checked):
Montgomery's 5-, 6- and 7-term formulas (13, 17 and 22 multiplications), Bernstein, Cenk-Ozbudak and Fan-Hasan's
bit-parallel multipliers.

**A one-level Karatsuba for every `N`, measured on 2026-11-01 (proved since: the baseline `tests/clmul/baselines/clmul_k1.sv`
with `clmul_k1.lean`, 2026-11-12; the record below is the 2026-11-01 state).** A generate-for
design that splits the operands at `H = (N+1)/2` (a localparam), zero-pads the odd case, builds `L`, `Hh` and
`M = (aL ^ aH) (x) (bL ^ bH)` as three `H x H` arrays of the reference's shape and combines them with five more generate
families is correct for every `N` (Verilator, `N = 1 .. 5, 8, 9, 16, 31, 32, 33`) and scores **651.950 GE, depth 7 at
`N = 16`** (-15.6 % against the array), 2556.137 / 8 at `N = 32` (-20.5 %), 167.320 / 6 at `N = 8`;
`check.py --unproved --tactics` accepts it (`in_fragment: true`). Its proof, in the scratch directory of the work package
(`$SCRATCH/wptclmul/`: `g3/clmul_k1u.sv` with 19 sites and padded vectors `ap`, `bp`; `g3/clmul_k1v.sv` with the 16 sites of one
vector `abz = {1'b0, b, 1'b0, a}`; `probe/G3h.lean`), exists except for the coverage obligations: the Karatsuba identity at the level
of coefficient functions (`karatsuba_full`, `cl_sum`, `comb_spec`, about 150 lines), the structure theorem (`sv_structure (lexRank := …)`,
about 60 s of CPU at 19 sites and 110 s at 27, with a raised heartbeat limit), the 15 `sv_bridge` fields of the three arrays, the
combination equations and the whole chain from `sv_equations` to the Spec's `BitVec` all compile for the 19-site design.
**What blocked it was `sv_cover`, which has since been fixed** (2026-11-01): the whole coverage obligation was normalized as one
conjunction first, `sv_simp` ran out of its 100000 steps on the larger designs, `try` swallowed the error and the site-witness form
(`∃ b, (b = site₀ ∨ …) ∧ Q b`) was left behind; the fix renormalizes each goal after the split (`design/always-comb/G25-NOTE.md`, section 13). The 17 coverage
goals of the 19-site design (`design/tasks-week2/clmul/karatsuba/`) now close with the standard closer and no hand-written case split
(`Examples/system-verilog/comb_karatsuba/cover.lean`, `k1u_covers`). The Karatsuba proof is NOT yet registered as a reference: the
structure theorem takes about 60 s of CPU at 19 sites with a raised heartbeat limit, so registering it would raise the task's time
limit from the floor (then 120 s); that is the maintainers' decision.

## How people write clmul (and what our pipeline accepts today)

The maintainers' instruction (2026-11-01): look at how such circuits are written in the wild, so that the constructs
contestants use naturally are supported, not only the ones the tactics like. This section is the survey done
for this task: 23 files from 19 repositories found with `gh search code` (`clmul`, `ghash`, `carry-less multiplier`)
and a web search for Karatsuba over GF(2), fetched on 2026-11-01 as UNTRUSTED DATA (read with `cat`/`grep` only,
never executed, nothing copied into the repository; only URLs, the licence GitHub reports and one-line snippets
are recorded here). The eight-family survey that followed (`design/real-world-sv/SURVEY.md`, section 6 and
the ranked gap list of section 4; 30 of its 331 entries are clmul, and its 241 reduced probes, `probes/cl__c*.sv`
and `probe_results.json`, were run through the same `check.py --unproved --tactics`) reaches the same verdicts
on every clmul-shaped probe I compared (c01 unpacked chain: `design`; c02 size cast: `design`; c05 to c09 procedural
loops and functions: `fourstate`; c11 generate-local declaration: `design`; c03, c04, c10 bit-level generate and the
flat expression: accepted up to the proof). For each style there is a test design under `tests/clmul/attacks/` (correct for
every `N`, simulated in Verilator, run through `check.py --unproved --tactics` by `tests/run.py` and pinned in
`tests/expected.json` as ADVISORY entries): they document the gap, they are not statements about the task.

| # | style | seen in (all `github.com/<repo>/blob/<branch>/<path>`; licence as GitHub reports it) | test design (`tests/clmul/attacks/`) | `check.py --unproved --tactics` today |
|---|---|---|---|---|
| 1 | **nested procedural loops, one XOR-accumulate per partial product** (`r[i] ^= a[i-j] & b[j]` into a vector bit; or a chain through an intermediate vector indexed `S[WIDTH*i+j]`) | `openhwfoundation/cv32e40x` `rtl/cv32e40x_alu.sv` (NOASSERTION); CORE-V-WALLY `clmul.sv` as `zeroasiccorp/logikbench` `logikbench/benchmarks/large/wally/rtl/clmul.sv` (MIT repo, file Apache-2.0 WITH SHL-2.1) and the copy `brlditos/tft-assignment` `src/ieu/bmu/clmul.sv` | `proc_nested_for`, `wally_chain` | **refused at `fourstate`**: "run-time index in `b[i]`: a signed 32-bit index addresses …, outside the declared range" (a procedural loop counter is an `int`, hence a run-time index); behind it ls-sv does not load the loop (the extractor marks `ForLoopStatement` Unsupported: register `st-for`, rank 1) |
| 2 | **whole-word shift-and-XOR in a procedural loop or function**: `if (b[i]) p = p ^ (a << i)` | `fontamsoc/hw` `cpu/clmul.sv` (GPL-2.0, Verilog-2001 function `clmulFull`); `effanem/set_project` `rtl/gf64_mul.v`, `rtl/gf128_naive.v` (no licence listed); `akerlund/rtl_bch` `rtl/bch_gf.sv` (MIT, SystemVerilog function with `return`); `efectn/riscv-crypto-extensions` `rtl/units/clmul_unit.sv` (MIT, a 2-stage sequential unit around the loop); `karucore/karu64` (the reduced GF(2^128) form) | `proc_shift_xor`, `func_oldstyle_xor`, `func_shift_xor` | `proc_shift_xor`: **`fourstate`** as in 1. `func_oldstyle_xor`: **refused at `source`**: its counter `integer i` is declared outside the loop header (source gate item 7, the stopgap for ls-sv's procedural-loop defects). `func_shift_xor` (the `return` form): **refused at `banlist`** because the scorer's own Yosys frontend rejects `return` ("syntax error"): not even the pinned flow can read it. Behind both: a user function call is Unsupported in ls-sv (`ex-user-call`, rank 2) |
| 3 | **generate-for word-wide partial products and an XOR tree/chain**: `pp[i] = b[i] ? a << i : '0`, then XOR (a hand-unrolled tree of fixed depth for 32 bits) | `lowRISC/ibex` `rtl/ibex_alu.sv` (Apache-2.0); `ycakbas/rv32imafb-core` `rtl/execute/bitmanip/clmul_unit.sv` (no licence listed; "assumes WIDTH is a power of 2") | `gen_word_pp_chain`, `gen_pp_zerofill` | **accepted up to the proof** (source, extract, banlist, fourstate, design, score, postsynth all pass; the oracle agrees). The tactics refuse it: `site g_pp#0: unbased unsized literal '0/'1 inside an expression` (the zero-extension replication `{{(N-1){1'b0}}, a}` is read since 2026-11-02), and with the zero-fill written as a loop, `generate-for header outside for (g = <int>; …)` (the start must be an integer literal, `for (i = N; …)` is refused); behind that: the `'0` fill inside `?:` (PROVING.md, section 4: "write a sized literal") and, at the base commit these results were measured on (`9388ea91`), the run-time shift `aw << i`, which the tactics (`e862b83c`) have since added to the fragment: re-run `tests/run.py --only clmul` after merging it |
| 4 | **hand-unrolled flat expression**, one conditional word per bit of `b`, XORed in one assign (32 terms) | `chipsalliance/Cores-VeeR-EL2` `design/exu/el2_exu_mul_ctl.sv` (Apache-2.0, `{63{rs2_in[i]}} & {..., rs1_in, i'b0}`); `Arvern-Silicon/arvern` `rtl/verilog/arv_alu.v` (BSD-3-Clause) | none: fixed width by construction (a for-every-`N` statement cannot be met), the same class as the one-width generated netlists of `tests/clmul/unproved/` | n/a |
| 5 | **generate-for, one shift-and-add step per iteration, each an `always_comb` with a default and a conditional compound XOR** (`Z[i] ^= H[i-1]`) on 2-D packed arrays | `soc-hub-fi/Marian` `src/ip/crypto/gcm/src/mult_ghash.sv` (the RISC-V vector-crypto `vgmul`, with reduction) | `gen_always_step` | **refused at `design`**: ls-sv cannot run `AssignmentExpression:compound` (register `st-compound`, rank 17); a generate-local temporary (`logic [N-1:0] t;`) is refused the same way (`gen_local_column`, "generate-local declaration") |
| 6 | **Karatsuba on module instances**: one level with three base multipliers, or per-width modules, or a recursive parameterized module | `effanem/set_project` `rtl/gf128_karatsuba.v` (three `gf64_mul` instances; no licence listed); `patwarind/Karatsuba_algorithm_for_Multiplication` `KA_131bit/*.v` (a module per width); `JC-S/Karatsuba_multiplier_HDL` `rtl/karat_mult_recursion.sv` (GPL-2.0; integer arithmetic, `nSTAGE` recursion with generate-if) | `inst_karatsuba_1level` (procedural base), `inst_karatsuba_1level_gen` (generate-array base), `inst_karatsuba_rec` (recursive) | `inst_karatsuba_1level`: `fourstate` (its procedural base). `inst_karatsuba_1level_gen`: **accepted up to the proof** (the loader, the scorer and postsynth handle instances); the tactics refuse module instances. `inst_karatsuba_rec`: **refused at `extract`** ("no such module among top instances": a self-instantiating top, register `le-recursion`, rank 14) |
| 7 | **unary reduction XOR per column**, `p[k] = ^(a & window of b)` | not seen in the files read (the style the task description names; written here for coverage) | `reduce_xor_column` | **accepted up to the proof**; the tactics refuse the indexed part select `bpad[… +: N]` |
| 9 | **explicit size cast** to widen before shifting, `(2*N-1)'(a) << i` (the survey's commonest spelling of the word-wide partial product; 49 of its 331 entries use casts) | cv32e40x-style and `ibex`-style code in the survey's probes c01, c02 | `gen_size_cast` | **refused at `design`**: `ConversionExpression:Explicit` (register `cv-explicit`, rank 9) |
| 10 | **unpacked partial-product / accumulator arrays**, `logic [2*N-2:0] pp [N]` | `lowRISC/ibex` (`clmul_and_stage[32]`), the cogs core; survey probe c01 | `gen_unpacked_pp` | **refused at `design`**: `decl 'pp': unpacked array storage outside E (UnpackedDecl:memory)` (parameter-sized unpacked arrays) |
| 11 | **replicated-bit mask**, `(a << i) & {W{b[i]}}` | VeeR and scarv macros (the survey's second spelling of the shift-and-XOR accumulate) | `gen_mask_replication` | **accepted up to the proof**; the tactics read it since 2026-11-02 (at this task's base commit the first refusal was the run-time shift, added by gate 3a, then the genvar amount, gate 4b, then the replication of a bit select, gate 4c): `sv_structure` and `sv_equations` accept it |
| 12 | **Verilog-2001 nets**: `input wire` / `output wire`, `wire [N-1:0][N-1:0] r` | 13 of the survey's 30 clmul entries are Verilog (`effanem/set_project`, `Pim-aes-gcm`, `fontamsoc/hw`) | `verilog2001_wire` | **refused at `design`**: `decl 'a': unrecoverable packed dimensions` (register `dc-net-z`) |
| 13 | **`always @*`** per row inside a generate-for (60 of the 331 surveyed entries use `always @*`) | the survey's SHA/MD5 and ALU entries, `effanem`'s Verilog | `always_star_rows` | **refused at `design`**: `TimedStatement:ImplicitEventControl` (registers `pr-implicit-event`, `pr-event-list`) |
| 14 | **sequential / iterative** multipliers: one bit (or a few) per cycle under a start/done handshake | `allan70627/Pim-aes-gcm` `rtl/gf128_mul.v` (MIT); `lowRISC/opentitan` `hw/ip/aes/rtl/aes_ghash.sv` (Apache-2.0); `karucore/karu64` `rtl/zvk/karu_ghash.v` (BSD-3-Clause); `fontamsoc/hw` (a 2-cycle registered unit around style 2) | none | a different task class: the statement requires `Unclocked` and a combinational function (`always_ff` is refused by the statement); the sequential layer (`SeqTask`) is future work |

What the survey says:

* **More than half of the real code uses a procedural `for` loop** (9 of the 16 multiplier cores read: styles 1,
  2, 5, and the base of the instance designs; 2 use a generate-for with word operators, 2 are hand-unrolled, 3
  are built from instances); the natural way to write a carry-less multiplier today is `for (int i = 0; i < N; i++) if (b[i]) p ^= a << i;`.
  **None of those designs gets past `fourstate`**, the stage before ls-sv even tries to load them, and the
  message ("run-time index … outside the declared range") does not tell the contestant that the loop itself is
  the problem (the rule's own text says "ls-sv does not load procedural loops today"). This is the register's
  `st-for` (value rank 1); a PR that admits procedural loops must teach `fourstate` the loop bounds.
* The only natural styles that reach the proof stage are generate-for ones with word-level operators (3, 7) and
  instances (6); the tactics refuse them at replication, indexed part selects, shifts, a non-literal generate
  start and module instances respectively: each is a small, separate extension, all listed in
  `docs/sv-refusals.json` or PROVING.md section 4, none touched here.
* **The score does not depend on the style.** Every schoolbook form scores within 0.7 % of the array (Yosys + ABC
  canonicalize them: 770.9 to 775.6 GE at `N = 16`, depth 5 or 6); the `if (b[i])` form scores 774.3, the nested
  loop form 770.9, the same as the one-width per-column XOR tree netlist. Karatsuba on instances: 650.6 GE for one level,
  625.0 for the recursion with a 4-bit base. So the proofs, not the scores, separate the styles.
* The Zbc units of RISC-V cores (`clmul`, `clmulh`, `clmulr`) return one `N`-bit SLICE of the product and
  many compute `clmulr` by reversing the inputs and the result; this task's `2N-1`-bit full product is the form of
  GHASH and of the polynomial arithmetic. A contestant must not return a slice (`negative/wide_out.sv` and the
  interface conjunct).
* `MoonbaseOtago/vroom` `rv/mul.sv` (GPL-3.0) takes its 64-bit product from a generated include (`mk19_64.inc`,
  not fetchable) and carries `synthesis full_case parallel_case` pragmas, which the source gate refuses.
* `return` in a function is accepted by slang and refused by the Yosys frontend of the pinned scoring flow: a
  gap outside ls-sv, in the scorer (`func_shift_xor`).

What the reference and the proved designs cover: the generate-for AND/XOR array with a 2-D packed accumulator (the
reference, par; the shape the tactics prove), the proved parametric entries (the schoolbook with an XOR tree per column,
the level-by-level Karatsuba with a 4-bit base, the one-level Karatsuba), the generated one-width flat netlists as
test material (`tests/clmul/unproved/`, not on the site), and, as ADVISORY attack entries, the styles above. Nothing in `LeanModels/Sv` was changed.

## Validation (`tests/clmul/validate/`)

`validate.py` (quick): the oracle equals an independent implementation by Kronecker substitution on every pair at
`N <= 6` and on random pairs to `N = 100`; the FIPS 197 products reduce to `{c1}` and `{fe}`; and the TRUSTED
Lean spec, evaluated by Lean's interpreter, equals the oracle on every pair at `N = 1 .. 7` and on samples to
`N = 64`. `sim.py` (Verilator) simulates the reference, every baseline and every wrong design against a
whole-word shift-and-XOR testbench (exhaustive at `N <= 8`, 100 000 random pairs to `N = 64` in the full plan).

## Negative designs (`tests/clmul/negative/`)

Eight designs the task must reject, with the evidence (`Refute.lean`: kernel-checked refutations whose runs are
interpreter-checked) and the `check.py` stage each fails at: `top_shift` (wrong bit), `drop_top` (dropped term),
`or_accumulate` (wrong gate), `reversed_p` (the reflected orientation), `wide_out` (a `2N`-bit `p`), `only_n16`
(correct only at the scoring point), and the two CORRECT designs the banlist refuses: `plus_xor` (the XOR as a
one-bit `+`) and `kronecker_mul` (Kronecker substitution through `*`). Both synthesize to the reference's
netlist: the ban protects the task, not the score. `tests/clmul/negative/README.md` has the table.

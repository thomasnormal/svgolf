# WP-H2, gate 0: proving the `fdiv16` reference (feasibility spike)

**Outcome (2026-11-01): gates 1 and 2 are done, the reference is proved.** The recommended rewrite (t4, section 4) is the
reference `tasks/fdiv16/reference/fdiv16.sv`; the math layer M3a to M3f is `tasks/fdiv16/Dp*.lean` (registered in
`tasks.lean`), the glue and the solution are `DpGlue.lean` and `reference/fdiv16.lean`; `check.py` accepts it (stages,
`--postsynth full`); exhaustive Verilator over all 2^32 pairs: 0 mismatches. Gap table (section 3): G1 and G2 were worked
around as proposed (localparam bounds, flat rows); the heartbeat bracket of `sv_equations` on t4 is 250,000 fail, 275,000
pass, the whole chain adds a few thousand (the solution carries `maxHeartbeats 300000`). Below: the gate-0 note as written.

Status: NOTE, 2026-11-01, branch `wph2` (fast-forwarded to `svgolf-prep` `e862b83c`, which has WP-B2 gate 3a, run-time
shifts, and WP-G S1b gate d1). Labels: MEASURED (a probe I ran, file named), READ (from a source file, `file:line`),
MODEL (the Python model `h2/datapath_model.py`), PLANNED (a proposal). Everything is under
`svgolf/design/fdiv-param/h2/` (probe designs) and, outside the repo, the scratchpad `wph2/probe/` (Lean probes, raw
outputs). No file of `LeanModels/`, `check*`, `score/` or the trusted `tasks/*/Spec.lean` was touched.

## 0. Summary and go/no-go

1. **The reference as written is outside the fragment** (`check.py --unproved --tactics`: "OUTSIDE the sv_comb fragment:
   site `plain#3`: legacy part select"), **but a wiring-level rewrite is inside it, and the whole pipeline accepts it.**
   `h2/fdiv16_t4.sv`, a FLAT netlist (no generate loop, no 2-D array, no `always_comb`; the 13 restoring steps written
   out), scores **1929.778 GE, depth 299** (the draft: 2089.081 GE, depth 298; area -7.6 %), has 0 functional mismatches
   on the checker's 236 light vectors and on 343,736 Verilator pairs, and the REAL tactics run on it: `sv_structure`
   (rank table from `h2/mkrank.py`) in under a second of tactic time at the default heartbeats, `sv_interface`, and
   `sv_equations` (111 equations, the obligations decided, only `inputsKnown` left) in under 45 s at
   `maxHeartbeats 600000` (the whole probe file, structure + interface + three equation runs, took 106 s). The variants with the loop (`t0` to `t3`) each stopped on a different measured gap
   (section 4); the circuit differs from the draft only in the shifter (R2, a cheaper mux shifter that collects the
   sticky bit; exhaustively equal), in declarations (R1) and in naming (R3).
2. **Gate d (multi-window `always_comb` equations) is NOT needed:** the reference has one `always_comb` and it writes one
   window (`q`); it is accepted today (`b9_table`), and the flat rewrite replaces it by a `?:` chain over named words.
   **Gate 3a (run-time shifts) is in the tip and covers `qm >> sh`, `qs << sh` and the normalizer's constant shifts**;
   gate 3b (concatenation operands) is needed only by the AS-WRITTEN reference (`eoff`, `mag`, the divider's
   `>= {1'b0, nb4}`); gate 3c (`Part.cmp`) only by `{ea != 5'd0, fa}` and comparisons in conditions, which the
   lead asked to write as one-bit signals anyway. Waiting for any gate would buy nothing: the rewrite needs none.
3. **Seven tactic gaps were found and ranked (section 3), none blocks:** G1 legacy part select (workaround: localparam
   declarations), G2 loop-indexed 2-D row access (workaround: part-select rows or named vectors), G3 comparisons in
   conditions, G4 concatenation operands/arms, **G5 a generate family or an `always_comb` puts `sv_structure` on a
   slow path that does not finish in 10 times the default heartbeats (hence the flat design)**, G6 rank by hand, G7 the
   rest. The cheapest high-value fixes are G1 (est. 1 to 2 agent-days) and a diagnosis of G2.
4. **The math layer is feasible without any solver**, in plain Lean, six pieces M3a to M3f (section 5). PROVED at
   gate 0 (probes, compile in 9 s and 7 s, no Mathlib): the normalizer and its BitVec bridge (kernel evaluation over 2^11
   values), the exponent identity (`omega`), the divider rows are `restRem` (induction), and the rounding core (`omega`
   after a split on the 13 shifts). The remaining hard piece is M3e/M3f, the certificate for the packed result in three
   cases: 500 to 700 lines, no new idea needed. A Python model of the datapath (`datapath_model.py`) checks every
   intermediate fact the decomposition relies on, and `cert16` itself, on 290k finite pairs (0 failures).
5. **Go / no-go:** M3a, M3b, M3c, M3d: DONE for the probe datapath, GO to finalize. M3e/M3f: GO (largest). Final
   composition: GO. Design layer on `t4`: GO. Estimated total: G1 about 1000 to 1250 lines, G2 about 750 lines, 8 to 11
   slot-hours (section 6); expected `solution` compile time 3 to 6 minutes, i.e. a time limit of 12 to 24 minutes.

## 1. How this was measured

* Tip `e862b83c`; build products cloned from the shared tree and then brought up to date (the shared tree's tactic
  oleans were STALE with respect to its sources: a first round of probes ran against them and showed the pre-3a
  messages. Anyone probing with a cloned `.lake/build` should run `lake build LeanModels.Sv.CombProcTactic` first).
* Probes: `h2/b*.sv` (the reference cut into blocks, each as written `bN_*` and rewritten `bNb_*`), `h2/m*.sv`, `h2/g*.sv`
  (micro designs), `h2/s*.sv` (styles of real code, section 7), `h2/fdiv16_t0.sv` … `t4.sv` (the rewrites, section 4).
  Each through `load_sv` + `sv_structure?` and `sv_equations?` (the refusal text is the finding).

## 2. What the pipeline reads of the reference, construct by construct

The first column is the reference as written (`tasks/fdiv16/reference/fdiv16.sv`, line numbers).

| ref. lines | construct | today (tip `e862b83c`) | after gate 3 (3b, 3c) | after gate d |
|---|---|---|---|---|
| 39-41 | `sa = a[15]`, `s = sa ^ sb` (bit selects of a port, XOR) | yes | yes | - |
| 42-45 | `ea = a[14:10]`, `fa = a[9:0]` (constant part selects, literal bounds) | **no**: legacy part select (G1; `b1`) | no (not a gate-3 item) | - |
| 48-53 | `(ea == 5'd31) && (fa != 10'd0)` (comparisons under `&&`) | yes (`t4`) | yes | - |
| 57 | `ma = {ea != 5'd0, fa}` (a comparison as a concatenation part) | **no**: "expression construct outside the v1 fragment" (G3; `b2`) | 3c `Part.cmp` (designed, unscheduled) | - |
| 58, 61-62 | `xa = (ea == 5'd0) ? 5'd1 : ea` | yes (`b2b`) | yes | - |
| 67-74 | normalizer: `ma[10:3] == 8'd0`; `za8 ? (ma << 8) : ma`; `~na3[10]` | part select **no** (G1); constant shifts under `?:` yes (gate 3a, `b3c` with R1 declarations); `~x[10]` yes | same | - |
| 87-89 | `lza = {za8, za4, za2, za1}` | yes | yes | - |
| 93-95 | `logic [13:0][11:0] rem`; `rem[0] = {1'b0, na4}` (row, constant index) | yes with localparam/param dims (`m2`, `g5`); **no** with literal dims (G2; `m1`, `g2`) | - | - |
| 96-99 | 13-step `generate for`: `qq[12-i]`, loop-indexed rows `rem[i]`, `rem[i+1]` | **no**: structural check fails on a loop-indexed ROW access (G2; `g1`, `g3`, `g6`, `b4c`, `t0`); cells `r[i][k]` are fine (`g4`) | - | - |
| 97 | `qq[12-i] = (rem[i] >= {1'b0, nb4})` (concatenation as a comparison operand) | recognizer yes, `sv_equations` **no** (G4) | 3b (in flight) | - |
| 98 | `(rem[i] - {1'b0, nb4}) << 1` | **no**, by design since 3a: a shift operand must be an access, a sized literal or an unsized constant (G4); `rem[i] << 1` yes | no (not planned) | - |
| 105-107 | `adj = ~qq[12]`; `qm = qq[12] ? qq[12:1] : qq[11:0]`; `st0 = (qq[12] & qq[0]) | (rem[13] != 12'd0)` | `~qq[12]` yes; the part selects **no** (G1; `b5`); the `!=` in an operand of `|` not probed in this form (the rewrites name it first, `rnz`) | - | - |
| 111 | `eoff = {2'b0, xa} + {3'b0, lzb} + 7'd47 - … - {6'b0, adj}` (concatenation operands of `+`, `-`) | recognizer yes, `sv_equations` **no** (G4; `b6`); with implicit zero extension (`xa + lzb + 7'd47 - xb - lza - adj`) yes (`b6b`) | 3b | - |
| 117-119 | `ovf = (eoff >= 7'd63)`, `nrm`, `dsh = 7'd33 - eoff` | yes (`b7b`) | yes | - |
| 120 | `sh = nrm ? 4'd0 : ((dsh >= 7'd12) ? 4'd12 : dsh[3:0])` | **no**: comparison in a `?:` condition (G3; `b7`), and the part select (G1) | no | - |
| 127-130 | `qs = qm >> sh` (run-time shift), `st1 = st0 \| ((qs << sh) != qm)`, `rb = qs[0]`, `inc` | **yes** (gate 3a; `b8` sites 0 to 3 accepted) | yes | - |
| 131-132 | `ef = nrm ? eoff[4:0] : 5'd0`; `mag = {ef, qs[10:1]} + {14'd0, inc}` | part select **no** (G1); concatenation operand of `+` **no** (G4, inferred from `b6`) | 3b | - |
| 135-146 | the `always_comb` table: `if (a_nan \|\| b_nan \|\| (a_inf && b_inf) \|\| …) q = 16'h7E00; else if … q = {s, mag}` | **yes**: structure and equations (`b9`) | yes | **not needed**: ONE window (`q`); gate d is about bodies that write several |

## 3. Gaps, with measured cost (REPORT; nothing was patched)

Ranked by what they cost the fdiv16 proof (and any other design that unpacks a format or iterates a recurrence). All
MEASURED on tip `e862b83c` unless marked READ. A gap is a report to the lead; the workaround is what the rewrite uses.

**G1. "legacy part select"** (`CombView.lean:614`, `leafRd?`). Every constant part select `x[hi:lo]` whose declaration has
literal bounds is the extractor's legacy `PartSel` (`extract.py` `_sym_array_select_depth1`: "literal labels over
literal declared bounds stay legacy") and is refused by `sv_structure` and `sv_equations` alike. The as-written
reference has 15 such reads (`a[14:10]`, `ma[10:3]`, `qq[12:1]`, `eoff[4:0]`, `dsh[3:0]`, `qs[10:1]`, …), and so has
every design that unpacks a floating-point format, and every packed-struct member select (`a.e`, lowered to a `PartSel`).
The real-world survey found the same refusal independently (its x01, x07, x11) and ranks the fix 7th of its gap list.
Probes: `m4_part_lit` refused, `m3_part_lp` accepted, `m5_bits_cat` accepted. WORKAROUND (free, no score change): declare
the vector with localparam bounds (`localparam integer W11 = 11; logic [W11-1:0] ma;`, ports copied once into
`logic [W16-1:0] aw, bw`), or write the field as a concatenation of bit selects. FIX (not measured, ESTIMATE 1 to 2
agent-days): either send canonical literal selects through `ArraySel` in symbolic mode (one extractor predicate, but it
changes the cache key and envelopes of every design that has one) or give `leafRd?` a `.partSel (.ident n) (.int hi)
(.int lo)` arm with its instance lemma next to `arrayPartGeom`. It is the single most valuable fix for floating-point
tasks.

**G2. A loop-indexed ROW of a 2-D array fails the structural check.** A whole-row read or write whose index mentions a
loop variable (`rem[i + 1] = …`, `… rem[i] …`) makes `sv_structure` and `sv_equations` stop with "structural check
failed: site `g#0[i]`: the access `r[i + 1]` does not match the declaration of `r` (a select needs zero-based descending
packed dimensions `[hi:0]` …)", although the declaration IS `[R-1:0][C-1:0]`. MEASURED on six micro designs: loop-indexed
rows fail with localparam dimensions (`g1`), parameter dimensions as in the `mul` references (`g3`), literal dimensions
(`g2`) and with the other side as cells (`g6`); constant-index rows pass with localparam or parameter dimensions (`m2`,
`g5`) and FAIL with literal dimensions (`m1`, `g2`: `r[0]`, `r[3]`); cell accesses `r[i][k]` always pass (`g4`, the `mul`
references). READ: `Summary.accOk` (`CombView.lean:1248`) compares the row width with `m2 + 1`; why it fails for
loop-indexed rows is not diagnosed (a bug or an unrecorded restriction: PROVING.md section 4 lists "a whole row of a 2-D
array `x[i] = e`" as accepted, and no existing example has a loop-indexed row). WORKAROUND: write the row as a full-width
part select (`rem[i][11:0]`; depth-2 selects pass, `t2`/`t3`), or name the 13 rows (`t1`/`t4`).

**G3. A comparison in a self-determined position.** `{ea != 5'd0, fa}` (a comparison as a concatenation part: the
designed-but-unscheduled `Part.cmp` of gate 3c) and `… ? x : (dsh >= 7'd12) ? …` (a comparison in a `?:` condition) are
refused with a message that says so. The survey counts 33 of its 37 divider files with a comparison in an `if`/`?:`
condition. WORKAROUND: write the comparison into a one-bit signal first (`nz`, `big`), free; the lead's instruction for
this rewrite. Worth a PROVING.md line and perhaps a sharper advisory message ("name it first").

**G4. Operands that are operations or concatenations.** (a) A concatenation as an operand of `+`, `-`, `>=` (the
as-written `eoff`, `mag`, and the divider's compare): the recognizer reads it, `sv_equations` refuses (gate 3b is in
flight). (b) **A concatenation as an ARM of `?:`** (`sh[0] ? {1'd0, qm[11:1]} : qm`): `sv_structure?` reads it,
`sv_equations?` refuses ("a right-hand side is outside the fragment", `m7_concat_arm`); a constant shift
(`sh[0] ? (qm >> 1) : qm`, `m8_shift_arm`) is accepted, and so is a reduction of a part select inside `&`/`|`
(`m9_reduce_part`). (c) An operation as the left operand of a shift (`(rem[i] - nb) << 1`): refused BY DESIGN since 3a
("write it into a signal first"). WORKAROUNDS: name the operand; use constant shifts, not concatenations, as `?:` arms;
write the exponent sum with implicit zero extension (which gate 1 reads).

**G5. Cost: a generate family or an `always_comb` puts `sv_structure` on the slow path.** The fast path ("a flat netlist
leaves nothing", PROVING.md sections 2.1 and 12: every site plain, no free parameter, no `always_comb`; the obligations
are DECIDED, linear in the sites: 113 sites in 12 s) is lost as soon as the design has a `generate` loop or an
`always_comb`, and then the obligations are normalized by `simp`: `t3` (65 plain sites, a 3-site family of 13 instances,
one `always_comb`) does not finish at 400,000 / 800,000 / 1,600,000 / 2,000,000 (x1000 raw) heartbeats (the default is
200,000; `mul_tree`'s `tree_struct` needs 797,104), while `sv_equations` and `sv_interface` on the same design pass at
2,000,000. So a fixed-size 13-step divider must be written FLAT (`t4`). Not a bug, a complexity of the slow path in the
number of sites; it matters for every "sequence of many stages" design.

**G6. The rank certificate by hand.** `sv_structure (rank := …)` needs a function of the site identity; for 111 plain
sites it is a table. `h2/mkrank.py` computes it from the source (longest dependency path; bit-level for the
bitwise-written `qq`; ~60 lines of Python). A tactic option `rank := depth` (compute it from the summary) would remove the
hand work for every fixed-size design.

**G7. Other constructs** (section 7): procedural `for`, functions (WP-PROC is designing both), `casez`, `$clog2`
localparams, replication, indexed part selects, instances, `unique`, `wire`, `import`: refused today and not needed by
the rewrite.

## 4. The rewrite

Five variants were written and probed; each stopped for a different measured reason, which is the content of this
section (`h2/fdiv16_t0.sv` … `fdiv16_t4.sv`, all the same circuit as `tasks/fdiv16/reference/fdiv16.sv` up to the changes
named here; every variant passes the checker's `--unproved` stages, `tactics: inside the sv_comb fragment` and 0
functional mismatches on its 236 light vectors, and `t0`, `t1`, `t3`, `t4` also 0 mismatches in 343,736 Verilator pairs; `t2` is `t0` with other spellings).

| variant | what it is | what stopped it | score (GE / depth) |
|---|---|---|---|
| `t0` | the reference with R1 (localparam-declared vectors), R2 (mux shifter, constant shifts as concatenations), R3 (named comparisons); generate loop over `rem`/`dif` (2-D), `always_comb` table | `sv_structure`: loop-indexed ROW accesses fail the structural check (G2); concatenations inside `?:` arms are outside the equations fragment (G4 (b)) | 1937.445 / 300 |
| `t1` | `t0` with the loop written out (13 named row vectors `r0..r13`, `d0..d12`) | no 2-D array, so G2 is gone, but the real `sv_structure` hits the default heartbeat limit (PROVING.md: no fast path with an `always_comb`); `sv_equations` refuses the concatenation arms | 1936.116 / 305 |
| `t2` | `t0` with every loop-indexed row access a full-width part select (`rem[i][11:0]`) | the structural check passes; `sv_structure` times out at 200,000 | 1937.445 / 300 |
| `t3` | `t2` with constant shifts (`ma << 8`, `qm >> 1`, `dif[i][11:0] << 1`) instead of concatenation arms | `sv_equations` and `sv_interface` ACCEPT it; `sv_structure` does not finish at 400k, 800k, 1.6M, 2M (units of 1000 heartbeats: 10 times the default): a generate family and an `always_comb` together keep the slow path of the obligations | 1962.439 / 299 |
| `t4` | **flat**: no generate, no 2-D array, no `always_comb`; the table is a `?:` chain over named words; all sites plain | **accepted by every tactic**: `sv_structure` (rank = dependency depth, `h2/mkrank.py`) 0.6 s of tactic time and about 10 s of checking at the default heartbeats; `sv_interface`; `sv_equations` at `maxHeartbeats 600000` in under 45 s (111 equations; `decided … auto, inRange, width, bitRead, cover`; only `inputsKnown_1`, `_2` left); `sv_equations?` prints the shapes of section 5.3 | **1929.778 / 299** (1293 gates) |

The three kinds of change relative to the draft reference:

* **R1 declarations by localparam bounds.** Every vector that is part-selected is declared `logic [W11-1:0] …` with
  `localparam integer W11 = 11;`, and the ports are copied once into `aw`, `bw` (`logic [W16-1:0]`). Reason: a part select
  `x[hi:lo]` with literal labels over a literally-bounded declaration is emitted by the extractor as the LEGACY `PartSel`
  (`extract.py` `_sym_array_select_depth1`: "literal labels over literal declared bounds stay legacy"), which the
  tactics refuse (`CombView.lean:614`). MEASURED: `m4_part_lit` refused, `m3_part_lp` accepted (also the survey's x40);
  `m5_bits_cat` (a concatenation of bit selects) is the other workaround.
* **R2 the subnormal shifter.** `qs = qm >> sh; st1 = st0 | ((qs << sh) != qm)` becomes a 4-stage mux shifter (shift by 1,
  2, 4, 8 under `sh[0..3]`) whose stages OR the dropped bits into the sticky bit (`h2/b8b_round_rw.sv`; exhaustively equal
  to the original over all 4096 · 13 · 2 inputs, `h2/shifter_eq.py`). Run-time shifts are in the tip (gate 3a) and the
  original two lines are READ by the tactics (`b8` sites 0 to 3 accepted), so the mux form is a cheaper circuit, not a
  workaround; but its arms must be constant SHIFTS (`qm >> 1`), not concatenations (G4 (b)).
* **R3 named subexpressions.** `nz = ea != 5'd0` before `{nz, fa}` and `?:`; `nb12 = {1'b0, nb4}` and `dif = r - nb12`
  before the compare/shift; `big = dsh >= 7'd12` before the nested `?:`; `efq = {ef, qs[10:1]}` before `efq + inc`; the
  exponent sum with implicit zero extension (`xa + lzb + 7'd47 - xb - lza - adj`, slang's `Resize` marker, which gate 1
  reads). Every comparison is a one-bit signal before it is used as a condition, as the real-world survey found
  necessary independently.

**Scores** (`check.py --unproved`, the pinned flow) against the draft's 2089.081 GE, depth 298: the saving of 7 to 8 %
is the shifter (the original computes `qm >> sh`, then `qs << sh`, and a 12-bit inequality). **Functional checks**: 236
light vectors per variant, 0 mismatches; Verilator against the C port of the spec on 343,736 pairs (S0, every
constructed tie, 300,000 random), 0 mismatches for `t0`, `t1`, `t3`, `t4` (`validate.py --only sample --sv …`, 4 s each); the Python
model `datapath_model.py` on 290k finite pairs; `Fdef.lean` (`F`, the transcription of `t0`) against the trusted `fdiv16`
on golden vectors and 20,000 pairs. NOT yet run: the exhaustive 2^32 Verilator step (about 2 min on 8 cores), which
belongs to the final reference at G2.

## 5. Decomposition of the proof

### 5.1 The shape of the whole proof

`Submission.solution : Goal` is `CombTask.satisfiedAt_of_comb` (the flat `t4` has no `always_comb`, so no lowered twin; `sbox_bp.lean` is the model:
rank table, `sv_structure`, `sv_interface`, `sv_equations`) applied to

* **S** `sv_structure (rank := rippleRank (fun p => prT4.getD p 0) (fun _ _ _ => 0))`: `CombDesign design.sem ∧ Acyclic design.sem`; **I** `sv_interface`;
* **E** one settled-state lemma: in every `st` solving the equations of `design.sem` with `a = A`, `b = B` known, `lookup st "q" =
  some (LVec.ofBitVec (F A B))`, where `F` is the Lean transcription of the datapath (section 5.2);
* **M** the math theorem `F A B = fdiv16 A B` for all `A B : BitVec 16`.

**E** is the design layer (the tactics give the equations, a glue calculus turns them into `BitVec` facts); **M** is the
math layer (plain Lean, independent of ls-sv). They meet at `F` only.

### 5.2 `F`, the transcription (design layer's target, math layer's subject)

One Lean definition per signal of the rewritten reference, in `BitVec` operations that read like the SystemVerilog
(`h2/Fdef.lean` transcribes `t0`; the flat `t4` computes the same value in every signal, only the spelling differs.
`Fdef.lean` was compiled at gate 0: `F` agrees with the trusted `fdiv16` on the 9 golden vectors and on 20,000
xorshift pairs by `#guard`, 3 s). Blocks (`F_k`):

| block | SV (`t4`) | `F_k` | what it computes |
|---|---|---|---|
| B1 unpack | fields, classes | `ex, fr, nz, mant, xe`, class `Bool`s | `ea, fa, ma = {ea≠0, fa}, xa = max(ea,1)`, `a_nan…` |
| B3 normalize | `na1…na4`, `lza` | `n1…n4`, `lzc` | 8/4/2/1 left normalizer, shift count |
| B4 divide | `r0..r13`, `d0..d12`, `qq[12-k]` | `remF na nb : Nat → BitVec 12`, `qqF` | restoring recurrence; `qq[12-i]` = step i's bit |
| B5 qnorm | `adj, qm, st0` | `adjF, qmF, st0F` | one-bit normalization, sticky from the last remainder |
| B6 exponent | `eoff` | `eoffF` | `xa + lzb + 47 - xb - lza - adj` in 7 bits |
| B7 shift amount | `ovf, nrm, dsh, sh` | `shF`, `ovf`, `nrm` | subnormal shift, clamped at 12 |
| B8 round | `q1…qs, t1…t3, st1, rb, inc` | `sh1…qsF, st1F, incF` | mux shifter with sticky, round-to-nearest-even decision |
| B9 pack | `ef, efq, mag` | `magF` | `{E, T} + inc` (carry into the exponent field) |
| B10 table | `c_nan, c_inf, c_zero`, `w_*`, `q` (a `?:` chain) | the `if` chain of `F` | specials, `ovf` row, `{s, mag}` |

The glue calculus (design layer) proves, signal by signal in rank order, `lookup st "sig" = some (ofBitVec (F_sig A B))`
from the printed equation `eq_sig_k` and `known_sig_k`.

### 5.3 The glue calculus (E)

`LeanModels/Sv/CombWord.lean` already has `XF.bv_addBits`, `bv_subBits`, `bv_zext`, `bv_shlBits`, `bv_shrBits`, `lt_bv`,
`le_bv`; the proof file adds one small lemma per operator KIND that the rewrite uses (each a `getLsbD` extensionality,
5 to 15 lines): bit select, part select, concatenation of accesses and literals (`catBit`), `?:`, `==`/`!=` (`XF.eqv`),
`>=`, `&&`/`||`, `&`/`|`/`^`/`~`, reduction-or (`XF.any`), constants. About 15 kinds, ~250 lines; then one application
per signal (~110 signals, 3 to 5 lines each: ~350 lines). In the flat `t4` the 13 restoring steps are 13 explicit blocks of
three equations (`qq[12-k]`, `d_k`, `r_{k+1}`), so the design layer proves ONE step lemma (`lookup st "r_k" = ofBitVec
(remF k)` ⟹ the same for `k+1`, from the three printed equations) and applies it 13 times (~60 lines); the induction over
`k` lives in the math layer (`remF_toNat`). What `sv_equations?` prints for the flat `t4` (111 equations, `h2` probe `P10`; the stable aliases are `eq_<signal>_<k>`, so
`eq_na1_1`, `eq_qq_1 … eq_qq_13` (one per bit, source order), `eq_r1_1`, …, `eq_q_1`):

```
eq_na1_plain_22 : ∀ k < 11, st.boolAt "na1" k =
  if st.boolAt "za8" 0 = true then XF.shlBits (XF.zext 11 fun x => st.boolAt "ma" x) 32 (fun x => XF.constBit 8 32 x) k
  else st.boolAt "ma" k
eq_qq_plain_41 : st.boolAt "qq" 12 = decide (XF.val (fun x => st.boolAt "r0" x) 12 ≥ XF.val (fun x => st.boolAt "nb12" x) 12)
eq_r1_plain_43 : ∀ k < 12, st.boolAt "r1" k =
  if st.boolAt "qq" 12 = true then XF.shlBits (XF.zext 12 fun x => st.boolAt "d0" x) 32 (fun x => XF.constBit 1 32 x) k
  else XF.shlBits (XF.zext 12 fun x => st.boolAt "r0" x) 32 (fun x => XF.constBit 1 32 x) k
eq_q1_plain_90 : ∀ k < 12, st.boolAt "q1" k = if st.boolAt "sh" 0 = true then
  XF.shrBits 12 (fun x => st.boolAt "qm" x) 32 (fun x => XF.constBit 1 32 x) k else st.boolAt "qm" k
eq_q_plain_110 : ∀ k < 16, st.boolAt "q" k = if st.boolAt "c_nan" 0 = true then st.boolAt "w_nan" k else if …
```

All of these are covered by existing glue (`XF.bv_shlBits`, `bv_shrBits`, `bv_subBits`, `lt_bv`/`le_bv`, `bv_zext`, `eqv`,
`any`) or by one-line `getLsbD` lemmas. 

### 5.4 The math layer (M): six pieces, generic where possible

Generic statements are about integers/`BitVec` quantities, not about the reference's signal names, so that they can ship
in the `tasks` library next to `Cert16.lean` (and serve the parametric `fdiv-param` task: `FormatFacts.lean`/`CertF.lean`
already hold the certificate for every format). `F` and its bridges stay in the reference's own file.

* **M3a normalizer** `[PROVED at gate 0, kernel]`. `m4 m = m * 2^lzN m`, `1024 ≤ m4 m < 2048`, `lzN m ≤ 10` for
  `0 < m < 2048`; and the BitVec stages equal the Nat stages (`n4_toNat_K`: `(n4 (BitVec.ofNat 11 n)).toNat = m4 n`
  and `lzc` likewise). Both by `decide +kernel` over the 2047 significands, 2 lines each once the Nat stages are defined
  (a symbolic `split <;> simp_all <;> omega` version failed on 11 of 16 branches and is not needed).
* **M3b divider tie** `[PROVED at gate 0, the induction]`. `(remF na nb i).toNat = restRem nb na i` by induction on `i`
  using `restore_inv`'s bound `restRem < 2·nb` (no 12-bit wrap; `Nat.reducePow` must be in the `simp only` set or
  `omega` sees `2^12` as an atom), hence by `restore_spec` (PROVED) `qq = ⌊2^12·na / nb⌋`, `rem13 = 2·(2^12·na mod nb)`,
  and `qq ≥ 4096 ↔ na ≥ nb` (the last three facts are one-liners not yet written). ~60 lines in all.
* **M3c exponent** `[PROVED at gate 0, omega]`. `eoff + xb + lza + adj = xa + lzb + 47` for ALL 5-bit `xa, xb`, 4-bit
  `lz`: no 7-bit wrap at all, so `eoff` is an exact natural, and `E := eoff - 32`. `simp` + `omega`.
* **M3d rounding core** `[PROVED at gate 0, omega per shift]`. For `qm ∈ [2048, 4095]`, `sh ≤ 12`, `M = 2^(sh+1)` and
  `z = qs/2 + inc` (`qs = qm / 2^sh`, `inc = qs[0] ∧ (st0 ∨ dropped bits ≠ 0 ∨ qs[1])`): `z` is the round-to-nearest-even
  integer of `(qm + f)/2^(sh+1)` for EVERY `f ∈ [0,1)` with `f > 0 ↔ st0`, in cross-multiplied form (both bounds; a
  boundary is reachable only when `f = 0` and then only for even `z`). Two theorems, `st0 = true` (`z = (qs+1)/2`: the
  tie is impossible) and `st0 = false`, each `rcases` on the 13 shifts (`sh_cases`, `omega`) and one `omega` per case:
  `h2/` probe `Math1c.lean`, 7 s, no Mathlib, `exit 0`. (The first attempt, a kernel evaluation over all 106,496 cases,
  did not finish in 200 s; a `Nat.decidableBallLT` chain also needs `maxRecDepth`.)
* **M3e exact quotient value** `[pen and paper checked by MODEL]`. `qm = ⌊2^(11+adj)·na/nb⌋`, `st0 ↔ 2^(11+adj)·na mod nb ≠ 0`
  (from M3b by cases on `adj`), and the spec's exact quotient in least-subnormal units is
  `N/D = (qm + f)·2^(eoff-34)` with `f = (2^(11+adj)·na mod nb)/nb` (this is the identity `N·nb·2^(w⁻) = D·na·2^(w⁺)`,
  `w = eoff + adj - 23`, an exponent equation: `omega` + `pow_add`).
* **M3f the certificate for the packed result** `[the long piece]`. Three cases by `eoff`:
  (i) `eoff ≥ 63`: `c = {s, 7C00}`: `N ≥ D·4095·2^28` (`2^11·2^29 ≥ 4095·2^28`);
  (ii) `33 ≤ eoff ≤ 62` (E = eoff - 32 ∈ [1, 30]): grid spacing `2^(E-1)`, `mag = (E·1024 + T0) + inc` and
  `U(mag) = U(E·1024 + T0) + 2^(E-1)` also across the carry into `E + 1` (`T0 = 1023`; the `uOf` arithmetic, ~30 lines);
  M3d gives the two inequalities and the parity condition; the binade-bottom `dn` of `cert16` needs the carry case apart;
  `c = {s, 7C00}` after a carry from `E = 30` is the `E = 31` branch of `cert16` (`thr ≤ N`, exactly the tie case);
  (iii) `eoff ≤ 32`: subnormal grid spacing 1, `qs = qm >> sh`, `sh = 33 - eoff` (clamped at 12: `R < 2^-1` strictly).
  Each case is a conjunction of `D·(2u - dn) ≤ 2N ≤ D·(2u + up)` forms; cancel `D` and the power of two
  (`roundUnits_scale`-style), substitute M3e, close with `nlinarith`/`omega` on `z`'s defining relations.
* **Final** `F = fdiv16`: `fdiv16_table` (PROVED) turns `fdiv16 a b` into the special-case table; the six class
  conditions of `F` are `isNaN16…` by `expField_eq/fracField_eq`; the finite row is `finQuot a b = F a b`, which is
  `fdiv16_cert`/`cert16_bridge` (PROVED) applied to `cert16 a b (F a b) = true` (M3f). ~120 lines.

## 6. Sizes, slot-hours, risks

Lines are Lean lines of new code (comments excluded), estimated from what the gate-0 probes cost and from the nearest
finished proofs (`add_proc.lean` 140, `mul_n.lean` ~250, `sbox_table.lean` ~120 generated, `Cert16.lean` 543). "Slot-h" is
pure compile time on the shared slot (the queue itself was 30 to 60 minutes deep during this gate: wall time is a
multiple of it).

| piece | what | lines | slot-h | go / no-go |
|---|---|---|---|---|
| G1.0 | `F` (one def per signal), 9 golden `#guard`s + the 20k-pair sweep | 110 (compiled at gate 0: 3 s) | 0.1 | GO |
| G1.a | M3a normalizer: Nat stages, bridge, spec (kernel `decide`, 2047 cases) | 30 (PROVED at gate 0) | 0.1 | GO |
| G1.b | M3b divider tie: `remF = restRem`, `qq`, `rem13` from `restore_spec` | 60 (the induction PROVED at gate 0) | 0.3 | GO |
| G1.c | M3c exponent identity | 15 (PROVED at gate 0) | 0.05 | GO |
| G1.d | M3d rounding core (`core_t`, `core_f`: `omega` per literal shift) + the clamp-at-12 extension | 50 (core PROVED at gate 0, 7 s) | 0.2 | GO |
| G1.e | M3e exact quotient value (`qm`, `st0`, `N/D` identity) | 90 | 0.5 | GO |
| G1.f | M3f certificate, three cases (overflow, normal with carry, subnormal) | 500 to 700 | 2 to 3 | GO, the long piece |
| G1.g | final composition `F = fdiv16` (`fdiv16_table`, class lemmas, `fdiv16_cert`) | 120 | 0.5 | GO |
| **G1 total** | the math layer, plain Lean, Mathlib optional | **~1000 to 1250** | **~4 to 5** | GO |
| G2.a | the rewritten reference + exhaustive Verilator + checker `--unproved` + README/task.json/expected.json | 0 Lean | 0.5 (Verilator is not slot) | GO |
| G2.b | `sv_structure` (rank table from `h2/mkrank.py`), `sv_interface`, bridge lemma | 40 | 0.1 (measured: about 10 s) | GO |
| G2.c | glue calculus: 15 operator-kind lemmas | 250 | 1 | GO |
| G2.d | glue per signal / per block (B1..B10), ~110 signals | 350 | 1 | GO |
| G2.e | the 13 steps: one step lemma instantiated 13 times | 60 | 0.5 | GO |
| G2.f | assembly into `solution`, three cold runs, time limit | 60 | 0.3 (three cold runs of ~5 min) | GO |
| **G2 total** | the design layer | **~750** | **~4 to 6** | GO |

The `solution` stage will be: tactics (measured on `t4`: `sv_structure` about 10 s, `sv_interface` about 5 s, `sv_equations` under 45 s) + glue (~1 min) + the imported math (precompiled in the `tasks`
library, if the generic lemmas ship there, or compiled in the same file otherwise). Expected T = 3 to 6 minutes, hence a
time limit of 12 to 24 minutes by the rule `max(120, ceil(4 T))` (the draft's 3600 s is a placeholder). If the math
files do not ship in the `tasks` library and the Solution has to carry them, the Solution grows to ~2000 lines: split
`Solution.lean` into the checker-compatible single file only at the end (the file is generated by concatenation).

**Risks, in order.** (1) The M3f case analysis is the one place where the elaborator can fight back (`omega` with
big literals and `2^k` atoms, `nlinarith` on products): mitigated by the symbolic core (M3d) and the grid-additivity
lemma, and by proving each of the three cases as its own theorem. (2) The tactic gaps of section 3: the flat rewrite `t4` works around G1, G2, G4 and G5. (3) Queue: a 15-minute
slot is shared with four to six other agents; the fixed cost per edit-compile cycle is the queue, not the compile.
(4) The in-flight gates change printed equation shapes (3b): all glue is written against the stable aliases
`eq_<signal>_<k>`, which the gates keep.

## 7. How people write it

Twelve real implementations were read as untrusted text (`cat`/`grep` only, nothing executed, nothing copied into the
repo; the downloaded copies live in the agent scratchpad). URLs and licences, as printed by the files and by `gh api`:

| # | file | licence | what it is |
|---|---|---|---|
| 1 | https://github.com/pulp-platform/cva6 `core/serdiv.sv` | Solderpad 0.51 (file header) | serial integer divider, FSM, 2 `lzc` instances |
| 2 | https://github.com/pulp-platform/fpnew `src/fpnew_divsqrt_multi.sv` | Solderpad 0.51 | wrapper around the T-Head-derived div/sqrt, `typedef enum` FSM, input/output pipeline `generate` loops |
| 3 | https://github.com/pulp-platform/fpu_div_sqrt_mvp `hdl/{preprocess,nrbd_nrsc,norm,iteration}_div_sqrt_mvp.sv` | Solderpad 0.51 | the iterative non-restoring FP divider/sqrt behind FPnew: unpack, normalize, iterate, round |
| 4 | https://github.com/lowRISC/ibex `rtl/ibex_multdiv_slow.sv` | Apache-2.0 | shift/subtract integer divider, FSM |
| 5 | https://github.com/freecores/fpu `verilog/{post_norm,primitives}.v` | Rudolf Usselmann, 2000 (permissive notice in the header; no SPDX id) | OpenCores FPU; the divide is `opa / opb`, `opa % opb` |
| 6 | https://github.com/taneroksuz/fpu `verilog/src/float/fp_fdiv.sv` | MIT | FP divide in the Gaisler "v / r / rin" struct-of-registers style, multi-cycle |
| 7 | https://github.com/dawsonjon/fpu `divider/divider.v` | MIT | single-precision divider, one flat `always @(posedge clk)` with `case (state)` |
| 8 | https://github.com/haritha-debug/SOC_4_Flat `artix7_full_DDR_COMPLETE/verilog/dgrid_fp16_div_rtl.sv` | none stated | a COMBINATIONAL fp16 divider (the closest relative of our reference): significand `/` and `%`, nested-ternary leading-one search, run-time shifts |
| 9 | https://github.com/pulp-platform/common_cells `src/cc_lzc.sv` | Solderpad 0.51 | the standard leading-zero counter (binary tree of `generate` loops) |
| 10 | https://github.com/Bh4r4t/32-bit-Divider `divide.v` | none stated | combinational restoring divider unrolled BY HAND: 32 copies of a comparator, an "assigner" and a subtractor module |
| 11 | https://github.com/rsd-devel/rsd `Processor/Src/Primitives/Divider.sv` | Apache-2.0 | radix-2 FSM divider; `function automatic … CountSignificantBits` with a procedural `for` |
| 12 | https://github.com/google-coral/coralnpu `hdl/verilog/rvv/design/rvv_backend_div_unit.sv` | Apache-2.0 | vector-divide wrapper: `always_comb` with long `for (int i…)` ladders, `generate` |

(A `gh search code` run for combinational restoring dividers written as a procedural `for` inside `always_comb` found
only testbenches and iterative dividers; that style is the textbook one (lecture notes, tutorials) and appears in real
code mostly inside helper functions, as in #11.)

**The survey workflow's fpdiv entry** (`design/real-world-sv/SURVEY.md` section 6 and `per_topic.json`, 37 files, with
its measured probes in `probe_results.json`) was folded in after the first draft. Its summary: about half of the
dividers are bit-serial restoring/non-restoring FSMs over a `{rem, quot}` shift register; the rest are SRT radix-4/16
with a carry-save residual and a digit-selection ROM, combinational `/` and `%` on wide shifted numerators (banned
here), restoring loops in functions or `always_comb`, and unrolled generate stage chains; the floating-point wrapper is
always unpack/classify, an `if`-`else` special-case cascade, a leading-zero count by `casez`/`lzc`/loop, signed
exponent arithmetic with `$signed` and casts, and guard/round/sticky rounding. Its blockers for the tactics, with the
counts out of 37: loops inside functions, `signed` (20) and `>>>`, size casts (8), `casez` (3), comparisons in
`if`/`?:` conditions (33), function calls (12), generate-local stage variables (31), unpacked stage arrays, packages
(11), `$clog2` (13), sequential FSMs (19). Where the two overlap they agree with the probes below: the survey measured
the same "legacy part select" refusal (its x01, x07, x11) and the same localparam-declared-width workaround (x40
accepted), the same refusal of a comparison in a self-determined position with the one-bit-signal workaround (x28, w08,
r06), the same loop refusal (`LocalDecl` for the loop variable, `Unsupported ForLoopStatement`, and the svGolf
`fourstate` rule against a signed 32-bit loop index, `sg-fs-loop-index`). Two facts here come from it alone: **every
`wire` declaration is refused** (Verilog-2001 style `wire [N-1:0] x;`, `input wire …`, non-ANSI ports; use `logic`;
three of the files above (#5, #7, #10) are written that way), and **Yosys 0.53, the scorer, cannot read `import`**
(`pkg::name` is readable; a packed-struct PORT crashes it), `return`, `break`, `while` outside constant functions,
`foreach`, `inside` or streaming. Procedural loops and functions are being designed by WP-PROC.
**Consequence for the rewrite of the reference:** every comparison is written into a one-bit signal first (`nz`,
`big`, the `qq` bits, `rnz`; the `always_comb` table's conditions are wires), nothing is `signed`, nothing is a
function, the loop is a `generate for`, and the design needs no package.

**The styles, and what our pipeline does with each today.** The "pipeline" is: source gate, extractor, loader
(`load_design_sv2`, the `design` stage), then the `sv_comb` tactics. The measured columns come from
small modules `design/fdiv-param/h2/s*.sv` (section 9), probed with `load_sv` and `sv_structure?`.

| style (who writes it so) | probe (`h2/`) | loader (`design` stage) | tactics today | gate / fix |
|---|---|---|---|---|
| **FSM over cycles**: `typedef enum` state, `always_ff`, `unique case`, shift/subtract one bit per cycle (#1, #2, #4, #6, #7, #11) | `s6_fsm` | the SOURCE GATE refuses `unique` (`unique qualifier … ls-sv runs the first matching arm`); without it the sequential tier loads | not combinational: out of scope BY KIND for a `CombTask` (the statement has "no clocked process"); `sv_structure` is for assigns and `always_comb` only | a sequential task kind (`design/sequential`), not a tactic gate |
| **procedural `for` with a running remainder** inside `always_comb` (textbook restoring/non-restoring divider; the reference's loop written the way a software person would) | `s1_for_always`, `s1b_for_module_int` | REFUSED at load: `LocalDecl: unknown statement kind` (the loop variable `int i` is a block-local declaration); with a module-level loop variable (`s1b_for_module_int`) the design loads but `hasUnsupported = true` (`ForLoopStatement`), so the `design` stage refuses it (register `st-for`) | no | "procedural `for` accumulators (recurrence extraction)" is a separate, unscheduled gate (`always-comb/README.md` 2.2) |
| **function with a `for` loop** called from an `assign` (#11's `CountSignificantBits`) | `s2_function` | loads; `hasUnsupported = true` (`CallExpression`), so the `design` stage refuses | "out-of-tier module members are present" | no gate |
| **generate-for chain over a packed array**, one step per index (ours; the way a hardware person unrolls the loop above) | `fdiv16_t0` | loads, 0 unsupported | the recognizer reads it (`sv_structure?`); with row accesses written as part selects (`t3`) `sv_equations` and `sv_interface` pass, but the real `sv_structure` does not finish within 10 times the default heartbeats (G5); with whole-row accesses it fails the structural check (G2) | see gaps G2, G1 |
| **hand-unrolled** steps with named vectors or sub-module instances (#10: 32 copies of comparator + subtractor) | `fdiv16_t1` (named vectors); `s11_inst` (instances) | both load | named vectors with an `always_comb` table (`t1`): real `sv_structure` hits the default heartbeats; the FLAT variant (`t4`, table as a `?:` chain) is accepted by all three tactics; instances: "this design instantiates modules, and the `sv_comb` tactics cannot summarize module instances yet" (WP-I step I0) | instances need the hierarchy tactics (WP-I) |
| **`casez` / `casex` leading-zero count** (#5: 48 arms of `48'b001????…`) | `s3_casez_lz` | loads; `hasUnsupported = true` (`CaseStatement:WildcardJustZ`), so the `design` stage refuses | — | no gate; a plain `case` with a default (sized literals) IS in the fragment, `casez` is not |
| **priority `if … else if` chain** or **nested `?:` chain** for the same count (#8; also the shape of the reference's table) | `s8_ternchain`, `s9_ternchain` | load, 0 unsupported | accepted by `sv_structure?` (one site; the chain is a tree of `if`/`?:`) | in the fragment today |
| **`$clog2` for widths and counters**, localparams, casts `CW'(W)` (#1, #9, #11) | `s4_clog2` | loads; the cast is Unsupported (`ConversionExpression:Explicit`) | `localparam CW: $clog2 is outside the v1 fragment` | register `tl-sv-structure-fragment`; the reference needs none (fixed size) |
| **packages and packed structs for the format** (#2, #3: `fp_pkg::fp16_t`, `a.e`, `'1`) | `s5_pkg_struct` | loads, 0 unsupported | a member select is a LEGACY part select (gap G1), refused; `== '1` is a fill inside an expression, refused | follows the part-select fix; independently, the scorer's Yosys 0.53 cannot read `import` (survey, y-series), so a package is usable only as `pkg::name` |
| **Verilog-2001 `wire` / `reg`, non-ANSI ports** (#5, #7, #10) | READ (survey v01 to v14) | `wire` declarations of any form are refused (`assign target 'x' undeclared`); `reg` and `logic` load | — | write `logic` |
| **replication `{N{1'b0}}`** and **indexed part select `[DIVF -: 11]`** (#3, #8) | `s10_repl` | load | "replication (outside the v1 fragment)"; `x[…-:…]` "indexed part select … (outside the v1 fragment)" (READ, `CombView.lean` `partAcc?`) | none planned |
| **`unique case`** in combinational blocks (#1, #2, #4) | `s12_unique` | the SOURCE GATE refuses `unique`/`priority` | — | policy (source gate) |
| **signed arithmetic** `$signed`, `>>>`, `signed` ports (#1, #8) | READ (register `dc-signed`) | the extractor refuses signed symbolic ports and sign-extending conversions | — | none planned |
| **the `/` and `%` operators** (#5, #8) | — | fine | — | BANNED by this task's banlist (the point of the task); fine for other tasks |
| **one `always_comb` priority table** over a few wires (#3's `norm`, the reference's last block) | `b9_table` | loads | structure and equations accepted | in the fragment today |

## 8. Decisions asked of the lead

1. **Which reference?** `t4` (flat, 1929.778 GE / 299) replaces the draft as `reference/fdiv16.sv` at G2, and the draft
   (2089.081 / 298) moves to `tests/fdiv16/baselines/` (the existing practice for the layout variants). The ruling
   allows the rewrite; the cost is readability (13 explicit steps instead of a `generate for`) and it is what the
   tactics can take today (G5).
2. **Gap routing** (section 3): G1 (legacy part select) to the gate-3 agent or a new small gate (est. 1 to 2 agent-days;
   it would let the reference be written as people write it), a diagnosis of G2, a sharper message for G3/G4, a
   `rank := depth` option (G6). None is needed for G1 (math) or G2 (design) of this work package.
3. **Where the generic math lives.** M3a to M3f are stated about integers and `BitVec` quantities, not about this
   reference's signal names; I propose they ship in the `tasks` library next to `Cert16.lean` (register the modules in
   `tasks.lean`; a `Solution.lean` may import `tasks.*`, README "Rules"), so that they also serve the parametric `fdiv-param`
   task, and that the reference-specific `F`, its bridges and the glue stay in `Solution.lean`. Your call; it changes
   what every player gets for free.
4. **Stale text to correct when the task goes `ready`** (G2, nothing edited now): `task.json` `allow_bv_decide: true` and
   the matching bullet of `README.md` ("The proof is symbolic"), `README.md` "What is proved" / "Not proved", the
   `time_limit_s: 3600` placeholder, `tests/expected.json` (`stage: comparator` for the reference).
5. **Heartbeats.** `sv_equations` on `t4` needs `set_option maxHeartbeats` between 200,000 and 600,000 (measured only at
   600,000 and 2,000,000), as `sbox_bp`'s `solution` carries its own option; fine in a submission, to be measured at G2.
6. **PROVING.md**: the localparam-declaration workaround (G1) and "name every comparison" are worth a paragraph each
   (the survey found both independently).

## 9. Files

* `svgolf/design/fdiv-param/H2-NOTE.md` (this file); `svgolf/tasks/fdiv16/PROOF_PLAN.md` (stale `bv_decide` text fixed, Design2 layer marked superseded, M3 re-decomposed).
* `svgolf/design/fdiv-param/h2/`:
  * the reference rewritten: `fdiv16_t0.sv` … `fdiv16_t4.sv` (`t4` is the flat one: the recommended reference);
  * probe designs: `b1_fields.sv` … `b9_table.sv` (the reference cut into blocks, as written `bN_*` and rewritten `bNb_*`/`bNc_*`),
    `m1`…`m9` (micro designs: 2-D literal vs localparam dims, part selects, concat/shift arms, reductions), `g1`…`g6` (2-D row/cell access in loops),
    `s1`…`s12` and `s1b` (styles of real code);
  * Lean: `Fdef.lean` (`F`, the transcription of `t0`, checked against `fdiv16` by `#guard`), `NormDivExp.lean` (M3a, M3b, M3c), `RoundCore.lean` (M3d);
  * Python: `datapath_model.py` (model of the datapath + every invariant of section 5 + `cert16`, 290k pairs), `shifter_eq.py` (exhaustive), `mkrank.py` (rank table from the source), `gen_probe.py` (probe-file generator);
* outside the repo (scratchpad `wph2/`): `probe/*.lean` and `probe/*.out` (every raw tactic output quoted here), `LOG.md`, `realworld/` (the downloaded real implementations; untrusted, never executed).


# fdivp radix-4 SRT divider: gates S0 to S5 (source, adaptation, validation, score, fragment, library, proof; S5 holds), 2026-11-04

The design is `tests/fdivp/baselines/fdivp_srt.sv`. Gate S0 validated the file at sha256
`39cdd266aaa02015d60cc403d58227da72f3da3d1c3fcad236114577174fb8b4` (ed147f1a). Gate S1 (section 7) made two wiring-only
edits and re-ran every run of sections 4.3 to 5 on the edited file, sha256
`f7b6aaa148f996f8bda3d1bfccddd93a782a56586c77c808e313b9a6eeeceac4`. Those sections now report the S1 runs (with S0's
numbers beside them where they differ), and the `srt_*` records in this directory are S1's. Sections 1, 2, 4.1 and 4.2
are S0's; they do not read the file (the survey, and the Python model of the core).

The design is D3 (`tasks/fdivp/reference/fdivp.sv`) with the P + 2 restoring steps replaced by an unrolled radix-4 SRT
core adapted from CORE-V Wally. Everything outside the core is D3 VERBATIM (the same text as the Newton reference), and
the core meets the same interface: `qq = floor(2^(P+1) ma / mb)`, `rnz = (2^(P+1) ma mod mb != 0)`. The provenance and
the list of changes with their reasons are in the file's header. Unproved; no Lean was run for S0 or S1. Gate S2
(section 8) ran the tactics on the S1 file, and gate S3 (section 9) built the core's mathematics as a library module.

MEASURED = run and recorded here; JUDGED = reasoning, not run.

## 1. Real-world radix-4 SRT dividers (shortlist)

| design | URL, commit | license | radix, digits | selection (QDS) | partial remainder | conversion | iterative / unrolled | fit to fdivp |
|---|---|---|---|---|---|---|---|---|
| **CORE-V Wally `fdivsqrt` (chosen)** | https://github.com/openhwgroup/cvw `c1e386b5d1155e92e21593a7986999274f086729`, `src/fpu/fdivsqrt/` | Apache-2.0 WITH SHL-2.1 (permissive) | 4 (or 2), {-2..2} | 7 top bits of the assimilated carry-save remainder (an 8-bit add, LSB dropped) against 4 constants chosen by 3 divisor bits (`fdivsqrtuslc4cmp`; a 1024-entry table form `fdivsqrtuslc4`) | carry-save (WS, WC), one `csa` row per digit | on the fly (U, UM = U - 1, positional `K` masks) | DIVCOPIES stages unrolled per clock in a generate loop, iterated over cycles | best: the same contract as fdivp's core (the sign of WS + WC selects UM, WS + WC != 0 is the sticky), parametric in its config, textbook (Harris et al., "RISC-V System-on-Chip Design") |
| HYF `fpdiv_scalar_r64` | https://github.com/hyf6661669/verilog_library `0d1afe6e2a005a89efa67bf24e02a010817c0331` (mirrored in OpenXiangShan/XS-Verilog-Library) | BSD-3-Clause | 64 per cycle = 3 overlapped radix-4 stages, {-2..2} one-hot | `r4_qds_v0/v1/v2` (6-7 bits), speculative QDS/CSA across the 3 stages | carry-save | on the fly (`quo_iter`, `quo_m1_iter`) | iterative | high-performance but the speculation and the fixed fp16/32/64 widths would all have to be undone |
| T-Head OpenE906 FDSU | https://github.com/openhwgroup/cvfpu `7093289d00ec842c94ca973e2d5ba9301fb11363`, `vendor/opene906/E906_RTL_FACTORY/gen_rtl/fdsu/rtl/pa_fdsu_srt_single.v` (also OpenC910 `ct_vfdsu_srt*`, radix 16 = 2 x 4) | Apache-2.0 | 4, {-2..2} | two bound comparisons of the 8 top remainder bits against divisor-dependent bounds | NON-redundant (a full adder per digit) | on the fly (`total_qt_rt_30`, `..._minus_30`) | iterative, binary32 only | medium: not carry-save, fixed width, Verilog-2001 netlist style |
| andmiele `Radix4SRTDivider` | https://github.com/andmiele/SystemVerilogALUandFPUmodules `07a5310b8801dc634755e79e9dcaf09ecf5a352b`, `divider/` | Apache-2.0 | 4, {-2..2} | PLA (`qSelPLAPos`, `Radix4PLA0/1`) on 5 bits of the remainder and 4 of the divisor | carry-save (`csAddSubGen`) | quotient and correction registers, signed | iterative FSM, integer, generic N | low-medium: integer with signed control, FSM |

Not shortlisted: XiangShan `fudian` FDIV (Chisel, SRT-16 = 2 x SRT-4; Mulan PSL v2), Berkeley HardFloat
`divSqrtRecFN_small` (Chisel, radix 2), CVFPU `fpnew_divsqrt_multi` / PULP `fpu_div_sqrt_mvp` (radix 2), Ventium
`fx_srt_div` (radix-4 carry-save, no license or source repository stated on its page).

## 2. The unmodified originals through the svGolf pipeline (findings for the ls-sv lane) — MEASURED

Wally, the files `fdivsqrt{stage4,uslc4cmp,uslc4,uotfc4,fgen4,iter,postproc}.sv`, `csa.sv`, `aplusbeq0.sv`, `mux.sv`,
`flopen.sv`, `cvw.sv`, byte-identical to the commit above:

* source gate (`score/srcgate.py`, per file): 9 of 12 pass. Refused: `fdivsqrtstage4.sv:61` the `default: Dsel = 'x`
  arm of the digit mux (x literal); `fdivsqrtuslc4.sv:42-43` procedural `for` loops whose iterators `a`, `w` are
  declared outside the header (the svGolf stopgap rule); `cvw.sv` its `` `ifndef ``/`` `define ``/`` `endif `` guard.
* extractor (`extractors/sv/extract.py --top`): `fdivsqrtuslc4cmp`, `csa`, `aplusbeq0` as tops: 0 Unsupported (the
  `$signed` comparisons extract). `fdivsqrtuslc4` (the table form: a 1024-entry array filled by a nested procedural
  `for` in `always_comb`) did not finish in 300 s. `fdivsqrtiter` (and every module with the struct parameter
  `cvw_t P`, which has no default) is not a top at all: `error: --top fdivsqrtiter: no such module among top instances
  ()`. Through a probe wrapper that instantiates `fdivsqrtiter` at the rv32gc configuration (`` `include `` of
  `config.vh` and `parameter-defs.vh`; the wrapper is not Wally's): 11 Unsupported nodes — 5 `Syntax:ScopedName`
  (`P.DIVb` member accesses of the struct parameter in the port widths), 1 `AssignmentPattern:element` (the
  configuration's struct literal `'{XLEN: ..., ...}`), 4 `ConversionExpression:Explicit` (`(32)'(Q_SUPPORTED)` and
  the like in the configuration), 1 `ModuleDefinition:elaboration` (the `fdivsqrtiter` instance).
* banlist (`score/banlist.py`, `/ % **`): `fdivsqrtuslc4cmp` passes (front and backstop).
* proof fragment (JUDGED from svgolf/PROVING.md section 4, not run): the `$signed` comparisons, the signal-indexed
  constant arrays `mks2[A]` etc., the instances, the flops and the package import are outside it.

andmiele, `Radix4SRTDivider.sv` with its 8 dependencies from `divider/`:

* source gate: 8 of 9 pass; refused: `encoder.sv:30` `for (int unsigned i ...)` (only `int`/`integer` iterators).
* extractor (probe points N=8, N=32): 11 Unsupported in the envelope, 22 in the probes: the `typedef enum` state
  variable (`VariableSymbol:signed`), 3 size casts `N'(...)` (`ConversionExpression:Explicit`), 6 instances with a
  width-changing parameter override `#(N + 3)` of an untyped parameter (`InstanceSymbol:override-untyped-width`), the
  `for (int unsigned ...)` loop (`ForLoopStatement`). 0 frontend errors.
* banlist: fails (on the source-gate finding above).

Raw logs: in the S0 scratch area (not committed); sha256 of every original file is listed there.

## 3. The adaptation

See the header of `fdivp_srt.sv` (10 numbered changes with reasons). In short: Wally's per-cycle stage loop unrolled to
N = (P + 2) / 2 + 1 stages; division only; the struct parameter replaced by integer localparams of W, P (H, XS, N, RW);
instances inlined; `$signed` comparisons made unsigned by flipping the estimate's sign bit and adding 64 to Wally's
constants (unchanged otherwise); the constant arrays made four 3-level `?:` trees on the 3 divisor bits (four
`always_comb case` tables at S0); the dividend's parity pre-shift a part-select of a zero-padded copy (a shift by the
localparam XS at S0); the `'x` mux made a priority `?:` chain; the negative multiples padded so the residual's 3 low
bits stay constant zero; the positional on-the-fly conversion written in shift-append form (the same five cases); the
final correction and sticky as in `fdivsqrtpostproc`. Unsigned vectors only; every index and bound affine in W, P, the
genvar and the localparams.

## 4. Validation

### 4.1 The selection table, exactly (`srt_model.py table`) — MEASURED

For each divisor interval (3 bits after the leading one) and each Q4.3 estimate (128 values), with the carry-save
truncation error in [0, 3/16) and the remainder bound |w| <= 8/3 d, every vertex of the (closed) feasible polygon is
checked in exact rationals: the selected digit keeps |w - q d| <= 2/3 d, and the 8-bit estimate never wraps.
**547 feasible cells, 0 bad.** The check is not vacuous (`srt_model.py perturb`): changing one constant
(mks2[0] 12 -> 11, mks2[7] 23 -> 25, mks1[0] 4 -> 2, mks0[3] -6 -> -3, mksm1[0] -13 -> -12, mksm1[7] -23 -> -26) gives
1-2 bad cells each; mks1[5] 8 -> 6, which Wally's own comment asks about, is also valid (0 bad).
This is the P-independent part of the correctness argument: the core never looks below the window except through
the truncation error bound.

### 4.2 Bit-exact model of the core against exact division (`srt_model.py`) — MEASURED

| run | pairs | mismatches |
|---|---|---|
| every (ma, mb), P = 2..12 | 5,592,404 | 0 |
| uniform, P = 2..64, 20,000 per P | 1,260,000 | 0 |
| near divisor-interval edges and extreme quotients, P = 2..64, 20,000 per P | 1,260,000 | 0 |
| uniform, P = 2..300, 300 per P | 89,700 | 0 |

### 4.3 Verilator against `oracle.h` (the harness in `tests/fdivp/validate/`, unchanged) — MEASURED

S1's runs, on the S1 file; S0's on its file gave the same counts (0 everywhere).

| run | formats | pairs | mismatches | record |
|---|---|---|---|---|
| every pair, all W + P <= 14 | 66 | 3,817,748,736 | 0 (each format 0) | `srt_exhaustive_k14.jsonl` |
| every pair at (5, 11), (8, 8), (2, 14) | 3 | 3 x 4,294,967,296 | 0 | `srt_exhaustive_2p32.jsonl` |
| corner-rich vectors (gen_vec, seed 7; exact-integer oracle checked against `Fraction` on 2000 each) and the testbench's sampled mode (seed 11) | 14 | 2,800,000 vectors + 6,053,600 sampled pairs (the `Fraction` oracle agreed on 2000 x 14) | 0 | `srt_vectors_14_formats.jsonl` |
| the scored gate netlists, every pair at (2,2), (5,11), (8,8) | 3 | 8,589,934,848 | 0 | section 5 |

The 14 vector formats are Newton's: (8,24) (11,53) (2,62) (20,12) (2,30) (6,30) (15,48) (3,60) (12,20) (16,16) (4,20)
(10,40) (5,11) (8,8).

### 4.4 Deliberate mutants (`srt_mutants.txt`) — MEASURED

Each mutant of `fdivp_srt.sv`, every pair at W = 2, P = 2..12 (357,913,856 pairs): every one is caught. At S1 the ten
were re-derived on the edited text (the table mutants are now leaves of the `?:` trees, the same entries) and re-run:
every per-P count equals S0's, as it must for the same function with the same change.

| mutant | change | mismatches | first P |
|---|---|---|---|
| `m_qds_t2_d0` | wrong QDS entry: mks2[0] 12 -> 11 (t2's da = 0 leaf 76 -> 75) | 525,728 | 5 |
| `m_qds_t1_d0` | wrong QDS entry: mks1[0] 4 -> 2 (t1's da = 0 leaf 68 -> 66) | 1,139,376 | 5 |
| `m_qds_tm_d7` | wrong QDS entry: mksm1[7] -23 -> -26 (tm's da = 7 leaf 41 -> 38) | 251,364 | 5 |
| `m_no_corr` | final correction missing (`qq = u[N]`) | 18,993,996 | 3 |
| `m_drop_carry` | one carry-save carry dropped (`cy[3]`) | 19,810,756 | 2 |
| `m_no_cin` | the +1 of -q * dv (q > 0) dropped | 93,138,296 | 2 |
| `m_sticky_sign` | sticky from the wrong residual sign (`rnz = ~sign & (rs != 0)`) | 9,387,252 | 3 |
| `m_stages_m1` | one stage fewer (`N = H`) | 182,588,792 | 2 |
| `m_otfc_um` | on-the-fly conversion: UM' for q = 0 taken from U | 82,114,960 | 3 |
| `m_otfc_digit` | on-the-fly conversion: the pair appended for q = -1 is 10, not 11 | 94,439,864 | 2 |

The three wrong table entries are invisible below P = 5 (the bad cells are not reached), so the small formats alone
would not certify the table; section 4.1 does, for every P.

### 4.5 Cheap gates — MEASURED (S1 file; S0's results were the same)

* source gate: passed, no findings.
* banlist (`/ % **`): passed, front check at all 8 probe points and the Yosys backstop at (2,2), (5,11), (8,24)
  (`--task tasks/fdivp`, and `--point` at each probe point).
* extractor (`--top fdiv --probe-points` the task's 8): exit 0, 0 frontend errors, 0 Unsupported in the envelope; in
  the probes only D3's empty `lo` loop at P = 2 (`GenerateFor:no-template`, 2 nodes: (2,2) and (3,2)), exactly as for
  the reference. The envelope has 69 `Assign` sites and no `AlwaysComb` (S0: 65 `Assign` + 4 `AlwaysComb`).
* fourstate: passed at (2,2), (2,3), (3,2), (5,11), (8,8), (8,24), and with `--task tasks/fdivp`.
* proof fragment (JUDGED, `check.py --tactics` needs Lean and was not run): only constructs svgolf/PROVING.md section 4
  lists as accepted — continuous assigns only, `generate for` with the bound `N` (a localparam `(P + 2) / 2 + 1`),
  unsigned packed 1-D/2-D declarations, `+`, `^`, `&`, `|`, `>=`, `?:`, part-selects with affine bounds over the
  localparams and the genvar (`xw[RW+XS:1+XS]`), shifts by literals and D3's shifts by a signal, concatenations of
  accesses and literals, `'0`/`'1` fills.

## 5. Score (pinned flow, `score.py` with the Yosys timeout lifted; sky130 A0' by `ppa.py --netlist-in`) — MEASURED

The current flow, after the merge of svgolf-prep at S1: the GE / depth flow is unchanged (the Yosys version and the
hashes of `canon.ys`, `svgolf.ys`, `ge.json` are `tests/expected.json`'s), and the ranked sky130 A0' columns are
`sky130_a0_v2` (buffering only). Each cell: GE / depth / um^2 / ps. Every sky130 number below is v2, weighed now
(S0's table had v1's): SRT S1 and S0 from their scored netlists, D1, D2, D3 from the N0 record's scored netlists
(their GE / depth are `tests/expected.json`'s; D3 at (5,11) reproduces its v2 golden 9675.5296 / 37872 and its repaired
netlist's sha256 exactly), Newton at (5,11) from its v2 golden (`score/tests/ppa/expected_ppa.json`), its other GE /
depth from `tests/expected.json` (the `qe` version's).

| point | SRT (S1) | SRT (S0) | D3 (reference) | Newton (reference) | D1 | D2 |
|---|---|---|---|---|---|---|
| (2,2) | 96.652 / 19 / 431.66 / 3030 | 96.653 / 19 / 424.16 / 2594 | 102.985 / 18 / 456.69 / 3019 | 115.318 / 21 / - / - | 93.322 / 20 / 405.39 / 3030 | 96.32 / 18 / 422.91 / 2655 |
| (5,11) | **2787.652 / 189 / 12356.85 / 27486** | 2777.994 / 192 / 12310.56 / 28792 | 2166.076 / 289 / 9675.53 / 37872 | 7892.452 / 252 / 33824.94 / 39689 | 1911.446 / 300 / 8575.72 / 34875 | 2314.058 / 295 / 10344.92 / 38193 |
| (8,8) | 1907.436 / 141 / 8423.08 / 22427 | 1886.773 / 139 / 8331.74 / 22292 | 1369.84 / 184 / 6077.08 / 23718 | 4286.665 / 211 / - / - | 1251.195 / 181 / 5604.12 / 24963 | 1498.496 / 179 / 6661.39 / 24445 |
| (8,24) | 10139.803 / 387 / 44719.14 / 64736 | 10230.378 / 386 / 45442.33 / 65795 | 8826.016 / 1261 / 39466.60 / 158865 | not scored | 7450.536 / 1256 / 33545.92 / 146544 | 9813.601 / 1279 / 43517.99 / 151561 |

Every v2 weighing is legal (no cell outside its tables, no net over its capacitance or transition limit); v2 inserted
buffers only at (8,24): SRT S1 5, S0 5, D1 3, D2 10, D3 14. Gate counts (SRT S1): 75, 2012, 1402, 7392 (S0: 77, 1997,
1385, 7339). The scored S1 netlists simulate correctly: every pair at (2,2) (256), (5,11) and (8,8) (4,294,967,296
each), Verilator + Yosys `simcells.v` against `oracle.h`: 0 mismatches.

`&fraig -x` did not stall: the pinned flow took 0.5 s at (2,2), 2.2 s at (5,11), 1.6 s at (8,8), 104.6 s at (8,24)
(S0: 0.5, 2.8, 1.8, 164 s; D3: 0.9, 2.0, 1.5, 10.9 s). No perturbation was needed.

The S1 scores differ from S0's by -0.9% to +1.1% in GE and -3 to +2 in depth; section 7.3 explains why (the same
function, a different expression structure).

Pareto (MEASURED numbers, JUDGED reading): at (5,11), the scoring point, SRT has the lowest depth of the five designs
(189 vs Newton 252, D3 289, D2 295, D1 300) and the lowest sky130 delay (27486 ps vs D1 34875, D3 37872, D2 38193,
Newton 39689) at 1.28x D3's area (um^2; 1.29x in GE): a Pareto point on both boards, and it dominates Newton on both
(2787.652 < 7892.452 GE, 189 < 252; 12356.85 < 33824.94 um^2, 27486 < 39689 ps). At (8,8) likewise (depth 141 vs
179-184, 22427 ps vs 23718-24963; dominates Newton in GE / depth). At (8,24) depth 387 vs 1256-1279 and 64736 ps vs
146544-158865 at 1.13x D3's area (1.15x in GE) (the radix-4 core has (P + 4) / 2 stages where D3 has P + 2, and each
stage's critical path is an 8-bit estimate add, the selection compare and one carry-save row, not a P-bit borrow
chain). At (2,2) D2 dominates it on both boards (96.32 / 18 vs 96.652 / 19; 422.91 um^2 / 2655 ps vs 431.66 / 3030);
S0's (2,2) netlist had the lowest v2 delay there (2594 ps), S1's does not.

## 6. Open items

* `tests/expected.json` does not list `fdivp_srt` yet, so the `layout` step of `tests/run.py` will report
  `baselines/: on disk [...]` until the entry is added (gates S0 and S1 commit only the design and its records, as
  Newton's N0 did); the numbers for the entry are in section 5 (gate S6 registers it).
* The license text: closed at S1 (section 7.4).

## 7. Gate S1: the design edits (2026-11-04)

### 7.1 The merge

svgolf-prep (731a4e3b) was merged into `svgolf-fdivp-srt` first (eb6ee2ea): no conflict, no Lean file, lakefile or
toolchain touched. It brings the buffering-only `sky130_a0_v2`, now the ranked sky130 flow (section 5). `lake build`
of svGolf's default targets afterwards: success, 123 jobs (`lake build --no-build` had found three targets out of date
in this worktree, `LeanModels.Sv.Comb2Base`, `LeanModels.Sv.Param`, `SvGolf.TaskSeq`; they were stale before the merge,
which changed no Lean input).

### 7.2 The two edits (the lead's decisions; wiring only)

1. The four `always_comb case` tables (`t2`, `t1`, `t0`, `tm` by `da`) are four continuous assigns, each a 3-level
   `?:` tree on `da[2]`, `da[1]`, `da[0]` over the same 7-bit literals (8 leaves each, equal leaves kept, so each
   table's proof glue is an 8-way split). A script built the trees from the case tables and checked all 32 leaves
   against them before the edit. Reason: a procedural process takes the design off `CombDesign`, the route the D3 and
   Newton proofs use (PROVING section 13); the plan's option T2.
2. `ws[0] = xv >> XS` (a shift by a parameter amount, which the proof fragment's shift operand reader refuses) is
   `ws[0] = xw[RW+XS:1+XS]` with `xw = {4'b0000, ma, 4'b0000}` (16 ma, RW + 2 bits): the same value ma * 2^(3-XS),
   now a part-select with affine bounds over the localparam XS. `xv` is gone.

The site count is unchanged: 69 (S0: 65 continuous assigns + 4 `always_comb`; S1: 69 continuous assigns). The proof
plan's "70 sites (66 assigns + 4 `always_comb`)" counted the word `assign` in a comment; S2 should expect 69.

### 7.3 Why the scores moved — MEASURED

Every validation is unchanged (section 4: 0 mismatches everywhere; the 2^32 runs at (5,11), (8,8), (2,14) show S0 and
S1 compute the same function there), but the scores moved. Each edit alone, at (5,11) (GE / depth / gates):

| variant | score | canonical RTLIL (`canon.ys` output) |
|---|---|---|
| S0 (case tables, `xv >> XS`) | 2777.994 / 192 / 1997 | 479 cells: 4 `$pmux`, 20 `$eq`, 4 `$logic_not`, 90 `$mux`, ... |
| S0 + edit 1 only (`?:` trees) | 2806.317 / 191 / 2019 | 473 cells: 0 `$pmux`, 0 `$eq`, 0 `$logic_not`, 112 `$mux`, the rest equal |
| S0 + edit 2 only (`xw` window) | 2774.326 / 190 / 1995 | the same 479 cells; only wires differ (at (5,11) XS = 0: a 17-bit `xv` becomes a 19-bit `xw` sliced at [17:1]) |
| S1 (both) | 2787.652 / 189 / 2012 | 473 cells as edit 1 |
| S0 with `xv` renamed (`xw`, `aa`, `zz`) | 2777.994 / 192 / 1997 each | renamed only |

So the score is invariant under renaming (as `canon.ys` intends) but not under these structural changes: edit 1
replaces the `case` lowering (`$pmux` with `$eq` selects) by `$mux` trees, edit 2 only re-wires constant-zero padding,
and ABC maps the two functionally equal circuits differently. The effects do not add (+28.3 and -3.7 GE alone, +9.7
together), so they read as the mapper's sensitivity to its input's structure, not as a cost of either edit (JUDGED).
sky130 v2 at (5,11) moves the same way: 12310.56 -> 12356.85 um^2 (+0.4%), 28792 -> 27486 ps (-4.5%).

### 7.4 The license text

The provenance header now names `LICENSES/Apache-2.0.txt` and `LICENSES/SHL-2.1.txt`, in
`tests/fdivp/baselines/LICENSES/` beside the design (they move with it to `tasks/fdivp/reference/` at S6), as Apache
2.0 section 4(a) asks of a redistributed derivative. `Apache-2.0.txt` is apache.org's
`https://www.apache.org/licenses/LICENSE-2.0.txt` byte for byte (sha256 `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30`).
`SHL-2.1.txt` is the license steward's page `https://solderpad.org/licenses/SHL-2.1/` rendered to plain text by a
script (paragraphs verbatim, no hand transcription). SPDX's license-list-data rendering differs from the steward's in
three places ("Rights owner" for "owner of the Rights", twice, and a final period); the file follows the steward.
Wally's own `LICENSE` is only the notice, not the text.

### 7.5 What S1 re-ran

On the S1 file (sha256 above, checked at the start and the end of the run queue): sections 4.3 (every pair of the 66
formats with W + P <= 14, every pair at (5,11), (8,8), (2,14), the 14 large formats), 4.4 (the 10 mutants re-derived
on the S1 text, each one substitution asserted to occur exactly once; the three table mutants change the same entries,
now tree leaves), 4.5 (source gate, banlist, extractor, fourstate) and 5 (the pinned score and sky130 v2 at the 4
points, the scored netlists simulated). All pass.

## 8. Gate S2: the tactic fragment at symbolic W, P (2026-11-04) — MEASURED

The S1 file staged by `check.py tasks/fdivp tests/fdivp/baselines/fdivp_srt.sv --unproved --no-score
--no-trusted-build --ppa off --stage-dir DIR` (every check that needs no proof passed), then a probe file importing
`Submission.Design` compiled against the stage through the Lean slot: `sv_structure?` on
`CombDesign (design.sem W P) ∧ Acyclic (design.sem W P)` and `sv_equations?` in `solution`'s context (`Goal`, the
structure taken as a hypothesis, `satisfiedAt_of_comb`, the inputs introduced as Newton's proof does).

* `sv_structure?` recognizes every site: 45 plain sites, the family `norm` (4, `i < P - 1`), the family `srt` (19,
  `k < N`, `N = H + 1`, `H = (P + 2) / 2`) and the family `lo` (1): **69 sites** (the plan's 70 counted an `assign`
  in a comment; S1 already said 69). It prints the localparams `H`, `XS`, `N`, `RW` and the rank relation; no refusal.
* `sv_equations?` prints the 69 equations (and their knownness facts) with no refusal. The shapes the glue (S5) will
  read are in `srt_S2_equations.txt` (the 19 equations of `srt` and the 19 plain sites of the core, verbatim). The
  ones that fix the library's statements:
  * `es[k]`: `XF.addBits 8` of the windows `ws[k][P+5:P-2]`, `wc[k][P+5:P-2]` (offsets `rmN (P+6) k (P-2)`);
  * `yb[k]`: `es[k][1 + j] ^^ c j` with `c` the 7-bit constant `1000000`: `XF.val_xor_top`;
  * `g2[k]` .. `gm[k]`: `decide (XF.val yb 7 ≥ XF.val t 7)` (widths `max 7 7`);
  * `mm[k]`: the priority chain as nested `if g = true then .. else ..` per bit;
  * `sm[k]`, `cy[k]`: `ws ^^ wc ^^ mm` and `ws && wc || ws && mm || wc && mm` per bit: `XF.val_csa`;
  * `ws[k+1]`, `wc[k+1]`, `u[k+1]`, `um[k+1]`: concatenations (`{sm[RW-3:0], 00}`, `{cy[RW-4:3], g1, 00000}`,
    `{us, uq1, uq0}`, `{ums, um1, um0}`); `us`/`ums`: `if g0/g1 = true then u else um` on the low `P` bits;
  * `ws[0]`: `xw[(2 * ((P + 2) / 2) - P).toNat + j]` (the affine part select, offset `XS + 1`); `t2` .. `tm`: the
    3-level trees `if da[2] = true then ..` over 7-bit constants; `qq`: `if rs[RW-1] = true then um[N] else u[N]`;
    `rnz`: `XF.any (P + 6) rs`.

Gate S2 holds.

## 9. Gate S3: the mathematics, `LeanModels/Sv/Lib/Srt.lean` (2026-11-04) — MEASURED

The plan's (a) to (h) as a prebuilt, Mathlib-free library module (512 lines, imported by `LeanModels/Sv/Lib.lean`),
in units of `U = 2^(P-2)` (`2^RW = 256·U`, `dv = 8·mb`), plus two bit-level lemmas in `Lib/XFVal.lean`:

| plan | lemma | statement |
|---|---|---|
| (a) | `srt_tbl` | for every `da < 8`: the constants are a thermometer, and for every `yb < 128` the cell is safe for the digit `srtQ da yb` it selects (`srtCell`: `(3q-2)·d ≤ 6y` and `3(2y+3) ≤ (3q+2)·d` at both divisor endpoints `d ∈ {16+2da, 18+2da}`, `y = yb - 64`; the sides at `q = ±2` are the invariant). ONE `decide +kernel`, 1,024 cells |
| (b) | `srt_est` | `ws, wc < 256U`, `256U ∣ ws + wc - R`, `|3R| < 256U`, `es`, `yb` as the hardware reads them ⇒ `2(yb-64)·U ≤ R < (2(yb-64)+3)·U` |
| (c) | `srt_qds` | the divisor in its cell, (b)'s bracket and `|3R| ≤ 8dv` ⇒ `|3·4(R - q·dv)| ≤ 8dv` |
| (d) | `srt_mm`, `srt_csa` | the priority chain plus the carry-in `8·g1` is `-q·dv` mod `256U`; `sm + 2cy = ws + wc + mm`, `cy ≡ 0 (mod 8)` ⇒ `ws' + wc' ≡ 4(ws + wc + mm + 8g)` |
| (e) | `srt_otf` (`srt_append`) | `u ≡ Q`, `um ≡ Q - 1 (mod 4K)` ⇒ the five appends give `u' ≡ 4Q + q`, `um' ≡ 4Q + q - 1` |
| (f) | `srt_init`, `srt_r0` | the start (`R = r0`, `Q = 0`, `um = 16U - 1`); `16·ma / 2^(1+XS) mod 2^(P+6) = ma·2^(3-XS)` |
| (g) | `SrtInv`, `srt_step`, `srt_core` | the invariant (`ws, wc < 256U`; `R`, `Q` with `256U ∣ ws + wc - R`, `|3R| ≤ 64mb`, `4^k·r0 = R + 32mb·Q`, `u ≡ Q`, `um ≡ Q - 1 (mod 16U)`), one stage, `N` stages (relational, over sequences) |
| (h) | `srt_final`, `srt_rest` | the two's-complement decode of `rs = (ws + wc) mod 256U` gives `rs[RW-1] ? um : u = ⌊8U·ma / mb⌋` and `rs ≠ 0 ↔ 8U·ma mod mb ≠ 0`; `srt_rest` states it at the hardware's widths (`2^(P-2)` .. `2^(P+6)`) against `restQuo mb ma (P+2)` / `restRem`, for `2N = P + 3 + XS`, `XS ≤ 1` |
| XFVal | `val_csa`, `val_xor_top` | `val(f ^^ g ^^ h) + 2·val(f && g ‖ f && h ‖ g && h) = val f + val g + val h` (the printed shape); the XOR with a constant of value `2^n` at `n + 1` bits is `+ 2^n mod 2^(n+1)` |

`srt_rest`'s hypotheses are the Nat values the glue (S5) will derive from the printed equations of section 8, one per
family equation and `∀ k < N`, so `core` becomes one application. Measured (through the Lean slot):
`lake build LeanModels.Sv.Lib` green (21 jobs; `Srt` 4.6 s, `XFVal` 0.9 s); every declaration elaborates under the
default `maxHeartbeats` 200000 (no option is set in either file), the table included; `#print axioms`: `propext`,
`Classical.choice`, `Quot.sound` at most (`srt_tbl`: `propext` only; no `Lean.ofReduceBool`); no `sorry`, `admit`,
`native_decide` or `bv_decide`. Gate S3 holds, under both stop lines (700 lines, 1M heartbeats).

## 10. Gate S4: the structure (2026-11-04) — MEASURED

svgolf-prep (544d2d44) merged first (ec6c2f53, clean; `lake build` of svgolf's default targets green, 124 jobs). The
design moved to `tasks/fdivp/reference/fdivp_srt.sv` with `LICENSES/` beside it (byte-identical, sha256 `f7b6aaa1…ceac4`;
its header's `LICENSES/…` paths are relative, so they still hold). `fdiv_struct` in `reference/fdivp_srt.lean`:
`sv_structure` with a `rippleRank` (plain sites by depth, `norm` at `2 + i`, `srt` at `P + 5 + 19·i + p`, the sites
after the core from `11·P + 50`), then `intros; sv_rowmajor; omega`. One fact had to be added: the stage bound reaches
the rank goals as `(↑P + 2).tdiv 2` (SV's integer `/`), which `omega` does not read; `htd : (↑P + 2).tdiv 2 = (↑P + 2) / 2`
(`Int.tdiv_eq_ediv_of_nonneg`) in the context fixes the four goals it broke. **670 thousand heartbeats** (`Elab.async
false`, a counter around the declaration; Newton 315), limit set 900 thousand. A balanced `if` tree for the plain ranks
(depth 5 instead of up to 25) measured 686 thousand: the rank's evaluation is not the cost. Gate S4 holds.

## 11. Gate S5: glue, core, chain and solution (2026-11-04) — MEASURED; STOP on the stage time

`reference/fdivp_srt.lean` (5,556 lines; committed 45c8a081): D3's 16 sections verbatim (`shared_sections.py` now checks
both copies against D3, and any section two copies share), `SrG1` (19 glue lemmas, one per printed shape, and `core`:
one application of `srt_rest`, the 32 table leaves and the other constants checked by `decide`), `SrG2` (`g_inc_rnz`,
`fin_ops`, `chain` over the 69 equations, `DpG5`'s body with the core block replaced) and the Submission section
(Newton's, with the 4-conjunct coverage alternative the carry-save row `cy` needs). The chain's hypotheses were
generated from the `sv_equations?` printout (`↑P` → `(f.p : Int)`, the literal vectors as `({ bits := … } : LVec)`);
the 32 equations it shares with Newton came out character-identical to Newton's chain (renumbered).

Heartbeats (thousands, sequential): `core` 38, `chain` 90 (the S5 stop line is 8,000), `fdiv_struct` 670, `solution`
959, of which `sv_equations` alone 749 (119 goals after it; Newton's whole `solution` is 536). `#print axioms solution`:
`propext`, `Classical.choice`, `Quot.sound`.

`check.py tasks/fdivp tasks/fdivp/reference/fdivp_srt.sv tasks/fdivp/reference/fdivp_srt.lean` (fresh `--stage-dir`
each, one at a time, each run taking the Lean slot, `LEAN_NUM_THREADS=2`, nice 19, light postsynth, no liberty in the
worktree so no sky130 figure):

| run | load average (start, end) | verdict | `solution` stage |
|---|---|---|---|
| 1 | about 10 to 12 (12.0 at the end) | **accepted** (leanchecker 45.6 s, comparator 31.8 s) | 92.42 s |
| 2 | 13.7, 12.7 | timeout | 120.33 s (`SVGOLF_TIMEOUT after 120s`) |
| 3 | 11.7, 16.9 | timeout | 120.78 s |

The third planned run was stopped. The stage is over 90 s in every run and over the 120 s ceiling in two: **STOP**
(the plan's stop line). The proof itself is complete and accepted (run 1 differs from the committed file only in the
header's doc comment).

JUDGED, for the lead: the cost is the two framework tactics on 69 sites (1.42 million of the SRT-specific 1.76 million
heartbeats; Newton's structure and whole solution are 0.85 million together, on 46 sites), not the glue. Options:
1. Re-measure on a quieter machine: Newton's 45 s was taken at load 5 to 6, these at 10 to 17 with other agents'
   Lean and Python jobs running.
2. Fewer sites, wiring only (S1-style revalidation and rescoring): inline `mbn` into `nd1`/`nd2`, read `dv[P+1]`,
   `dv[P]`, `dv[P-1]` in the tables instead of `da`, and fold `uq1`, `uq0`, `um1`, `um0`, `us`, `ums` into the
   concatenations of `u[k+1]`, `um[k+1]`: 69 → 61 sites, an estimated 10 to 20 percent of the tactic cost.
3. Layout: put `fdiv_struct` before the shared sections so that it overlaps them on the second thread (only helps if
   the thread pool idles; not measured).
4. ls-sv: the rank and coverage obligations are the known costs (PROVING.md, "What still costs").

## 12. Gate S5, round 2: the stage time (2026-11-04, evening) — MEASURED; S5 HOLDS

Nothing in the proof changed: every run below is `reference/fdivp_srt.lean` as committed in 45c8a081 (sha256
`fe7640da…`), against the design of section 10 (`f7b6aaa1…ceac4`). Round 1's three runs (section 11) were taken at
load 10 to 17; this round measured what the stage time depends on, then timed three runs on a quiet machine.

**The stage time follows the machine's load.** Calibration: the Newton reference, 45 s at load 5 to 6
(`score/time_limits.json`), run through `check.py --time-limit 600` at 16:38 (load 25 rising to 37, peak 58) did not
finish its `solution` stage in 600 s. The SRT solution compile alone (the stage's `lean -o`, outside the sandbox, the
slot's `LEAN_NUM_THREADS=2` and nice 19): 216.9 s wall, 226.6 s user, at load 12 to 17; 75.4 s wall, 162.5 s user,
at load 4.6 to 5.6 (the instrumented copy below, whose counters cost nothing measurable). The CPU time of the same work
rises with the load too (226.6 against 162.5 s): niced threads share and land on the slower cores.

**Where the time goes.** Heartbeats do not depend on the load; counters (`IO.getNumHeartbeats` around each step) in
a copy of the file:

| step | M heartbeats | s (load 5) |
|---|---|---|
| `fdiv_struct`: `sv_structure` | 557 | 30.4 |
| `fdiv_struct`: the rank goals, `all_goals (intros; sv_rowmajor; omega)` | 49 | 2.6 |
| `solution`: `sv_equations` | 752 | 38.3 |
| `solution`: the 116 side goals | 104 | 5.3 |

Of the side goals' 104 M, 91 M are 7 coverage goals that reach the conjunction-splitting alternatives after five
failing ones (the `norm` family's two 2-D goals, `cover_37` and `cover_38`, 28.5 M each); the chain's application
is 0.04 M (round 1's probe). The profiler (`-Dprofiler=true`, load 12 to 21): import 6.5 s, kernel 63.5 s summed over
the threads, `.olean` serialization 11.5 s at the end (the olean is 57 MB).

**Layout (round 1's option 3): not adopted.** JUDGED from the toolchain's source (`Lean/AddDecl.lean`,
`Environment.addConstAsync`): every kernel check is chained on the previous declaration's (`Environment.checked`),
in file order, and the task pool is first-in first-out, so moving `fdiv_struct` and the body of `solution` ahead of
the shared sections puts the shared sections' kernel checks (about 40 s of the 63.5) behind the two largest proofs,
at the end. A variant that moves only the chain's application out of `solution` (`ChainOut` stated in `W P`,
`solution_of (hC : ChainOut)`) compiled and buys nothing (0.04 M heartbeats). Round 1's option 2 (fewer sites,
wiring only) was not needed.

**The three cold runs.** `check.py tasks/fdivp tasks/fdivp/reference/fdivp_srt.sv tasks/fdivp/reference/fdivp_srt.lean`,
fresh `--stage-dir` each, one at a time, each taking the Lean slot itself (`LEAN_NUM_THREADS=2`, nice 19, light
postsynth, no liberty in the worktree so no sky130 figure). A run was started only if the 1-minute load was below 8
when it took the slot (none had to give the slot back):

| run | taken | load average (start, end) | verdict | `solution` | leanchecker | comparator |
|---|---|---|---|---|---|---|
| 1 | 19:44 | 5.73, 6.11 | **accepted** | 79.10 s | 43.99 s | 31.61 s |
| 2 | 20:38 | 7.01, 7.00 | **accepted** | 80.80 s | 43.44 s | 33.41 s |
| 3 | 21:05 | 7.72, 7.19 | **accepted** | 83.59 s | 43.41 s | 31.85 s |

**After the merge of svgolf-prep.** The runs above are on ec6c2f53's tree (svgolf-prep 544d2d44). svgolf-prep was then
merged three times, as it moved (275ab0c4: 685949a5, github/master 80aae3bf with ls-sv's replication, SVA and
active-high reset changes; 8a118606: 8be44458, sky130_a0_v3; f6dc183c: 88c63e98). At 685949a5 and 8be44458
`lake build` of svgolf fails in `SvGolf.TaskSeq` (`Missing cases: (Process2.alwaysFFR _ _ _ true)`: ls-sv 3f5d7893 gave
`alwaysFFR` a fourth field), and since `check.py` builds `SvGolf` every task's check fails there; 88c63e98 fixes it and
the build is green (132 jobs). The same runs on f6dc183c (the proof file unchanged):

| run | taken | load average (start, end) | verdict | `solution` | leanchecker | comparator |
|---|---|---|---|---|---|---|
| 1 | 22:09 | 7.13, 6.31 | **accepted** | 77.33 s | 44.26 s | 30.30 s |
| 2 | 22:51 | 5.67, 5.51 | **accepted** | 78.51 s | 44.95 s | 31.67 s |
| 3 | 00:14 | 5.76, 10.78 | **accepted** | 93.96 s | 54.01 s | 34.15 s |
| 4 | 00:26 | 5.39, 7.21 | **accepted** | 79.31 s | 50.49 s | 32.37 s |

(Four attempts in between gave the slot back, at load 11.9, 9.5, 9.1 and 14.0.) Run 3 is over 90 s: the load rose
from 5.8 to 10.8 while it ran (its leanchecker, 54 s against 44, shows the same). Run 4 was added after it; all four
are reported.

Gate S5: on the first tree all three runs are under 90 s; on the merged tree three of the four are, and run 3 is
94 s (the load rose during it), under the 120 s ceiling. No run of either tree is over 120 s. `chain` is 90 thousand
heartbeats of its 8 million.
Gate S4 holds (section 10: 670 thousand of 900). Against the other two references (the same procedure): D3 70.3,
64.5, 71.6 s at load 6 to 9.5; Newton 44.6, 45.8, 45.3 s at load 4 to 6.

JUDGED: the margin is the load. 77 to 84 s when the load stays at 5 to 8, 94 s when it rose to 11 during the run, and
92 s and two timeouts at load 10 to 17 in round 1: the stage is about 1.8 times Newton's, the two framework tactics on 69 sites being 1.31 G of the file's heartbeats.
The 120 s ceiling holds on a quiet machine with a 1.4 to 1.5 times margin, not on a loaded one.

## 13. Gate S6: the merge onto svgolf-prep 06f2a700 and the registration (2026-11-05) — MEASURED

**The merge** (39f747eb). svgolf-prep had moved on to the shared library's renames (`docs/sv-changelog.md`, "The shared
proof library, made general"), the shared obligations of `sv_structure` (`SharedObl`, PROVING.md section 11, rule 4)
and the rule of 11/04 that a model of one design's core belongs to that design's proof (`Lib/Newton.lean` became
`fdivp_newton.lean`'s section `NwCore`). Resolved by the same rule: `LeanModels/Sv/Lib/Srt.lean` moved, declarations
unchanged, into `fdivp_srt.lean` as section `SrCore` (namespace `SvGolf.FdivParam`) and is deleted; `val_csa` and
`val_xor_top` stay in `Lib/XFVal.lean` (general facts about `XF.val`, named in `Lib.lean`'s docstring). The proof took
D3's sixteen new shared sections (`shared_sections.py` holds), four renamed XFVal lemmas in `SrG1`/`SrG2`
(`val_window`, `bit_eq_of_val`, `top_bit_succ_iff`, `any_eq_decide_val`) and Newton's new `Submission` shape
(`fdiv_struct` returns `SharedObl`, `sv_equations` takes it). Nothing else changed; `lake build` of svgolf green (132
jobs); `check.py --no-score` accepted it at once (`solution` 69.34 s at load 11.0 falling to 7.3).

**Heartbeats** (the `IO.getNumHeartbeats` probe of section 12, `Elab.async false`): `fdiv_struct` 672 thousand (670
before), `solution` **700 thousand** (959 before: the shared obligations are no longer normalized twice). The limits
stay at 900 thousand and 1.3 million.

**Registration.** `task.json` lists `reference/fdivp_srt.{sv,lean}` third; `tests/expected.json` has its scores at the
four points of D3 (pinned flow, `score.py`): (5,11) 2787.652 GE / depth 189 / 2012 gates, (8,8) 1907.436 / 141,
(2,2) 96.652 / 19, (8,24) 10139.803 / 387 (100 s of flow there). `score/tests/ppa/` (`ppa_validate.py table --only
fdivp_srt --mapped`, the pinned liberty, `sky130_a0_v3`): A0' 12356.8512 um^2, 27592 ps, no buffer; A1' 9850.6976 um^2,
33290 ps. The design gained one header comment (the pointer to its proof): sha256 `06b302b7…`, the canonical text and
every score unchanged. `tests/run.py`'s layout rule "reference/ holds only what task.json lists" now admits
`reference/LICENSES/` when every file in it is named as `LICENSES/<file>` by a listed design and every named file is
there (the lead's decision 3).

**The ten attacks** (`tests/fdivp/attacks/srt_*.sv`, S0's mutants re-applied to the committed design, one substitution
each). Exhaustive Verilator at `(4, 6)`: every one wrong (612 to 792,708 of 2^20 pairs); at nine small formats in
`attacks.txt`. Each through `check.py --no-score` with the SRT proof, one slot acquisition each: **all ten rejected at
`solution`**, each at the application of `Glue.chain` to the printed equation of the changed site (stage 62.5 to
66.9 s): `eq_t2_plain_20`, `eq_t1_plain_21`, `eq_tm_plain_23` (the three table constants), `eq_qq_plain_29`
(`no_corr`), `eq_wc_srt_10` (`drop_carry`, `no_cin`), `eq_rnz_plain_30` (`sticky_sign`), `eq_rs_plain_28`
(`stages_m1`), `eq_ums_srt_16` (`otfc_um`), `eq_uq0_srt_12` (`otfc_digit`). Cited in the refusal register
(`gen_sv_refusals.py --check` ok).

**Three cold runs** of the registered proof (sha256 `4dfa8c47…`), the procedure of section 12 with `--no-score`, each
started only at a 1-minute load below 8:

| run | taken | load average (start, end) | verdict | `solution` | leanchecker | comparator |
|---|---|---|---|---|---|---|
| 1 | 01:50 | 7.66, 10.45 | **accepted** | 78.58 s | 49.43 s | 29.31 s |
| 2 | 01:58 | 7.40, 6.68 | **accepted** | 73.19 s | 47.62 s | 27.58 s |
| 3 | 02:01 | 6.68, 7.40 | **accepted** | 69.92 s | 46.06 s | 29.56 s |

Recorded in `score/time_limits.json` (T = 78.6 s, the slowest fdivp reference; the 120 s ceiling holds, the 60 s target
does not, as for D3's 71.6).

**`tests/run.py --only fdivp`, one step per slot acquisition** (the pinned liberty read through `SVGOLF_SKY130_LIB`, so
the references ran `--ppa require`): `layout` 25 checks, 0 failed (after the `LICENSES/` rule above); `negatives` 5, 0;
`references` 26, 0 (`fdivp_srt` accepted with the full post-synthesis check, 4443 vectors, its PPA equal to the golden,
the four scores equal, the advisory oracle agreeing on every vector); `validate` 39, 0 (the quick plan on the SRT
reference, and each attack wrong at (4, 6)). `attacks`, first run: 25 checks, 5 failed, every one of them rejected at
`solution` as wanted but missing its `message_contains`: check.py keeps the last 4000 characters of a compile error,
and with the full type of a selection table (three attacks) or of the carry vector `wc` (two) in the message, the head
`Application type mismatch: The argument …` falls outside them. The ten phrases are now the error's tail,
`` <argument>\n'Submission.solution' depends on axioms`` (the application printed up to the bad argument, then the
axioms with `sorryAx`), checked against the ten recorded results first.
`attacks`, second run: 25 checks, 0 failed (each of the ten SRT attacks rejected at `solution` with its phrase). Not
in this track, and stale on svgolf-prep 06f2a700 already: `tests/site/test_site.py` fails here (4 failures, 6
errors), because `site/config.json` redacts in `docs/sv-refusals.json` a sentence ("… still lists it as a question for
the maintainers.") that occurs 0 times in svgolf-prep's own copy of the register (counted with `git show`; the test was not run
on that branch).

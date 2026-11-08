# Reactive controllers for svGolf: real-world RTL and an admission probe (arbiters, FIFOs)

Date 2026-11-04. Base: worktree `lean-surfaces-reactive`, branch `svgolf-reactive` at `f204d0a6` (svgolf-prep).
Tools: source gate `svgolf/score/srcgate.py --clock <clk>` (the clocked rules, as check.py runs it for seq/tx/stream
kinds); ls-sv extractor `extractors/sv/extract.py --top T --probe-points ...` (python3.12, pyslang 11.0.0);
`svgolf/score/ppa.py --seq` (Yosys 0.53, liberty sha256 ef34f999..., flow `sky130_a0_v2`); Verilator 5.042 and
Icarus for the differential runs. No Lean was run (see section 7).
Labels: MEASURED = run here; JUDGED = my reading or estimate.

Every download sits in its own directory under `reactive/dl-*`; every tool that reads it ran as
`python3.12 -I scripts/run_isolated.py TOOL ...` (the shim puts back only the tool's own directory and the
pyslang user site; downloaded files are arguments only).

## 1. Candidates (pinned)

| id | design | source, commit | licence | what it is |
|---|---|---|---|---|
| A | `cc_rr_arb_tree` (+ `cc_lzc`, `cc_pkg`) | github.com/pulp-platform/common_cells `e73baaec2ca665cd80c3c384e9258e35242b829c` (2026-09-18), `src/` | SHL-0.51 (Apache-2.0 option) | round-robin arbitration TREE with data mux, FairArb (two trailing-zero counters), LockIn, ExtPrio, AxiVldRdy options; the most widely used open RR arbiter (PULP, CVA6, Snitch). Has its own SVA spec |
| B | `cc_fifo` (formerly `fifo_v3`) | same | SHL-0.51 | synchronous FIFO, fall-through option |
| C | `prim_arbiter_tree` | github.com/lowRISC/opentitan `0a6ff6855bd9c6489110df167501e4d5f5c9bdbd`, `hw/ip/prim/rtl/` | Apache-2.0 | round-robin arbiter as a binary tree: request/priority/select/prefix-mask trees, one N-bit mask register; holds its decision under backpressure. Rich SVA + FPV spec |
| D | `prim_arbiter_ppc` (+ `prim_leading_one_ppc`, `prim_util_pkg`) | same | Apache-2.0 | the same arbiter with a parallel-prefix leading-one detector |
| E | `prim_arbiter_fixed` | same | Apache-2.0 | fixed-priority tree (combinational; clock only for assertions) |
| F | `arbiter` (+ `priority_encoder`) | github.com/alexforencich/verilog-axis `48ff7a7e2ef782cf778d47910cf85835c64b1bce`, `rtl/` | MIT | classic Verilog-2001 arbiter (RR or priority, blocking on ack or on request), registered grants |
| G | `bsg_arb_round_robin` (+ `bsg_scan`, `bsg_defines`) | github.com/bespoke-silicon-group/basejump_stl `c9710312482ddd725e14b26eafdcbf3c629dc14c`, `bsg_misc/` | SHL-0.51 | thermometer-code RR arbiter (cyclic scan) |
| H | `prim_fifo_sync` (+ `prim_fifo_sync_cnt`, `prim_flop`) | opentitan, as C | Apache-2.0 | synchronous FIFO |

Not found (JUDGED after one search): a widely used, permissively licensed AHB arbiter. The SYNTCOMP AMBA/genbuf
benchmarks are specifications, not RTL; the open AHB matrices found are LGPL or commercial.

## 2. Admission of the files AS WRITTEN (small instance; MEASURED)

Gate = `srcgate.py FILE --clock <clk>` on the main file. Extractor = one compilation of the file and its
dependencies at the default point plus `--probe-points` at the small instance (A: NumIn=4,DataWidth=4; B: Depth=4,
DataWidth=4; C/D/E: N=4,DW=4; F: PORTS=4,ARB_TYPE_ROUND_ROBIN=1; G: width_p=4; H: Width=4,Depth=4). The extractor
exits 0 on every file but G: it does not stop, it writes `Unsupported` nodes that the Lean load gate refuses, so the
count of distinct `Unsupported` nodes (`scripts/census.py`) is its refusal list.

| id | gate findings | gate kinds | extractor `Unsupported` (distinct) | extractor kinds |
|---|---|---|---|---|
| A | 19 | 19 directive/macro (`include` x2, `FFARNC` x3, `ifndef`/`endif`, `ASSERT`/`ASSUME`/`ASSERT_INIT`) | 47 | casts 26, concurrent assertions 8, generate-block localparam unresolved 6, immediate assertions 3, type parameters 2, package function call 1, `for (int unsigned ...)` 1 |
| B | 11 | 11 directive/macro (`FFARNC`/`FFLARNC` x4, assertions) | 7 | package function calls 2, concurrent assertions 2, cast 1, immediate assertion 1, type parameter 1 |
| C | 31 | 29 directive/macro (include + 28 `ASSERT*`/`ASSUME`/`ifdef FPV_ON`); clocked: async reset (second event + `negedge`), line 190 | 18 | concurrent assertions 15, unpacked port `data_i [N]` 1 (+ its select 1), immediate assertion 1 |
| D | 32 | 29 directive/macro; clocked: async reset (line 89); loop rule: bound `N` is `int unsigned` (line 104) | 24 | concurrent assertions 15, `for` loops 3 (int unsigned), package calls `prim_util_pkg::vbits` 2, unpacked port 1, unpacked variable + its copy 2, immediate assertion 1 |
| E | 15 | 15 directive/macro | 16 | concurrent assertions 13, unpacked port 1 (+ select 1), immediate assertion 1 |
| F | 8 | `resetall` x2; clocked: initializers `reg x = 0` x4, `always @*` / `always @(posedge clk)` x2 | 7 | (all in `priority_encoder`) unpacked wire arrays 2, selects from them 3, assignments into them 2 |
| G | 8 | 8 macro (`BSG_INV_PARAM` x3, `BSG_SAFE_MINUS`, `BSG_ABSTRACT_MODULE` x3, include) | top not found | `--top bsg_arb_round_robin: no such module among top instances`: `BSG_INV_PARAM(width_p)` leaves the parameter WITHOUT a default under slang, so the module is never a top |
| H | 19 | 13 directive/macro; clocked: async reset x3 | 35 | casts 10, concurrent assertions 8, output net ports driven only inside generate branches (`PortSymbol:net-z`) 6, package calls 4, uninstantiated `prim_flop`/`prim_count` in dead branches 3, immediate assertions 2, generate localparam unresolved 1, `#0` delay 1 |

Findings worth keeping (MEASURED unless marked):
* **The one-program problem is real in the wild.** OpenTitan's `prim_assert.sv` selects DIFFERENT macro files under
  `SYNTHESIS`, `YOSYS` and neither (dummy / Yosys / standard). BaseJump's `BSG_INV_PARAM(p)` expands to `p = "inv"`
  under `YOSYS` and to a bare `p` elsewhere. pulp's `FFARNC` register macro emits a `/* synopsys sync_set_reset */`
  pragma comment. The gate refuses all of them at the directive; it is exactly the design (PLAN4, Wally list:
  "preprocess ONCE with a pinned macro set") that would admit them.
* **Macros hide clocked findings.** On A and B the gate sees only the `FFARNC` token; the asynchronous reset inside
  it is reported only for the files that write `always_ff` out (C, D, H). JUDGED: after preprocessing, A/B would add
  the async-reset and pragma-comment findings.
* **Assertions are the bulk** of the extractor's list on every OpenTitan file (13-15 concurrent + 1 immediate).
  They synthesize nothing; they are the reactive SPEC (section 5).
* **Yosys 0.53 refuses something the extractor admits:** an element access of a packed 2-D array declared inside a
  generate block (`logic [M:0][W-1:0] t;` in `if (...) begin : g`) stops `read_verilog -sv` with "Failed to detect
  width of signal access `\g.t'". MEASURED on C's upstream (`idx_tree`, `data_tree` in `gen_normal_case`) and on a
  6-line repro (`yosys-repro/t1.sv` fails, `t2.sv` with the declaration at module scope passes, `t3.sv` fails). A, cc_lzc,
  D/E have the same shape. This is a scorer-side refusal of the most common real arbiter idiom.
* **ls-sv refusals found** (for the refusal register): explicit casts (all forms: `unsigned'(x)`, `T'(x)`,
  `(N)'(x)`); type parameters; package function calls in parameters (`cc_pkg::idx_width`, `prim_util_pkg::vbits`);
  unpacked ports, nets and variables; a generate-block `localparam` used in a declaration's range
  (`Syntax:Identifier:unresolved`, A lines 126/127, cc_lzc 48-50, H 144); output net ports with drivers only in
  generate branches; and two probe-point defects: (i) re-compiling an instance whose parameter is ENUM-typed
  (`cc_lzc #(.Mode(cc_pkg::LZC_TRAILING_ZERO_CNT))`) gives `InvalidExpression` and an invalid compilation at every
  probe point (main envelope clean); (ii) an instance inside a generate branch the point does not elaborate shows as
  `UninstantiatedDefSymbol` in the sidecar (A at FairArb=0 or ExtPrio=1).

## 3. The two adaptations (MEASURED: both pass the gate with `--clock clk_i` and extract with 0 `Unsupported`)

Picked: **C** (fewest changes, self-contained, one module, strongest spec) and **A** (the most widely used; shows the
cost of a typical pulp file). Both are built reproducibly from the pinned upstream text by counted replacements
(`scripts/adapt_C.py`, `scripts/adapt_A.py`; each asserts its pattern occurs exactly once), and the built files are
byte-identical to `adapt/prim_arbiter_tree.sv` and `adapt/cc_rr_arb_tree.sv`. Each file's header carries the
provenance, the upstream notice and the numbered change list. Diffs: `adapt/*.diff`.

**C, `prim_arbiter_tree`** (upstream 291 lines; diff -88 +7, of which ~80 deleted lines are assertions):
1. remove the `include`, `ASSERT_INIT` and the assertions section (gate: directives; extractor: assertions);
2. async active-low `rst_ni` -> synchronous active-high `rst_i` in the one `always_ff` (C1, clocked rules, the seq
   flow has no async-reset flop);
3. unpacked port `input [DW-1:0] data_i [N]` -> packed `input [N-1:0][DW-1:0] data_i` (selects unchanged);
4. `idx_tree`, `data_tree` (packed 2-D) declared at module scope instead of in `gen_normal_case` (Yosys, above).
Kept: module name, parameters (N, DW, EnDataPort), every generate loop (levels x offsets, no unrolling), all
equations, the assertion-only `req_chk_i` port.

**A, `cc_rr_arb_tree` + `cc_lzc`** (two modules in one file, the two `cc_lzc` instances kept; diff -85 +66):
A1 remove includes and `ifndef COMMON_CELLS_ASSERTS_OFF` blocks; A2 the three `FFARNC` registers written out as
`always_ff @(posedge clk_i)` with sync active-high `rst_i`, then `clr_i`, as the macro orders them; A3 type
parameters `data_t`/`idx_t` replaced by their packed defaults; A4 every cast removed (each argued value-preserving
in the header: non-negative genvars below 2^IdxWidth, unsigned comparisons, assignment-context extension/
truncation); A5 `cc_pkg::idx_width(Width)` replaced by its body; A6 `cc_lzc`'s `int unsigned Width` and loop
iterator -> `int` (gate item 7); A7 `NumLevels` hoisted to the parameter list (extractor leaves it unresolved);
A8 the packed 2-D node arrays at module scope (Yosys); A9 the enum parameter `lzc_mode_e Mode` -> `bit Mode` with
the enum's encoding, and `cc_pkg` dropped (the probe defect (i) above; the rest of `cc_pkg` also trips the gate: an
`ifndef SYNTHESIS` and initialized function locals). Kept: every generate branch (ExtPrio, LockIn, FairArb,
AxiVldRdy), the tree, the instances.
Caveat (MEASURED): at probe points with FairArb=0 or ExtPrio=1 the sidecar shows the dead-branch instances as
`UninstantiatedDef` (defect (ii)); a task would pin FairArb=1, ExtPrio=0 or ls-sv fixes (ii). Instances pass the
extractor and the loader expands them, but the svGolf proof route through hierarchy (R-HIER) is still open (JUDGED:
C is the one to build a first task on; A needs R-HIER or an inlined `cc_lzc`).

**Behaviour preserved** (MEASURED, differential simulation of upstream vs adapted, 20,000 random cycles each,
xorshift stimulus, outputs compared every cycle; the upstream's async reset asserted across one edge):
C at N = 1, 2, 3, 4, 5, 8 (DW = 3): 0 mismatches; A at NumIn = 1, 2, 3, 4, 5, 8, plus LockIn=1 (N=4, 5),
FairArb=0 (N=4), AxiVldRdy=1 (N=8): 0 mismatches. The benches are not vacuous: mutants are caught (C: the mask
prefix sum `mask_tree[C1]` without `sel_tree[C0]`: 6,650 mismatches; A: `next_idx = upper_idx`: 7,105;
A: `req_o = 0`: 18,798). A first A bench using Verilator's `$random(seed)` gave degenerate stimulus and missed the
`next_idx` mutant; replaced by xorshift (`sim/tb_Ax.sv`, `sim/tb_Cx.sv`).

## 4. PPA (MEASURED: `ppa.py --seq`, flow sky130_a0_v2; period = register-to-register, ps)

| design | N | data | area um2 | period ps | unit depth | flops | GE (score.py) |
|---|---|---|---|---|---|---|---|
| C prim_arbiter_tree | 4 | EnDataPort=0 (pure arbiter) | 307.8 | 1287 | 8 | 4 | 72.3 |
| C | 4 | DW=1 | 334.1 | 1364 | 8 | 4 | 80.0 |
| C | 4 | DW=8 | 551.8 | 1451 | 8 | 4 | 133.3 |
| C | 8 | EnDataPort=0 | 668.1 | 1779 | 10 | 8 | 159.0 |
| C | 8 | DW=1 | 754.5 | 1936 | 11 | 8 | 179.0 |
| C | 8 | DW=8 | 1253.7 | 2160 | 11 | 8 | 298.0 |
| A cc_rr_arb_tree (FairArb) | 4 | DW=1 | 307.8 | 1381 | 7 | 2 | 70.7 |
| A | 4 | DW=8 | 544.3 | 1381 | 7 | 2 | 119.6 |
| A | 8 | DW=1 | 774.5 | 2463 | 13 | 3 | 176.6 |
| A | 8 | DW=8 | 1336.3 | 2368 | 13 | 3 | 291.6 |

Reading (JUDGED): the two architectures already trade off: A stores log2(N) bits of state (an index), C stores N
(a mask); at N = 8 C is 3% smaller (DW=1) and 21% faster (1936 vs 2463 ps). A good first golf range. The upstream
files are not scoreable as written: C with only changes 1-3 stopped Yosys on the 2-D generate arrays (MEASURED in
the first `ppa.py` run, whose logs the second run overwrote; reproduced by `yosys-repro/t1.sv`); A has the same
construct (JUDGED), and A, B, C, D, H use an asynchronous reset, which the seq flow refuses (JUDGED from
`svgolf_seq.ys`: no async-reset flop cell; F and G reset synchronously, E has no register).

## 5. The reactive spec the upstream files already state (property catalogue)

OpenTitan C/D/E (SVA + `FPV_ON` block) and pulp A (SVA) carry the statement a task would formalize:
* safety, per cycle: `CheckHotOne_A`/`hot_one` ($onehot0 grants: mutual exclusion); `GntImpliesReady_A`/`gnt0`;
  `GntImpliesValid_A`; `GntImpliesReq_A` (no spurious grant); `IndexIsCorrect_A`/`gnt_idx`; `DataFlow_A`
  (data_o = data_i[idx_o]); `ReqAndReadyImplyGrant_A`/`gnt1` and `ReqImpliesValid_A`/`req0`/`req1` (work conserving);
* across cycles: `LockArbDecision_A` (C, D; A only with LockIn=1): under `valid && !ready` the next decision is the
  same; `RoundRobin_A` (D/C: the next index is higher unless no higher request);
* liveness/fairness under a rely: `ReqStaysHighUntilGranted_M` (rely: a request is held until granted),
  `NoStarvation_A` (strong eventually), `Fairness_A` (with n requests stable and ready = 1, each granted exactly once
  in n cycles).
MEASURED on the ADAPTED designs (`sim/tb_props.sv`, 50,000 cycles, requests held until granted, ready 75% / 100%,
N = 2, 3, 4, 5, 8): 0 violations of mutual exclusion, no-spurious-grant, grant=>ready, work conservation and
index/grant agreement for both; worst wait = exactly N-1 grants to others for both (a bounded-waiting clause
"granted within N-1 grants to others" holds and is tight). Decision held under backpressure: C 0 changes at
N = 3, 4, 8; A (LockIn=0) 406 / 54 / 0 changes. So the hold clause separates the two designs: a statement with it
rejects A at LockIn=0 (an attack for free), one without it admits both.
JUDGED for the statement (other tracks): the natural shape is SYNTCOMP's arbiter (G mutual exclusion; G (g_i ->
r_i); G (r_i -> F g_i)) strengthened to a BOUND (N-1 grants, or N cycles with ready held) so it is falsifiable by
a finite trace and not gameable by a design that delays forever; the rely is "requests held until granted".

## 6. Files

In this directory (the scripts, benches and repro only; no third-party code is committed, as in
`../../real-world-sv/`):
* `scripts/adapt_C.py`, `scripts/adapt_A.py` (+ `*_header.txt`): rebuild the two adapted designs from the pinned
  upstream files (fetch them at the commits of section 1), e.g.
  `python3.12 -I scripts/adapt_C.py <opentitan>/hw/ip/prim/rtl/prim_arbiter_tree.sv prim_arbiter_tree.sv` and
  `python3.12 -I scripts/adapt_A.py <common_cells>/src cc_rr_arb_tree.sv`; built sha256s: C `b7700560...4ec1`,
  A `55bfcae6...9d2a`.
* `scripts/run_isolated.py` (runs a trusted tool under `python3.12 -I`), `scripts/census.py` (the `Unsupported`
  list of an envelope).
* `sim/tb_Cx.sv`, `sim/tb_Ax.sv` (upstream vs adapted; the adapted module renamed `*_svg`), `sim/tb_props.sv`
  (the section-5 measurements on the adapted designs).
* `yosys-repro/t1.sv` (fails), `t2.sv` (passes), `t3.sv` (fails): the packed 2-D array in a generate block.
The measurement outputs (gate JSON, envelopes, PPA JSON, logs) stayed in the session scratchpad
(`reactive/`, provenance only).

## 7. Not done / next

* No Lean: the worktree has no build, so `load_sv` (the load gate, the multi-point cross-check of the probe
  sidecar) and `ffOnlyProfileB` were NOT run on the two adapted designs. JUDGED next step at the next Lean slot: one
  file with `load_sv arbT from ".../prim_arbiter_tree.sv" (top := "prim_arbiter_tree") (probes := "N=1;N=4;N=8")`,
  the same for A with FairArb pinned, and `#eval` of `ffOnlyProfileB` at N = 4.
* D (ppc) and F (verilog-axis) were not adapted. JUDGED cost: D like A (instance + package + loops); F needs the
  `priority_encoder` unpacked stage arrays flattened, `always @*` -> `always_comb`, initializers dropped.
* FIFOs (B, H) are the "buffer" controller class: refusal lists recorded above, not adapted.

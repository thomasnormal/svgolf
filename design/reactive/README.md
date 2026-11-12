# Reactive controller tasks for svGolf (design note, 2026-11-04)

**Status (2026-11-05): ADDED, as a draft for the maintainers' review.** Decided 2026-11-05: added. The study's defaults for its open choices were taken (section 9,
each now marked decided), and the kind is wired through the pipeline on branch `svgolf-react`: the
trusted module `SvGolf/TaskReact.lean`, the task `tasks/arbiter` (status `draft`, a statement draft whose
goalpost is the own mask round-robin), `check.py`'s kind `react-family` with a reactive post-synthesis
check, the 17 attacks in `tests/expected.json`, the run.py steps; the site keeps it hidden on this branch
(unranked). The task README (`../../tasks/arbiter/README.md`) is now the record of the decisions (a) to
(k) and the findings F1 to F9; this note keeps the study as it was written, with the corrections below.
Labels: **MEASURED** = run in this session (command or file named); **DERIVED** = a hand argument given
here; **JUDGED** = opinion.

Corrections since the study (2026-11-05): the refutations moved from `tasks/arbiter/Refute.lean` to
`tests/arbiter/negative/Refute.lean`, and `MooreOut`, `KnownAt` and `ReactTask` from the task's
`Spec.lean` to `SvGolf/TaskReact.lean` (with two named slots, `OutDiscipline` and `Known`, for the
planned switch to the shared clocked conjuncts). The reference of section 4 is NOT the OpenTitan tree
yet: ls-sv does not instantiate its generate-local declarations (MEASURED; task README (j), F5), so the
goalpost is `reference/rr_mask.sv`, scored 769.488 µm² × 2826 ps under sky130_a0_v3.

Decided 2026-11-04, on SYNTCOMP's controller specs: of interest, a category of tasks svGolf does not have yet.
This note is the plan for that category.

| file | what |
|---|---|
| [`../../tasks/arbiter/Spec.lean`](../../tasks/arbiter/Spec.lean) | the draft trusted text: `MooreOut`, the kind `ReactTask`, the task `arbiter` |
| [`../../tasks/arbiter/Refute.lean`](../../tasks/arbiter/Refute.lean) | kernel-checked refutations of wrong designs, the tightness of the bound, the window lemma |
| [`../../tasks/arbiter/README.md`](../../tasks/arbiter/README.md) | the task's own notes: decisions (a) to (e), 17 attacks, PPA |
| [`../../tests/arbiter/`](../../tests/arbiter/) | `tb.sv` + `sim.py`: the statement read by simulation; `attacks/`, `designs/` |
| [`rtl-probe/README.md`](rtl-probe/README.md) | the real-world RTL survey: 8 pinned candidates, two adaptations, PPA |

Inputs not committed (session scratch): the SYNTCOMP survey (13 controller families, their
checking and scoring, their spec pitfalls) and this review's measurement files (section 11).

## 1. The task kind: `ReactTask`

The existing kinds say WHAT is computed: a function (`CombTask`), or a function delivered after a
start within a latency (`TxTask`, `StreamTask`). A reactive controller has no transaction. It runs
for ever and must keep a temporal property over the whole input trace.

A `ReactTask` fixes:

* the ports: `clk`, a synchronous active-high `rst`, data inputs, outputs;
* `atReset`: what the snapshot of a reset entry must show;
* a SAFETY monitor: spec-side ghost state (`Ghost`, `ginit`, `gnext`) and a per-cycle predicate
  `safe` on the ghost state, the cycle's inputs and the cycle's outputs;
* RESPONSE obligations (`Obl`, `trig`, `resp`) with one bound `K`.

The semantics is ls-sv's E, unchanged: one stimulus entry is one clock period; the snapshot is the
state after the edge and the settle, with the entry still applied (`Runs2`, `⊨₂`).

## 2. The statement, clause by clause

`ReactTask.SatisfiedAt p K d` is three conjuncts. Each clause is there to stop a named attack.

| clause | says | why it is there (the attack it stops) |
|---|---|---|
| `Interface` | the ports are exactly `clk, rst`, the inputs, the outputs | hidden mode pins; wrong widths (as `CombTask`) |
| `ClockedBy clk none` | one clock, no async process, the clock not read as data | gated or tied clocks; the one async-reset shape `Design2` can express (the others, `negedge` and `iff` need the source gate: H2) |
| `MooreOut` | no combinational path from an input port to an output port | the Mealy phantom: a snapshot of a Mealy output is a value no wire carries. A10 (`gnt = (req == last) ? g : req`) passes every snapshot check and grants two clients in silicon |
| `Terminates2` | every schedule and stimulus gives a completed run | vacuity: `⊨₂` quantifies over completed runs only |
| `Released` + `InsAt` (hypotheses) | a reset release `c1`; known inputs at the reset entry and every entry after it | stimulus-only: a design cannot make a hypothesis false |
| **KS** `KnownAt` | every signal but `clk` is fully known in every snapshot from the reset entry on | x-optimism (A16, below): ls-sv and Yosys read one text as two circuits |
| G0 `atReset` | the reset snapshot shows `gnt = 0` | unreset output flops (A11); a grant out of reset |
| `Safe` (G1-G3 for the arbiter) | per cycle: at most one grant, only to a requester, someone if anyone requests | grant-everyone (A02), spurious grants (A03, A05), lazy designs (A06, A15) |
| `Responds` (G4) | an obligation triggered at `K + 1` consecutive entries is answered in one of those snapshots | starvation (A04, A08, A09, A12); deferral beyond `K` |

Three properties of the shape, each by construction:

* **No environment assumption.** The hypotheses are about the stimulus only. SYNTCOMP's two worst
  traps (the system forcing an assumption violation, and lazy "standard" implication) cannot
  occur, because there is nothing for the environment to violate.
* **Every prefix is a claim.** The list `xs` has any length, so a later input cannot void an
  earlier claim.
* **Bounded, not eventual, response.** G4 is refuted by a finite run. ls-sv's runs are finite, so
  `G(r -> F g)` could never be refuted, and a design that defers for ever would pass.

The window form needs no "hold until granted" rely: it is equivalent to the bounded-response form
under that rely, and stronger without it (DERIVED, `tasks/arbiter/README.md` (b)).

## 3. The first task: `arbiter`, the N-client fair arbiter

```systemverilog
module arbiter #(parameter int N = 8) (
  input logic clk, rst, input logic [N-1:0] req, output logic [N-1:0] gnt);
```

* Range `1 ≤ N`, `N·N < 2^31` (a matrix arbiter declares `N·N` bits).
* Safety: `gnt = 0` iff `req = 0`, else `gnt` is one bit of `req` (G1, G2, G3).
* Response: `K = N - 1`, fixed in the task's `Statement`. A client that requests at `N`
  consecutive entries is granted in one of those snapshots.
* The grant of snapshot `c` answers the request of entry `c` and is on the wire for the whole
  next period (registered, Moore).
* Scored instance: **`N = 8`, `K = 7`**. Probe points `N = 1, 2, 3, 5, 8` (A09 passes at powers
  of two only).
* Ranking: sky130 area and period, the usual sequential score with one decision per cycle.

**`K = N - 1` is optimal and tight.** `Refute.lean` `bound_tight` proves, for every `N ≥ 2`,
that no design satisfies the statement with `K = N - 2`: with all clients requesting for `N - 1`
cycles, mutual exclusion allows only `N - 1` grants. Every passing design measured reaches it
(max wait 7 at `N = 8`). So a declared `K` would be a dead column (JUDGED); a weaker-fairness
variant would expose it like `TxTask`'s latency.

**Policy is free.** Any policy meeting G4 is legal: round-robin pointer or mask, rotating
priority, matrix/LRU. The statement does not pin the state encoding either.

## 4. The reference and the golf space

Real-world first (`rtl-probe/README.md`, all pinned by commit and licence):

* **OpenTitan `prim_arbiter_tree`** (lowRISC/opentitan `0a6ff685`, Apache-2.0): the chosen
  reference. A round-robin binary tree with one N-bit mask register. Adapted in 4 counted
  changes (assertions removed, sync active-high reset, packed data port, the two 2-D trees at
  module scope for Yosys), behaviour identical to upstream (0 mismatches over 20,000 random
  cycles). It is Mealy, so it enters behind one output register (own wrapper).
* **verilog-axis `arbiter.v`** (alexforencich `48ff7a7e`, MIT): natively Moore (`grant_reg`);
  passes every simulation check unmodified. Needs `priority_encoder`'s unpacked arrays
  flattened to pass the gate.
* **pulp `cc_rr_arb_tree`** (common_cells `e73baaec`, SHL-0.51): adapted in 9 changes; keeps two
  `cc_lzc` instances, so it needs the hierarchy route R-HIER.

PPA at the scoring point (MEASURED, `score/ppa.py --seq`, flow sky130_a0_v2; files in the task
README section 4):

| design (Moore) | N | area µm² | period ps | flops |
|---|---|---|---|---|
| OpenTitan tree + output register | 4 | 300.3 | 1094 | 7 |
| same | 8 | **668.1** | **1454** | 15 |
| own mask round-robin (`designs/rr_mask.sv`) | 8 | 769.5 | 2844 | 16 |
| own rotating priority (`designs/rotate.sv`) | 8 | 1327.5 | 3148 | 11 |
| (attack A04, fixed priority: unfair) | 8 | 289.0 | 888 | 8 |

The tree is 13% smaller and 2x faster than the naive mask design. Matrix/LRU, one-hot vs binary
pointer and parallel-prefix variants are the next points (JUDGED). Fixed priority is the floor a
cheat would aim at: 2.3x smaller than the best fair design.

**Cost of KS on the reference (MEASURED, Icarus, `review/tb_ks.sv` in scratch).** At `N = 1` the
adapted tree's hoisted `idx_tree` and `data_tree` are driven by no branch, so they are `x`, and KS
rejects the wrapper there. At `N = 2, 3, 8` every internal signal is known. The fix is one more
adaptation line (tie both to `'0` in the `N == 1` branch).

## 5. Review of the draft statement (this track, 2026-11-04)

I tried to break the draft both ways: a WRONG design that satisfies it, and a RIGHT design it
rejects.

### 5.1 Holes found

**H1, x-optimism on a never-reset register: FIXED in the statement (KS).** Attack A16
(`tests/arbiter/attacks/a16_xopt.sv`): a correct round-robin, plus a register `u` that is never
reset and holds itself, and `if (!u) gnt <= fixed; else gnt <= pick;`.

* ls-sv and every 4-state simulator: `u` is `x` for ever, `!x = x`, and `if` on `x` takes the
  ELSE branch (IEEE 1800 §12.4). Every snapshot is the round-robin's. The draft's G0 to G4 hold,
  and a proof would go through.
* Yosys reads `u` as a don't-care 0 and keeps the THEN branch. The scored netlist is a
  fixed-priority arbiter.
* MEASURED: the source gate with the clocked rules passes it (`srcgate.py --clock clk`). The
  scored netlist is **280.3 µm², 888 ps at `N = 8`** (8 flops; fixed priority's own score is
  289.0), against 668.1 µm² for the best fair design. Simulated, the RTL passes every check at
  `N = 4, 8` in all three stimulus modes; the Yosys netlist (generic `synth`, Yosys `simcells.v`)
  fails G4 3064 to 17129 times per 20,000 cycles.
* A 2-state `bit u` does not reproduce it: ls-sv starts a 2-state variable at 0 (`initState2`),
  and Yosys agrees (MEASURED: both polarities score as the design ls-sv sees, 769.5 and 280.3 µm²).

The fix is the KS clause: every signal but `clk` is fully known (`LVec.allKnown`) in every
snapshot of a segment, the reset snapshot included. To make it satisfiable, the reset entry's
data inputs are now required known too (silicon inputs are 0 or 1; with an `x` request every net
computed from `req` is `x` in the reset snapshot). Argument (DERIVED): with KS, every register and
net read at an edge inside a segment is known, so no `x` reaches a decision there; the source gate
refuses the other `x` sources (`x` literals, undriven nets, out-of-range selects).
`Refute.lean` `xopt_refuted` refutes the `N = 2` twin by its KS failure; `#guard`s show that its
snapshots pass G0 to G4 on the same workload, and that `rr2` and `merged2` pass KS.

Residual (DERIVED, not closed by KS): an `x` decision at the reset EDGE itself, reading pre-reset
state (`if (rst) begin u <= 0; if (u) w <= 1; else w <= 0; end`). It changes silicon only until
the second reset, and it gives no area (Yosys keeps both flops). The clocked post-synthesis check
(random initial state) catches it with probability 1/2 per seed; the x-taint rule [XTAINT] closes
it.

**H1 is not specific to reactive tasks.** The frozen `TxTask`/`StreamTask` have the same hole
(DERIVED: `if (!u) <cheap wrong result> else <right>`). There the clocked post-synthesis check is a
backstop: it compares the netlist with ls-sv cycle by cycle, and the folded netlist differs. The
REFUSALS.md line "Every SOURCE of an x or z is refused, exactly" is not true for clocked kinds: a
never-reset register is an `x` source the gate does not refuse.

**H2, async reset, `negedge` and `iff` are invisible to the statement: a PIPELINE precondition.**
MEASURED on the pinned extractor's output: `@(posedge clk or posedge rst)` is recorded as
`areset: rst`, `@(negedge clk)` as `edge: neg`, `@(posedge clk iff en)` as `iff`. The loader
(`LeanModels/Sv/Ingest2.lean`, `parsePProcess`) reads none of the three fields, so each becomes a
plain `alwaysFF clk`. MEASURED (`load_design_sv2` of the three envelopes, processes `#eval`ed):
A13 loads as `[alwaysComb, alwaysFF clk]`, the `negedge` design as `[alwaysFF clk, alwaysFF clk]`,
the `iff` design as `[assign, alwaysFF clk]`. So `ClockedBy` cannot reject them, and `iff` even
changes the function: with `iff en` and `en = 0` the flop never updates in silicon, while the
model's snapshots show `gnt = 00` at the reset and `01` after one request (MEASURED).

* The source gate's clocked rules refuse all three (MEASURED: `srcgate.py --clock clk` refuses
  each with its own finding; without `--clock` all three pass).
* `check.py` applies the clocked rules for `CLOCKED_KINDS` only. **`react-family` must join
  `CLOCKED_KINDS`.**
* `load_sv` (the tests path, `check/envelope.py` `extract`) calls the gate WITHOUT the clock. A
  test that loads A13 (async reset) gets a synchronous design that satisfies the statement.
* The draft's claim "A13 is refused by `ClockedBy clk none`" was wrong; corrected in `Spec.lean`
  and the task README.
* Upstream (ls-sv lane, not touched here): `parsePProcess` should refuse the three fields loudly.

### 5.2 Tried, no hole

* **Grants to non-existent clients.** `gnt` has exactly `N` bits (`Interface`), and every
  property reads `getLsbD` at `i < N`.
* **`N = 1`.** `K = 0`, so G4 is G3 for the one client; the only legal design is `gnt <= req`,
  registered, reset to 0. Both own designs pass at `N = 1` (MEASURED, `sim.py`).
* **X on outputs.** `ShowsAt` needs `LVec.ofBitVec` values; KS now covers every other signal.
* **Glitches inside a period.** A Moore output decoded from registers can glitch after the edge.
  Synchronous consumers sample at the next edge, so the statement does not pin it (recorded).
* **Reset.** Every reset entry's snapshot is claimed (a release with `xs = []`), and every release
  starts a claim from any history.
* **Counter overflow.** The claim covers segments of every length, so a wrapping counter is caught
  by the statement even where simulation misses it. A17 (`attacks/a17_timebomb.sv`): round-robin
  for 4095 cycles after a reset, then fixed priority. `sim.py` passes it at every point and mode
  (MEASURED: the bench resets every ~256 entries); the statement rejects it (DERIVED: a segment of
  4095 + N entries with every client requesting). Lesson for the react post-synthesis stimulus:
  include long reset-free runs.
* **The environment.** There is no assumption to exploit.

### 5.3 Right designs it rejects (over-strong), each with a workaround

* **`MooreOut` is per process.** A comb block that reads an input puts ALL its targets in the
  input cone. `merged2` (`Refute.lean`) computes the next grant from `req` and drives `gnt = gq`
  in ONE `always_comb`: right in silicon (it passes KS and G0 to G4 on `workload`), rejected by
  `merged_not_moore`. Workaround: split the block. A per-assignment cone with the enclosing
  conditions would admit it (sound, about 40 lines of trusted text; JUDGED not worth it yet).
* **`MooreOut` rejects reset-gated outputs** (`assign gnt = gnt_q & ~{N{rst}}`), because `rst` is an
  input. Correctly so when `gnt_q` is unreset; harmless otherwise.
* **KS rejects dead `x` nets**: a declaration nothing drives, or one driven only in a generate
  branch the point does not take. MEASURED on the OpenTitan reference at `N = 1` (section 4).
  Workaround: tie it off.
* **Moore only.** The real-world Mealy arbiters need one output register: +N flops and one cycle of
  latency. A Mealy kind needs the pre-edge sample in the trace (the architecture lane's
  `CycleObs`).
* **One-cycle synchronous reset.** A design with a reset synchronizer fails G0. Real-world async
  resets enter by adaptation, as in the reference.
* **Work conservation (G3).** Time-division arbiters (fair, not work-conserving) are rejected on
  purpose; without G3 the gated token ring A06 would win.

### 5.4 Behaviour the statement does not pin, on purpose

**An intermittent requester can starve.** The reference round-robin itself starves a client that
requests at every other entry. MEASURED (Icarus, `rr_mask.sv`, `N = 3`, clients 1 and 2 always
requesting, client 0 at odd entries): 500 requests, 0 grants; the grants alternate `010, 100`.
G4 only covers requests held `N` entries. A "sparse" form (any `N` requests, consecutive or not)
would reject every round-robin. This matches industry: OpenTitan's fairness assertions assume
`ReqStaysHighUntilGranted`.

## 6. The proof route, and the library it needs

The route mirrors `TxTask.satisfiedAt_of_phases`:

1. **Structure.** `Interface`, `ClockedBy`, `MooreOut` (FF-only: `S` = the input names, as
   `rr2_moore`), `Terminates2` (the FF-only invariant).
2. **One cycle.** The FF-only closed form `cycleStep2_profile`: the snapshot after a non-reset
   entry with request `x` from state `(gnt, mask)` is `(pick x mask, next mask)`.
3. **KS.** In the closed form every register holds an `LVec.ofBitVec` value after the reset edge
   and every comb net is a function of known values, so KS is a corollary of the reset branch
   covering every register.
4. **Reduction theorem.** From a `CycleModel`, an invariant, an output map, and per obligation a
   rank `≤ K` that drops at every triggered, unanswered step, conclude `Follows`. The pure window
   argument is proved (`responds_of_rank`).
5. **The reference's rank.** Round-robin mask or pointer `p`: `rank i = (i - p) mod N`. If `i`
   requests and loses, the winner lies between `p` and `i`, so the rank drops by at least 1.

| piece | what | size |
|---|---|---|
| L1 | `ReactTask.satisfiedAt_of_rank`: release/segment bookkeeping + `responds_of_rank` | M |
| L2 | `MooreOut.of_ffOnly` and a decidable `MooreOut` checker with its soundness lemma | S |
| L3 | priority-encoder and thermometer `BitVec` lemmas for all `N` (`x & -x`, `~((g << 1) - 1)`); for trees, the same over the generate-loop tree by induction on the level | M-L |
| L4 | KS from the FF-only closed form and reset coverage | S |
| L5 | R-HIER, for references that keep an instance (the OpenTitan wrapper, pulp's `cc_lzc`) | L (E-core-2) |

To avoid L5 for the first reference, fold the output register INTO the adapted OpenTitan module
(one module, one more counted change). JUDGED: prove the own mask design first (FF-only, no tree),
then the tree.

## 7. The fixed-size layout tier, for reactive tasks

The layout tier (PLAN4 3c) checks one instance by equivalence with a proved reference. That does
not fit a reactive task: any policy meeting G4 is legal, so a golfer's netlist need not be
equivalent to the reference. It needs PROPERTY checking instead (JUDGED):

* **The monitor.** For fixed `N`, G0 to G4 is a safety property of the netlist composed with a
  small monitor: per client a counter of consecutive ungranted requests (`⌈log2 N⌉` bits), and a
  bad state when a client is still ungranted at its `N`-th consecutive request. The checker builds the monitor ITSELF from the task (as it builds
  the miter CNF itself), never from the golfer.
* **The netlist is 2-state, and its initial state is free.** The model checker starts in any
  state, then asserts `rst` for one cycle. So x-optimism (H1) cannot arise there: the property
  must hold from every power-up value. This is stronger than the Lean statement at the reset
  edge (it closes the H1 residual).
* **Certificates.** An inductive invariant (k-induction or IC3, the HWMCC format). Certifaiger
  checks a witness circuit with a few combinational SAT queries, and their LRAT proofs go to
  `cake_lpr` or Lean's LRAT checker. The solver stays untrusted. Size at `N = 8`: 15 design
  flops plus 24 monitor bits (JUDGED: small for IC3).
* **No certificate.** Bounded model checking to a depth is not a proof; it would be an
  unverified run under a time limit, as the tier already does for large miters.
* KS, `MooreOut` and the gate's clocked rules are RTL-level conditions; at netlist level the
  same purposes are served by the 2-state free-initial-state check and by sign-off STA (no path
  from an input to an output inside a period, if the task says Moore).

## 8. The next tasks

Ranked (JUDGED, from the SYNTCOMP survey's recommendation; sizes are SYNTCOMP's smallest known
circuits, L latches / A AND gates):

1. **HSBUF(n), a handshake buffer controller (GenBuf).** The 4-phase req/ack controller between n
   senders and 2 receivers, the FIFO in the environment (the Anzu/IBM shape, not the TLSF
   variant, which hard-codes 2 senders and lets the reference raise a request with no data).
   Hand 2n+3 L / 4n+2 A; tools 329 at n=2. **Needs the kind's rely form**: the environment holds
   `req` until `ack` and drops it after, a rely that reads PAST outputs. Form (in the task README
   (c)): a predicate `rely g x` on the ghost state before cycle `j` and entry `j`'s inputs; the
   claim "if `rely` held at every cycle `< n`, the guarantee holds on the prefix of length `n`";
   plus a task-author theorem, receptiveness `∀ g, ∃ x, rely g x`. Real-world anchor: the two
   FIFOs of the RTL probe (pulp `cc_fifo`, OpenTitan `prim_fifo_sync`), not yet adapted.
2. **AHB-ARB(n), the AMBA 2 AHB bus arbiter, in two steps.** (a) The decomposed arbiter: exactly
   one `HGRANT` always (default master 0), grants frozen while not `HREADY`, fairness. Hand n+1 L
   / 6n+6 A (76 at n=10) against the tools' 3910. Needs: an input `ready` with a HOLD clause in
   `safe` (ghost state = last grant), and a rely `G F HREADY` made bounded ("`HREADY` within B
   cycles"). (b) The full case study: `HLOCK`, `HBURST` SINGLE/BURST4/INCR, `HMASTER`,
   `HMASTLOCK`; SYNTCOMP's auxiliary signals `START/LOCKED/DECIDE/BUSREQ` become ghost state, not
   ports. Hand 3n+9 L / 17n+24 A; tools reach only n=2. No permissively licensed AHB arbiter RTL
   was found (`rtl-probe/README.md`): the reference is written from the ARM spec.
3. **PRIO-ARB(n), an arbiter with a priority master.** The one SYNTCOMP arbiter with a genuine
   input assumption (the master does not hold its request for ever), as the bounded rely "the
   master holds `r_m` at most B consecutive cycles". Tools beat the one-hot hand design (25 vs 33
   at n=8, a binary token), so encoding is a real golf axis.

Rejected (from the survey): the simple and round-robin SYNTCOMP arbiters (a request-ignoring ring
counter is minimal; kept as attack A05), the load balancer (realizable only by forcing an
assumption violation).

## 9. Open questions (decided 2026-11-05: the defaults below; task README section 1)

Decided with the study's defaults: 1 KS in the trusted text, yes; 2 the frozen kinds, unchanged here (the
shared conjuncts are another branch's work); 3 Ingest2's dropped fields, `react-family` is a clocked kind
(the gate refuses them); 4 `K` fixed at `N - 1`; 5 scope of v1 as below; 6 Moore only; 7 the layout-tier
check, open. The questions as the study asked them:

1. **KS in the trusted text.** Accept the known-state clause (and the known reset-entry input) for
   `ReactTask`? It closes a measured 2.4x scoring exploit at the statement level. Or keep it out
   and rely on a pipeline rule (a reset-coverage gate rule, or XTAINT) plus a react post-synthesis
   check?
2. **The frozen kinds.** Two holes reach `TxTask`/`StreamTask` too: the Mealy phantom (task README
   F1) and x-optimism (H1). A `txtask-v2` with `MooreOut` and KS, or the post-synthesis backstop
   only?
3. **Ingest2's dropped fields** (H2). Ask the ls-sv lane to make `areset`, `edge: neg` and `iff`
   loud in `parsePProcess`, and have `load_sv` apply the clocked gate rules for clocked tasks?
4. **`K` fixed at `N - 1`**, or exposed to the golfer as a third column (weaker fairness for less
   area)?
5. **Scope of v1.** No `ready`/backpressure input, no index output, no data mux. Each is a later
   task of the same kind. Agreed?
6. **Moore only for now.** A Mealy reactive kind waits for the pre-edge sample in the trace. Agreed?
7. **Layout tier.** Is a model-checking certificate (section 7) the right check for a fixed-`N`
   reactive instance, given that equivalence to a reference does not apply?

## 10. Build plan

Sizes: S = under a day, M = 1-3 days, L = a week or more (JUDGED).

| # | item | depends on | size |
|---|---|---|---|
| B1 | The maintainers review `Spec.lean` (this note, the task README); rulings on section 9 | — | — |
| B2 | L2: `MooreOut` checker + `MooreOut.of_ffOnly` | B1 | S |
| B3 | L4: KS from the FF-only closed form | B1 | S |
| B4 | L1: `ReactTask.satisfiedAt_of_rank` | B1 | M |
| B5 | L3: priority-encoder / thermometer lemmas ∀ N | — | M |
| B6 | first proved reference: the own mask round-robin (FF-only, one module) | B2-B5 | M |
| B7 | `react-family` in `check.py`: `task.json`, `CLOCKED_KINDS` (gate clocked rules), the clocked post-synthesis check with a reactive stimulus (random, hold-until-granted, all requesting, long reset-free runs) and `oracle.py` checking G0-G4 on the netlist | B1 | M |
| B8 | the attacks as `tests/arbiter/negative/` with `load_sv` (needs `load_sv` to apply the clocked rules) and `tests/expected.json` rows; refutations of A11, A13 (through the gate), A14 | B7 | S-M |
| B9 | the OpenTitan reference: output register folded in, the `N = 1` tie-off, the tree lemmas over the generate loops | B5, B6 | L |
| B10 | ls-sv: loud `areset`/`edge`/`iff` in `Ingest2` | ls-sv lane | S |
| B11 | XTAINT or a reset-coverage rule for every clocked kind (txtask-v2) | ruling 2 | M |
| B12 | the rely form in `ReactTask` + receptiveness; HSBUF | B4 | L |
| B13 | AHB decomposed arbiter (ready + hold clause, bounded `HREADY` rely) | B12 | M-L |
| B14 | layout-tier certificates for reactive instances (monitor builder, Certifaiger-style check) | the layout tier | L |

## 11. What was run here (the review)

MEASURED, in the session scratchpad `reactive/review/` unless named:

* `srcgate.py` with and without `--clock clk` on A13, `negedge`, `iff` and A16; the pinned
  extractor (`extract.py --top arbiter`) on the same files, envelope process records read.
* `score/ppa.py --seq` on A16 in both polarities, the 2-state variants and A04, at `N = 8` (and A16
  at `N = 4`: 133.9 µm², 541 ps).
* Icarus: A16's RTL and its Yosys `synth` netlist through `tests/arbiter/tb.sv`; A17 through
  `sim.py`'s runner at `N = 2, 3, 8`; the intermittent-requester trace; the KS check of the
  OpenTitan wrapper at `N = 1, 2, 3, 8`.
* `tests/arbiter/sim.py --cycles 20000 --axis … --ot …` with the two new attacks: exit 0, every
  expectation met (A16 and A17 PASS, as expected of attacks that simulation cannot see).
* Lean (`leanprover/lean4:v4.33.0-rc1`, through the shared slot, against the shared tree's built
  oleans, read only): `Spec.lean` and `Refute.lean` with the KS change elaborate with exit 0, no
  error, no `sorry`. `#print axioms`: `xopt_refuted` `[propext, Quot.sound]`; `rr2_moore`,
  `merged_not_moore` `[propext]`; the earlier eight unchanged. Every `#guard` passes.
* A scratch probe (`reactive/review/Probe.lean`) loads the extractor's envelopes of A13, the
  `negedge` design, the `iff` design, A16 and `rr_mask` with `load_design_sv2`. Processes as in H2.
  `passes`/`passesK` (G0-G4 / G0-G4 and KS, on the `Refute.lean` workloads): A16 at `N = 2` and
  `N = 8` `(true, false)`: ls-sv sees a fair arbiter and KS rejects it; `rr_mask` at `N = 2` and
  `N = 8` `(true, true)`.

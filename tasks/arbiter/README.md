# Task `arbiter`: a fair N-client arbiter, the first reactive task (`ReactTask`)

Give at most one of `N` requesters the grant each cycle, only one that asks, someone whenever anyone asks,
and grant a requester that asks `N` cycles in a row within those `N` cycles. This is svGolf's first REACTIVE task: a
controller that runs for ever and keeps a temporal property over the whole input trace, not a function
(`CombTask`) and not a transaction with a latency (`TxTask`, `StreamTask`). The statement covers every
`N` with `1 ≤ N`, `N·N < 2^31`; the score is the usual clocked one at `N = 8`, sky130 area times the clock
period (one decision per cycle).

Status (2026-11-07):

```
trusted statement: final, decided 2026-11-07 (the kind SvGolf/TaskReact.lean, the task Spec.lean, and the
  primitives of SvGolf/TaskSeq.lean they share), the clocked statements' rules 2 and 3 (§7)
run2 proof: complete, from every power-up state
checker: react-family (check.py)   post-synthesis: react-family (segments, a 70000-entry run, a Moore sample;
  8 seeds per point)
reference: reference/rr_mask.sv + rr_mask.lean (own code, every N with 1 <= N, N*N < 2^31), check.py ACCEPTS it
  (--postsynth full)
attacks: 19, all rejected (17 hand-written: 15 at postsynth, 1 at score, 1 at source; 2 mutants at extract)
negatives: 2   site: listing decided 2026-11-07; par = the reference's record 84da5a4152db,
  769.488 um^2 x 2826 ps = 2174.57 um^2*ns ((k), (n))
```

Labels: **MEASURED** = run (command or file named); **DERIVED** = a hand argument given here; **JUDGED** =
opinion.

| file | what |
|---|---|
| [`Spec.lean`](Spec.lean) | trusted text (final, decided 2026-11-07): the task (`task`, `Statement`) |
| [`../../SvGolf/TaskReact.lean`](../../SvGolf/TaskReact.lean) | trusted text (final, decided 2026-11-07): the kind `ReactTask`, `MooreOut`, the clocked statements' rules 2 and 3 (`ModelsPU`, `TerminatesPU`, `XSafe`, from `SvGolf/TaskSeq.lean`, whose Status lists the shared declarations, final too) |
| [`task.json`](task.json) | `react-family`, status `ready`, the reference, the reactive post-synthesis block |
| [`oracle.py`](oracle.py) | the reactive post-synthesis stimulus (`segments`) and the guarantee read on a netlist's grants (`violations`) |
| [`reference/rr_mask.sv`](reference/rr_mask.sv) | the reference: a registered mask round-robin (own code) |
| [`reference/rr_mask.lean`](reference/rr_mask.lean) | its proof, for every `N` in range (untrusted, checked like a submission) |
| [`../../SvGolf/React.lean`](../../SvGolf/React.lean) | the svGolf proof library for reactive tasks: the reduction `ReactTask.satisfiedAt_of_rank` (from every power-up), the window argument `responds_of_rank`, `snapshots_known` (by the x-free lemma), `mooreOut_of_combTargets` |
| [`../../SvGolf/RoundRobin.lean`](../../SvGolf/RoundRobin.lean) | the svGolf proof library's round-robin facts: the lowest set bit, the thermometer above a one-hot, the mask round-robin step, the cyclic distance |
| [`../../tests/arbiter/negative/Refute.lean`](../../tests/arbiter/negative/Refute.lean) | untrusted, kernel-checked: four wrong designs, a Mealy design and four designs with an unreset register (A16, its twin, `negative/bit_ring.sv`, `negative/reset_edge.sv`) REFUTED, each from one power-up state; `MooreOut` on a right design both ways; the bound `N - 1` proved TIGHT |
| [`../../tests/arbiter/negative/Mutants.lean`](../../tests/arbiter/negative/Mutants.lean) | untrusted, kernel-checked: eight generated mutants of the reference REFUTED (G0 to G4, eight operators; one at `N = 4`), each twin checked equal to the loaded `tests/arbiter/mutants/<id>.sv` (section 8) |
| [`../../tests/arbiter/`](../../tests/arbiter/) | `tb.sv` + `sim.py` (the statement read by simulation, Icarus), `attacks/` (17), `designs/` (two more correct arbiters), `mutants/` (the mutation sweep, section 8) |

## Proving a new design

A new arbiter is your own `solution.sv` (the header below; run-time `/ % **` are banned) and a `Solution.lean`
that proves it for every `N` with `1 ≤ N`, `N·N < 2^31`. Any fair policy is allowed: a pointer, a mask, a
rotating priority, a tree, a matrix. Find the design without Lean, then check it once without a proof:

```bash
python3.12 score/ppa.py solution.sv --task tasks/arbiter --seq --path   # area and period, about a second
python3.12 check.py tasks/arbiter solution.sv --unproved --stage-dir stage
```

The first command weighs the design through the clocked flow (`--seq`; without it `ppa.py` refuses the
flip-flops): the sky130 area, flip-flops included, and the register-to-register period, one decision per
cycle, with the critical path (`--path`). The second runs every stage that needs no proof: the clocked source
rules (one clock, rising edge, synchronous reset), the check that no construct can create an `x`, the
never-loaded register check, the score, and the reactive post-synthesis check, which drives the scored
netlist through reset segments and one long run without a reset and holds every grant to G0 to G4 and the
Moore sample. A wrong policy is named there, with the cycle, before any proof. It leaves the design staged in
`stage/` for probe files ([PROVING.md, section 0](../../PROVING.md#0-the-loop)). The `sv_comb` tactics are for
combinational tasks: `--tactics` does not read a clocked design.

**The route: an invariant and a rank, `ReactTask.satisfiedAt_of_rank`** ([PROVING.md, section
20](../../PROVING.md#20-a-reactive-task-the-arbiter-reacttask); `reference/rr_mask.lean` is a complete proof,
487 code lines). The reduction in `SvGolf/React.lean` turns the statement at one `N` into facts about ONE clock
cycle, six arguments:

1. `Interface`: the ports in order and distinct declaration names (`rfl`, and `decide` on the names);
2. `Disciplined`: `ClockedBy clk none` (a `simp` over the processes) and `MooreOut`, by
   `mooreOut_of_combTargets` when no `always_comb` writes an output;
3. `TerminatesPU`, by `TerminatesPU.of_invariant` from the clock step;
4. a `ReactTask.RankModel`: the clock step in closed form (its `CycleModel`: a `Shape` of the snapshots and the
   one-cycle `Step`), an invariant `Inv` of the snapshots from a reset on, the grant `out` it shows, a `rank`
   per requester at most `N - 1`, the RESET obligation (`gnt = 0`, from any state of the shape) and the STEP
   obligation (the grant meets `Grants`, the invariant holds again, and every requester that asks is granted
   or its rank drops). For a mask round-robin the invariant is "the mask is a thermometer" and the rank is the
   requester's cyclic distance from the mask's edge;
5. the shape at every power-up state (`powerUp_cons` once per declaration);
6. `XSafe`, by `simp` with `xsafeB`.

**Lay the design out so the proof stays short**:

* register the grant: when no `always_comb` writes `gnt`, `MooreOut` is one `simp`
  (`mooreOut_of_combTargets`), and a design whose output moves with `req` between two edges is rejected by
  the post-synthesis check before the proof;
* reset every register whose value matters: the claims hold from every power-up value, the first reset edge
  included, and a register that only holds itself (`u <= u`) is refused;
* keep the combinational logic in one `always_comb` block computed from signals it does not write (the
  reference's block reads `req` and `mask`; it reads `mreq` only after writing it): ls-sv's closed-form clock
  step covers flip-flop-only designs, and a design with combinational logic proves its own settle, which for
  such a block is two passes (the reference's `settle_rr`: the first computes the block, the second changes
  nothing);
* for `XSafe`, the loaded design's `&`, `|`, `^`, `==`, `!=` operands and `?:` arms at one width, and a run-time
  index whose every value is in range (a `k`-bit index into at least `2^k` elements): `req[(p + k) % N]` is
  refused, so scan a copy of `req` padded to `2^$clog2(N)` bits, as `tests/arbiter/designs/rotate.sv` does;
* what ls-sv does not read yet: casts (`N'(1)`, `32'(p)`: write the literal `1`), `unique` and `priority`
  (refused by the source gate), declarations inside a `generate` block (refused at the `design` stage, which
  is where a tree arbiter that declares its nodes there stops today), and instances over unpacked arrays
  (refused by the extractor).

**The skeleton** (`reference/rr_mask.lean` is it, filled in for the mask round-robin):

```lean
import Submission.Design
import SvGolf.React
import SvGolf.RoundRobin

namespace Submission
open LeanModels.Sv SvGolf

-- 1. agreement: `design.sem N = myD N`, a hand-built Design2 (sv2_inst_simp)
-- 2. one cycle in closed form, from any values: the comb settle, the edge, the commit
-- 3. the cycle on known values: after a reset, and after an entry with rst = 0

noncomputable def model (N : Nat) (hN : 1 ≤ N) :
    Tasks.Arbiter.task.RankModel N (N - 1) (design.sem N) where
  -- the CycleModel: Shape, Step, init, cycle, shape
  -- then Inv, out, shows, rank, rank_le, reset, step

theorem solution : Goal := by
  intro N hN
  obtain ⟨hN1, -⟩ := hN
  exact Tasks.Arbiter.task.satisfiedAt_of_rank (my_interface N hN1) (my_disciplined N hN1)
    (my_terminates N hN1) (model N hN1) (fun st h => my_powerUp N hN1 st h) (my_xsafe N hN1)

end Submission
```

`#print axioms solution` must show `propext`, `Classical.choice` and `Quot.sound` only.

**Library lemmas that exist today** (the tables: [PROVING.md, section 6](../../PROVING.md#6-what-the-libraries-already-give-you)):

* `SvGolf.React`: `ReactTask.satisfiedAt_of_rank` (the reduction), `ReactTask.RankModel`,
  `ReactTask.responds_of_rank` (the window argument, used inside the reduction), `ReactTask.snapshots_known`,
  `mooreOut_of_combTargets`;
* `SvGolf.RoundRobin`, for every width: the lowest set bit (`IsLow`, `getLsbD_isolate`, `isolate_eq_twoPow`,
  `isolate_eq_zero`: `x & (~x + 1)` is its one-hot), the thermometer above a one-hot (`getLsbD_thermo`,
  `Thermo`, `thermo_allOnes`), the mask round-robin's `pick`, `next`, `pick_eq_zero`, `pick_sub`,
  `pick_atMostOne` and its one-step theorem `step` (the next mask is a thermometer, and a requester that loses
  gets strictly closer to the edge in the cyclic distance `dist`, `dist_le`: at most `N - 1`);
* `SvGolf.SeqV2`: `TerminatesPU.of_invariant`, `powerUp_cons`, `powerUp_nil`.

A pointer, rotating-priority, tree or matrix policy uses the reduction and the lowest-set-bit lemmas, with
its own invariant and rank: the `pick`/`next`/`step` lemmas describe the mask policy.

## The circuit

```systemverilog
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
```

## The statement in one screen

For every `N` with `1 ≤ N`, `N·N < 2^31`: the ports exactly as above, no two declarations of one name;
clocked by `clk` alone, no asynchronous process, `clk` not read as data; **no combinational path from an
input to an output** (`MooreOut`); **no construct that can create an `x`** (`XSafe`, the clocked statements' rule 3);
termination from every power-up state; and **from every power-up state** (every register and variable,
2-state ones included, at some 0/1 value: the clocked statements' rule 2), under every schedule, on every known stimulus,
in every completed run, at every reset release `c1` and for every list `x0 :: xs` of request vectors driven at
the reset entry `c1-1` and the entries `c1, c1+1, …` with `rst` = 0, the snapshots `c1-1, c1, c1+1, …` show
known grant vectors `y0, ys[0], ys[1], …` with

| | property | formal (`Spec.lean`, `SvGolf/TaskReact.lean`) |
|---|---|---|
| G0 | no grant out of reset | `atReset`: `y0 = 0` |
| G1 | mutual exclusion | `AtMostOne ys[j]` |
| G2 | no spurious grant | `ys[j]` bit `i` ⇒ `xs[j]` bit `i` |
| G3 | work conservation | `xs[j] ≠ 0 ⇒ ys[j] ≠ 0` |
| G4 | bounded fairness, `K = N - 1` | client `i` requests at the `N` entries `j..j+N-1` ⇒ granted in one of the snapshots `j..j+N-1` |

G1 ∧ G2 ∧ G3 say: `gnt = 0` iff `req = 0`, else `gnt` is ONE bit of `req`. G4 says which bit, up to the
policy: any policy that serves a persistent requester within `N` cycles is legal (round-robin pointer or
mask, rotating priority, LRU/matrix). The grant of snapshot `c` answers the request of entry `c` and is on
the wire for the whole next period (Moore).

## 1. The decisions

The ruling of 2026-11-05 took the study's defaults for its open choices (a) to (e). Each is recorded
here as **decided 2026-11-05**, with its reason; so are the choices made when the kind was wired through the
pipeline (f) to (k).

### (a) Moore observation (decided 2026-11-05)

* **Inputs** are the stimulus entries from a reset release on (`Released`, C1 of the sequential contract,
  reused verbatim), with known values on the data inputs (`InsAt`; the `TxTask` knownness rule). A list `xs`
  of any length is quantified, so every prefix is a claim.
* **Outputs** are E's snapshots (`Runs2`, `⊨₂`; the same protocol as `SeqTask`/`TxTask`/`StreamTask`):
  snapshot `c` is the state after the edge of cycle `c` and the settle that follows, with entry `c` still
  applied. No new run function, no new trace type.
* **Moore, enforced on the design** (`MooreOut`: a set of signals containing every input, closed under the
  comb-phase processes, containing no output). Reasons: (1) a snapshot of a Mealy output is `f(registers after
  the edge, the inputs BEFORE it)`, a value no wire carries in silicon; (2) it is exploitable: register
  `last <= req` and drive `gnt = (req == last) ? g : req` from a correct registered grant `g`; every snapshot
  shows `g`, while in silicon `gnt = req` whenever `req` changes, which breaks G1 (`Refute.lean`
  `mealy_silicon` evaluates it in the kernel); (3) the pre-edge sample a Mealy kind needs is not in the trace
  type today; (4) it costs the proof route nothing (a design whose comb processes do not reach an output has
  `S` = the input cone).
* **Synchronous reset only**; the reset snapshot IS claimed (G0): for a Moore output it is what the
  requesters see during the first period with `rst` = 0.
* **Every power-up state, no x-creating construct** (the clocked statements' rules 2 and 3, 2026-11-06; until then the
  known-state clause KS of the study's review, 2026-11-04). ls-sv's own start state is `x` for a 4-state
  register and `0` for a 2-state one, and `if (x)` takes the else branch; the netlist's flops power up to
  some 0/1 value. So the claims are about the runs from EVERY power-up state, the first reset edge included,
  and rule 3 keeps every value of those runs known. What this covers: an unreset register whose value
  matters fails from some power-up (A16's `if (!u)` from `u = 0`; the 2-state ring of
  `negative/bit_ring.sv` from `u` all ones, which KS accepted because ls-sv started it at `0`; the flag of
  `negative/reset_edge.sv` set from the pre-reset `u` at the first reset edge, which KS accepted because the
  edge read `x`). What it does not cover: a register that only holds itself (`u <= u`) is still a single
  power-up value in ls-sv, while the pinned flow removes it and resolves each read separately; the checker
  refuses such a design (`check.py` `never_loaded`, the `score` stage, every clocked task).

Consequence: the real-world Mealy arbiters (OpenTitan `prim_arbiter_tree`, pulp `cc_rr_arb_tree`) enter
behind ONE output register. A Mealy reactive kind is a later version, once the trace carries the pre-edge
sample.

### (b) Safety + BOUNDED response; `K` a task constant, `N - 1` (decided 2026-11-05)

* Unbounded liveness (`G(r → F g)`, SYNTCOMP's form) cannot be refuted by a finite run, and ls-sv runs are
  finite. Bounded response is falsifiable and matches industry (OpenTitan `Fairness_A`, `NoStarvation_A`).
* **Form: a persistence window.** "If `i` requests at the `K+1` entries `j..j+K`, a grant to `i` is among the
  snapshots `j..j+K`." Under the usual rely "a request is held until granted" it is equivalent to "every
  request is granted within `K` cycles of being raised" (DERIVED: ⇐ a window with no grant would be a request
  held `K+1` cycles; ⇒ if `i` raises at `j` and is not granted by `j+K`, the rely keeps it up at `j..j+K`, a
  window with no grant). Without the rely it is STRONGER, and needs no assumption (c).
* **`K` is a task constant, `N - 1`, fixed in the task's `Statement`.** The kind takes `K` as an argument of
  `ReactTask.Statement` (like `TxTask`'s `lat`), so a later variant can expose it. For this task it is OPTIMAL
  and TIGHT: no design satisfies the statement with `N - 2` (`Refute.lean` `bound_tight`, proved for all
  `N ≥ 2`: with all `N` clients requesting for `N - 1` cycles, mutual exclusion allows at most `N - 1`
  grants); every passing design measured reaches exactly `N - 1` (max wait 7 at `N = 8`). So a declared `K`
  would be `N - 1` on every competitive entry: a dead column (JUDGED).
* The score is the plain sequential one with `cycles = 1`: one decision per cycle, so the time is the clock
  period.

### (c) No environment assumption beyond reset and known inputs (decided 2026-11-05)

* The hypotheses are about the STIMULUS only: a release, `rst` = 0 afterwards, known `req`. A design can
  neither falsify the hypothesis nor void a guarantee by an environment "violation": there is no environment
  obligation. The claim holds for every prefix `xs` (strict).
* When a task needs a real rely (the AMBA AHB arbiter's `GF HREADY`, a prioritized master's bounded hold), the
  form to add to the kind is a predicate `rely g x` on the ghost state BEFORE cycle `j` and entry `j`'s
  inputs, the claim "if `rely` held at every cycle `j < n`, the guarantee holds on the prefix of length
  `n`", plus a task-author theorem, receptiveness `∀ g, ∃ x, rely g x` (JUDGED; not drafted in Lean).

### (d) The first task: the parametric N-client arbiter, "any fair" policy, scored at `N = 8` (decided 2026-11-05)

Exactly G0 to G4 above, with `Interface`, `ClockedBy clk none`, `MooreOut`, `TerminatesPU`, `XSafe` (until
2026-11-06 with KS and `Terminates2` from ls-sv's start state, (a)). Range
`1 ≤ N`, `N·N < 2^31` (a matrix/LRU arbiter declares `N·N` bits). Scoring point `N = 8`; probe points
`N = 1, 2, 3, 5, 8` (a power-of-two-only design fails at 3 and 5: A09). "Any fair" rather than
"round-robin exactly": the statement pins fairness, not a grant order, so the golf includes the policy. Not in
v1: a `ready`/backpressure input with a hold clause, an index output, a data mux; each is a later task of the
same kind.

### (e) The proof route: an inductive invariant with a RANKING (decided 2026-11-05)

The route mirrors `TxTask.satisfiedAt_of_phases` (`SvGolf/Seq.lean`):
1. **Structure**: `Interface`, `ClockedBy`, `MooreOut` (`S :=` the input cone), `TerminatesPU`, `XSafe`
   (`Terminates2` until 2026-11-06), and the shape at every power-up state.
2. **One cycle** (the closed form of the sequential profile, as `mm_cycle` for matmul): the snapshot after a
   non-reset entry with request `x` from state `(gnt, mask)` is `(pick x mask, next mask)`.
3. **A reduction theorem** (library, BUILT: `ReactTask.satisfiedAt_of_rank`, `SvGolf/React.lean`): from a
   `CycleModel`, an invariant `Inv` (indexed by the safety monitor's ghost state), an output map, and per
   obligation `o` a RANK `rank o st ≤ K` with **progress**: a non-reset step from `Inv prev` whose input
   triggers `o` either responds to `o` or makes `rank o` drop. The window argument is pure
   (`ReactTask.responds_of_rank`, for every `ReactTask`; moved there from `Refute.lean`).
4. **The goalpost's invariant and rank** (round-robin mask): `Inv` = the mask is a thermometer code (the
   clients above the last grant); `rank i` = the cyclic distance of `i` from the mask's edge, `≤ N - 1`. If
   `i` requests and is not granted, the winner is the first requester from the edge (cyclically), so it
   precedes `i`, the new edge is past the winner, and `rank i` drops.
5. **Word-level lemmas for all `N`**: "`x & (~x + 1)` is the one-hot of the least set bit", "`~((g << 1) - 1)`
   is the thermometer above `g`", and, for tree arbiters, the same over the generate-loop tree by induction on
   the level (structure-preserving: the loops stay loops).

Library support: (L1) `ReactTask.satisfiedAt_of_rank` BUILT; (L2) `mooreOut_of_combTargets` BUILT (a design
whose comb processes write no output is Moore; the decidable `MooreOut` checker is not needed for it); (L3)
the lowest-set-bit / thermometer `BitVec` lemmas for all `N` BUILT (`SvGolf/RoundRobin.lean`); (L4) KS from
the closed form BUILT, in the reference, and no longer asked since 2026-11-06 (rule 3 makes every value known:
`ReactTask.snapshots_known`; the reduction dropped the rank model's `known` field); (L5) the hierarchy route,
for references that keep an instance: not needed yet.

### (f) The kind is its own trusted module, `SvGolf/TaskReact.lean` (decided 2026-11-05)

`MooreOut`, `KnownAt` and `ReactTask` moved out of the task's `Spec.lean` into `SvGolf/TaskReact.lean`,
beside `SvGolf/TaskSeq.lean`, which it imports and does not change. `tasks/arbiter/Spec.lean` keeps the task
only (`AtMostOne`, `Grants`, `task`, `Statement`) and its sanity checks. The refutations moved to
`tests/arbiter/negative/Refute.lean` (the `tests` library). Two edits the moved text needed on today's
ls-sv: the asynchronous-reset process `Process2.alwaysFFR` has a fourth field (its reset polarity), so
`processTargets` matches it with four arguments; and `OutDiscipline` (below) takes no task.

### (g) The two named slots: `OutDiscipline` and `Known` (decided 2026-11-05; `Known` gone 2026-11-06, §7)

The output discipline and the knownness clause are each ONE definition, used once in the statement:
`ReactTask.OutDiscipline d := MooreOut d` (in `Disciplined`) and `ReactTask.Known tr c n := KnownAt t.clk tr c
n` (in `Follows`). Both are kept as the study drafted them: sound, possibly over-strong (`MooreOut` is per
process; `KnownAt` asks every signal, not only those a decision reads). **An open choice**: the clocked
statements are getting shared conjuncts (`MooreOutDep`, Moore by signal dependency; `KnownDecisions`, every
signal a decision reads known in the claim window). Switching this kind to them is a change of these two
bodies (and of `Known`'s arguments, if the shared clause reads the design), plus the refutations that name
them (`tests/arbiter/negative/Refute.lean`: `mealy_not_moore`, `merged_not_moore`, `rr2_moore`,
`knownB_of_knownAt`).

### (h) `react-family`: a clocked checker kind without a latency (decided 2026-11-05)

`check.py` `KINDS` and `CLOCKED_KINDS` gain `react-family` (not `LATENCY_KINDS`): the source gate's clocked
rules apply (they refuse an asynchronous reset, a `negedge` clock and an `iff` guard: A13 stops at `source`;
past the gate, the pinned loader refuses the last two itself and keeps an asynchronous reset as `alwaysFFR`,
which the statement's `ClockedBy clk none` refuses), the goal is `abbrev Goal : Prop := SvGolf.Tasks.Arbiter.Statement
design.sem`, a `-- svgolf-latency:` line is refused, and task.json must name its `reset` port. The score is
`score_clocked` with `cycles = 1`: `time_ps = period_ps`, ranked (`area_um2`, `time_ps`).

### (i) The reactive post-synthesis check (decided 2026-11-05)

`check/postsynth.py` "THE REACTIVE CHECK", at each `postsynth.points` point (here `N = 3, 5, 8`: two
non-powers of two, and the scored netlist). Per seed (8 since 2026-11-07, F5; 3 before), the netlist starts from a
power-up state (seed 0 all zeros, every other seed random), and ls-sv's run from one of its own (seed 0 all zeros,
every other seed ls-sv's seeded random power-up, which need not be the netlist's); then
`oracle.py` `segments` drives 24 segments, each a reset entry and then entries with `rst` = 0 (8 request
patterns: random, sparse, all, none, held requests, a pair, one at a time, an intermittent requester), the
last one **70000 entries long and reset-free** (the study's A17 lesson: a time bomb after 4095 cycles passes a
bench that resets every ~256 entries; 70000 > 2^16 drives a 16-bit counter past its wrap). The random source is
seeded by sha256(`$SVGOLF_POSTSYNTH_SALT`, task, point, seed), as the combinational check's vectors are: the
default empty salt reproduces a run, a secret salt makes the stimulus unpredictable; the design is not in the
seed, so no edit of the text picks its own stimulus. Since 2026-11-07 (F5, every clocked kind) the two power-ups
of a seed above 0, Verilator's `randSeed` and ls-sv's `seed:<k>`, derive from the same hash and are recorded in
the seed's record (`netlist_randseed`, `lssv_start`); before, they were the seed number. Binding, each failure rejects:

1. every output at every snapshot from the last entry of the first reset on: ls-sv's value is known and
   σ_src = σ_rev (`svgolf-eval --trace`); where the two runs start from the SAME state (seed 0, when the
   pinned flow replaced no register and no array lane by the constant 1: `zero_starts_agree`) the netlist
   equals ls-sv bit for bit; from different power-ups ls-sv's outputs must meet the guarantee instead (the
   evaluator of 2., on ls-sv's run).
   A guarantee admits several outputs, so a design correct from every power-up may show different grants from
   two different ones (an arbiter whose mask is not reset: `design/soundness/TXTASK-V2-REVIEW.md`, section 12, F4);
2. G0 to G4 on the NETLIST's grants, segment by segment (`oracle.py` `violations`): a bug ls-sv shares is still
   caught (A17);
3. **the Moore sample**: the harness also reads every output BEFORE each rising edge, with the entry's inputs
   applied and the clock low; it must equal the previous snapshot. An output that moves with the inputs
   between two edges has a combinational path from an input (A10, A14: a snapshot-only check cannot see it,
   the silicon does). It is sound for every design meeting `MooreOut` (its outputs are functions of the state).

Cost (MEASURED, the goalpost at the three points): about 70 200 to 70 600 cycles per seed, ls-sv 1.2 to 2.6 s
and the netlist 0.2 to 0.6 s per seed, 11 to 15 s per point, 40 s for the whole check.py run (3 seeds). With 8
seeds (MEASURED 2026-11-07, full mode, a loaded machine): 16.5, 18.3 and 21.3 s at `N = 3, 5, 8`, against the
postsynth limit of 900 s per point.

### (j) The goalpost is own code; the real-world reference waits on ls-sv (decided 2026-11-05)

Real-world first was tried and hit a wall (MEASURED 2026-11-05):

* **OpenTitan `prim_arbiter_tree`** (lowRISC/opentitan `0a6ff685`, Apache-2.0), adapted into the task's
  module with its output register folded in (`tests/arbiter/designs/arbiter_ot.sv`, changes 1 to 8 in its
  header, the licence beside it): the source gate passes it and the extractor writes 0 `Unsupported` nodes at
  `N = 1, 2, 3, 5, 8`, but `svgolf-eval` stops at `unsupported process 'GenerateDecl:Var'`: ls-sv does not
  instantiate declarations inside generate blocks (`LeanModels/Sv/Ingest2.lean` `parseGenItem`), and the tree
  declares ten variables (`req_tree`, `prio_tree`, `sel_tree`, `mask_tree`, `prio_mask_d/q`, `sel`, three
  `unused_*`) and five localparams (`Base0`, `Base1`, `Pa`, `C0`, `C1`) there. check.py's design stage
  refuses such a design. Hoisting them would rewrite the design to get past ls-sv; it waits for ls-sv instead.
  It passes `sim.py` at every `N` (Icarus).
* **verilog-axis `arbiter.v`** (alexforencich `48ff7a7e`, MIT): natively Moore, but it instantiates
  `priority_encoder` twice (the hierarchy route) over unpacked arrays (refused by the extractor).

So the goalpost is the own mask round-robin `reference/rr_mask.sv`, which the study's design note already
named as the first design to prove (the route of (e) without a tree). `check.py --unproved` passes it at
every stage that needs no proof: **769.488 µm², 2826 ps, 16 flops at `N = 8`** (MEASURED, sky130_a0_v3). It is
now the proved reference ((l)).

### (k) The site: hidden while the statement was a draft; listed directly, without a preview (decided 2026-11-05; the listing decided 2026-11-07)

While its statement was a draft, `site/config.json` listed the task `hidden`, as it then listed `matmul` and the
sorter; the listing `preview` (a task page that ranks nothing, with a status line) exists on the public export
branch only. Decided 2026-11-07: the task is listed directly (`listed`, open for submissions, ranked by area ×
period with `cycles = 1`, par the reference at 769.488 µm² × 2826 ps, about 2175 µm²·ns), with no preview
round, once its statement is final and the reference's record is seeded. Both held on 2026-11-07, when the
listing was decided (`site/config.json`; the record, now `84da5a4152db`, (n)). The curated texts are
`content/tasks/arbiter.md`, `.json` and `content/attacks/arbiter.json`.

### (l) The first proved reference is the own mask round-robin; the adapted OpenTitan tree is the next (decided 2026-11-05)

Real-world first was the rule for the choice, and both candidates are still out of reach of today's ls-sv
((j), F5): the adapted OpenTitan `prim_arbiter_tree` needs generate-local declarations, verilog-axis
`arbiter.v` needs the hierarchy route over unpacked arrays. Neither is rewritten to get past the tool. So the
reference is `reference/rr_mask.sv` itself, unchanged, proved for every `N` in range by
`reference/rr_mask.lean` along the route of (e). **The next reference** is `tests/arbiter/designs/arbiter_ot.sv`
as it is, once ls-sv instantiates generate-local `Var`/`LocalParam` declarations; its proof reuses the
reduction and the window argument unchanged, and needs the tree's priority lemmas by induction on the level
(JUDGED).

### (m) Where the proof's parts live (decided 2026-11-05)

* `SvGolf/React.lean` (untrusted, beside `SvGolf/Seq.lean`): what every reactive reference uses, namely
  `ReactTask.RankModel`, `ReactTask.satisfiedAt_of_rank`, `ReactTask.responds_of_rank` (moved from
  `Refute.lean`), `ReactTask.ghostAt_succ`, `mooreOut_of_combTargets`.
* `SvGolf/RoundRobin.lean` (untrusted): word-level facts any round-robin arbiter proof uses, for every width:
  `x & (~x + 1)` isolates the lowest set bit (`getLsbD_isolate`, `isolate_eq_twoPow`, `isolate_eq_zero`),
  `~((twoPow k << 1) - 1)` is the thermometer above `k` (`getLsbD_thermo`), the mask round-robin's `pick` and
  `next` with its one-step theorem `step` (the next mask is a thermometer and a requester that loses gets
  strictly closer to the edge in the cyclic distance `dist`, at most `N - 1`).
* `reference/rr_mask.lean`: everything about this netlist: the agreement `design.sem N = rrD N`, the comb
  settle of its one `always_comb` block (`settle_rr`: one pass computes the block, a second changes nothing),
  the clock step in closed form for any values (`rr_cycle`), the cycle on known values (`rrNext_reset`,
  `rrNext_run`), the invariant `ArbInv` and the rank model.

JUDGED: `pick`/`next`/`step` describe the mask policy, not this file's encoding (its `always_comb` form, its
signal names), so a golfer's mask round-robin with a different netlist reuses them; a golfer's other policy
(rotating priority, a tree, a matrix) uses the reduction and the lowest-set-bit lemmas only.

### (n) The task is `ready`; unranked while its statement was a draft, ranked once listed (decided 2026-11-05; ranking decided 2026-11-07)

`task.json` turns `ready` with the proved pair `reference/rr_mask.sv` + `rr_mask.lean` (no `draft_reference`).
It was unranked while its statement was a draft (2026-11-05 to 2026-11-07). Since 2026-11-07 the statement is
final and the leaderboard can record a clocked result (F9 is closed: the clocked record format,
`leaderboard/README.md`). The reference's record was seeded on 2026-11-07 (`leaderboard.py seed-references
--task arbiter`, the full check: `--postsynth full --ppa require --sandbox require`) and re-seeded on 2026-11-08
from the same files, the same way (`--require-clean`), after `score/ge_seq.json` took its neutral wording (the
prices unchanged; the old record pinned the table's old sha256, so it was stale): record `f45a50745d61`,
769.488 µm² × 2826 ps = 2174.57 µm²·ns, 16 flops, the reactive post-synthesis check at `N = 3, 5, 8` with 8
unsalted seeds each and 0 mismatches. MEASURED, against the record it replaces (`26ff615744bb`): score, `ppa`,
`postsynth` (every seed), canonical hash, files and the stored `.sv` and `.lean` equal; new: the GE table's
sha256, the two revisions, the build time, the date and the record hash. It was re-seeded once more on
2026-11-08, the same way, after the comment-only change that made the tx/stream half of `SvGolf/TaskSeq.lean`
final (the record names the sha256 of every statement file it was checked under, so it was stale): record
`c3633e51ea51`. MEASURED, against `f45a50745d61`: score, `ppa`, `postsynth` (every seed), canonical hash, files,
date and the stored `.sv` and `.lean` equal; new: the sha256 of `SvGolf/TaskSeq.lean`, of `check.py`,
`check/Comparator.lean` and `check/postsynth.py` (the per-point latency and the tx/stream power-up rule, which do
not touch a react-family check), the two revisions, the build time and the record hash. It was re-seeded again
on 2026-11-09, the same way, after the statement decisions of 2026-11-09 changed `SvGolf/TaskSeq.lean` (in
`TxTask` and `StreamTask` only: `done` = 0 before the first start, rule 1 with nothing exempt, no asynchronous
reset; no constant of the reactive statement changed, MEASURED by constant hashes): record `84da5a4152db`.
MEASURED, against `c3633e51ea51`: score, `ppa`, `postsynth` (every seed), canonical hash, files and the stored
`.sv` and `.lean` equal; new: the sha256 of `SvGolf/TaskSeq.lean` and of `check/postsynth.py` (the tx-family
`done` = 0 rule, which does not touch a react-family check), the two revisions, the build time, the date and the
record hash. It is par, and the task ranks once it is listed ((k)).

## 2. Findings

* **F1, the Mealy hole is open in the frozen kinds.** `SeqTask`, `TxTask` and `StreamTask` constrain the
  snapshot only; none requires the DESIGN to be Moore. The `last <= x; out = (x == last) ? good : bad` trick
  passes them too (DERIVED). The reactive check's Moore sample (i.3) would catch it there as well.
* **F2, no rely is needed** for arbiters: the window form makes the statement assumption-free.
* **F3, the bound and work conservation are both load-bearing**: without G3 the time-sliced ring A06 wins on
  area; without the tight `K` the fixed-priority family comes back.
* **F4, x-optimism and the dropped clock fields** (the study's review): closed here by KS and by the clocked
  source rules; since 2026-11-06 by the clocked statements' rules 2 and 3 in place of KS (§7).
* **F5, generate-local declarations** (MEASURED 2026-11-05, (j)): the most common real-world arbiter
  idiom, a tree whose nodes are declared inside generate loops, is outside ls-sv.
* **F6, a false rejection by the netlist lint** (MEASURED 2026-11-05): the correct rotating-priority arbiter
  `tests/arbiter/designs/rotate.sv` passes the reactive check at `N = 3` and `5` and is REFUSED at `N = 8`:
  the scored netlist keeps a dead public-named wire of a techmapped cell (`wire [3:0] \_269_.B`) with an
  undriven bit, and the post-synthesis check lints the netlist with Verilator, `UNDRIVEN` fatal. The same
  happened to a double-width-shift version of it (`\_33_.A`, at `N = 3` and `8`). Nothing reads those wires;
  `score/ppa.py` already reads them (`score/tests/ppa/idioms.json`), the post-synthesis lint does not. It
  concerns every kind (the combinational check lints the same way), so it is a checker change for review, not
  made here. CLOSED for the clocked kinds (decided 2026-11-07): the clocked flow `score/svgolf_seq.ys` ends with
  `opt_clean -purge`, which removes such wires and keeps every cell and port; `rotate.sv` is lint-clean at
  `N = 3, 5, 8` with unchanged gates and GE (310.294 GE, depth 13 at `N = 8`), and `rr_mask`'s netlists are
  byte-identical (MEASURED 2026-11-07; `score/PPA.md`, "Known gap"). The combinational flow is unchanged.
* **F7, the study's own designs met two refusals** before the property they test (MEASURED 2026-11-05): ls-sv
  refuses casts (`N'(1)`, `32'(p)`: `ConversionExpression:Explicit`), and the fourstate stage refuses a
  run-time index it cannot bound (`req[(p + k) % N]`). A03, A05, A06 now use the literal `1`; A09 and
  `designs/rotate.sv` scan a copy of `req` padded to `2^clog2(N)` bits. Each file says so in its header.
* **F8, the preview listing** (MEASURED 2026-11-05, on a scratch overlay of the public export branch's
  site code over this branch's tree, the arbiter listed `preview`): the site builds `--strict`, and the page
  shows the status line, the statement, "Nothing to compare yet" and the 17 attacks with their stages. Three
  of that branch's site tests assume a listed task has designs (the explorer and the score chart:
  `test_score_chart_and_explorer`, `test_the_explorer_offers_every_measured_point`,
  `test_charts_read_without_javascript`); a statement draft has none (its goalpost is not a reference). With
  the arbiter hidden, all 121 pass. A fourth (no task page names `Refute.lean`) is fixed in `Spec.lean`'s
  docstring. RESOLVED by the proved reference (MEASURED 2026-11-05, the same overlay with this branch's
  current files): with the arbiter listed `preview`, all 121 pass (1 skipped), so listing it as a preview on
  the export branch is one line of its `site/config.json` and needs no test change.
* **F9, the leaderboard cannot record a clocked result** (MEASURED 2026-11-05, `leaderboard.py`
  `acceptance_problems` on a clocked `stages.postsynth`): it wants `stages.postsynth.vectors`, and a clocked
  check writes `points` (one record per point, `run_clocked`); the record's `postsynth` has no clocked form
  either. This holds for every clocked kind (matmul and the sorter included), so no clocked task can be
  ranked through `leaderboard.py add` yet. Not changed here (a record-format decision). MEASURED again on the
  proved reference (2026-11-05): its accepted `check.py` result fails `acceptance_problems` with exactly one
  problem, "the post-synthesis check did not pass (no `stages.postsynth` record with mismatches 0 …)", so
  `leaderboard.py seed-references --task arbiter` cannot seed its record. The change it needs: for a
  `CLOCKED_KINDS` task, accept `stages.postsynth.points` (every point in full mode, every seed run, 0
  mismatches) and give the record's `postsynth` a clocked form (the points and their cycles). CLOSED 2026-11-07
  (decided: the clocked record format, `leaderboard/README.md`): acceptance requires the clocked flow's result
  and `stages.postsynth.points` in full mode, the record keeps the points and their seeds, and the board, `verify`
  and the site compare a record only with the flow of its own kind.

* **F10, ls-sv has a closed-form clock step for FF-only designs only** (MEASURED 2026-11-05, by the proof):
  `cycleStep2_ffOnly` / `cycleStep2_profile` need every process to be an edge process, and the mixed profile
  (`cycleStep2_mixedProfile`) gives termination only, no closed form. The reference has one `always_comb`
  block, so it proves its own comb settle (`settle_rr`: one pass computes the block from `req` and `mask`,
  which it does not write; the second pass is the identity, so the settle loop's `==` test ends it) and its own
  cycle (`rr_cycle`), about 150 lines. A library form (a comb block that writes none of the signals it reads,
  settled in two passes, under every schedule) would serve every clocked reference with combinational logic
  (JUDGED: the ls-sv library).
* **F11, `sv2_inst_simp` stops at a comparison with a fill** (MEASURED 2026-11-05): `mreq != '0` instantiates
  at the width `maxW2 (selfWidth mreq) (selfWidth '0)` = `maxW2 (some N) none`, and ls-sv's private `maxW2` has
  a simp lemma for two known widths only (`maxW2_some`), so the fill's width and the comparison stay
  unevaluated for a symbolic `N`. The reference states the lowering once (`inst_ne_fill`, proved by unfolding
  `instExpr2` and `rfl`) and passes it to the tactic as a pre-lemma. The robust fix is in ls-sv: `@[simp]`
  lemmas `maxW2 (some a) none = some a`, `maxW2 none (some b) = some b`, `maxW2 none none = none` beside
  `maxW2_some` (`LeanModels/Sv/Param2.lean`). Not changed here (the library's file); the design was not
  rewritten.

## 3. The attacks (17), each with the clause it breaks and where the pipeline rejects it

MEASURED 2026-11-05: `tests/arbiter/sim.py --cycles 4000` (Icarus 4-state; `N = 1, 2, 3, 4, 5, 8` × 3
stimulus modes; every expectation met; `MO` is the silicon check `MooreOut` guarantees; since 2026-11-07 each run
starts from a 0/1 power-up state, the `KN` check is gone and a fourth, sparse mode runs: A16 now fails, the other
columns are unchanged, MEASURED 2026-11-07; since the review's F1, the same day, a power-up copy that leaves a
flip-flop bit without a 0/1 value is an error and the harness self-check `XK`, an unknown `gnt` after a power-up,
fires for none of these designs, MEASURED), and `check.py
--unproved` on each attack (a wrong design has no proof to submit it with), whose
stage `tests/run.py` pins (`tests/expected.json`, with a phrase of the rejection). The Lean column names a
kernel-checked refutation of the hand-built `Design2` twin (`tests/arbiter/negative/Refute.lean`, `N = 2`).

| id | design | simulation: checks that fire | check.py --unproved: rejected at | statement conjunct | Lean |
|---|---|---|---|---|---|
| A01 | never grant | G3, G4 (all N) | postsynth: G3 | Follows | `never_refuted` |
| A02 | grant every requester | G1 (N ≥ 2) | postsynth: G1 | Follows | `everyone_refuted` |
| A03 | always grant client 0 | G2 (all N), G4 (N ≥ 2) | postsynth: G4, G2 | Follows | `zero_refuted` |
| A04 | fixed priority, lowest wins | G4 only (N ≥ 2) | postsynth: G4 | Follows | `fixed_refuted` |
| A05 | free-running token ring, `gnt = token` | G2 (all N) | postsynth: G2 | Follows | |
| A06 | time-division: token ring gated by `req` | G3 only (N ≥ 2) | postsynth: G3 | Follows | |
| A07 | correct RR decision delivered one cycle late | G2, G3, G4 | postsynth: G3, G2 | Follows | |
| A08 | sticky RR: priority stays AT the granted client | G4 only (N ≥ 2) | postsynth: G4 | Follows | |
| A09 | rotating priority, counter wraps at `2^⌈log2 N⌉` | G4 at N = 3, 5 only (G3 at 5); PASSES at 1, 2, 4, 8 | postsynth: G4 at N = 3 | Follows (∀ N) | |
| A10 | correct registered grant behind `gnt = (req == last) ? g : req` | MO only | postsynth: the Moore sample | MooreOut | `mealy_refuted`, `mealy_silicon` |
| A11 | RR whose grant flop has no reset branch | G0 | postsynth: G0 on the netlist (since 2026-11-06; before, ls-sv's gnt x in the reset snapshot) | Follows (G0) | |
| A12 | mask RR that forgets the mask on the wrap-around grant | G4 only (N ≥ 2) | postsynth: G4 | Follows | |
| A13 | RR with an asynchronous reset (`posedge rst`) | MO at reset entries | source (the clocked rules) | Disciplined (`ClockedBy clk none` refuses the `alwaysFFR` the loader keeps) | |
| A14 | combinational (Mealy) RR, mask registered | MO, G0, G4 (N ≥ 3) | postsynth: the Moore sample, G0 | MooreOut | |
| A15 | RR arbitrating every other cycle | G3, G4 | postsynth: G3 | Follows | |
| A16 | correct RR behind `if (!u)` on a never-reset, self-holding `u` | NONE from Icarus's x start; G4 (N ≥ 2) from 0/1 power-ups (2026-11-07: from `u = 0`) | score: the never-loaded register (since 2026-11-06; before, postsynth: the netlist is not ls-sv) | Follows (from `u = 0`; KS until 2026-11-06) | `xopt_refuted`, `a16_refuted` |
| A17 | RR for 4095 cycles after a reset, then fixed priority | NONE (resets every ~256) | postsynth: G4 in the 70000-entry segment, after entry 4095 | Follows (G4) | |

Correct designs (must pass, and do, MEASURED): the goalpost `reference/rr_mask.sv` (check.py --unproved and
simulation), `tests/arbiter/designs/rotate.sv` (rotating priority, a different policy: simulation at every
`N`, the reactive check at `N = 3, 5`; F6 at `N = 8` until 2026-11-07, at all three since `-purge`), `tests/arbiter/designs/arbiter_ot.sv` (the adapted
OpenTitan tree: simulation at every `N`; F5 in ls-sv). Max wait 7 at `N = 8` for all three.

## 4. Golf space at the scoring point

| design (Moore) | N | area µm² | period ps | flops | source |
|---|---|---|---|---|---|
| `reference/rr_mask.sv` (the goalpost) | 8 | **769.488** | **2826** | 16 | MEASURED 2026-11-05, check.py's clocked score, sky130_a0_v3 |
| OpenTitan tree + output register (own wrapper, two modules) | 8 | 668.1 | 1454 | 15 | the study, `score/ppa.py --seq`, sky130_a0_v2 |
| rotating priority (the study's first version) | 8 | 1327.5 | 3148 | 11 | the study, sky130_a0_v2 |
| (attack A04, fixed priority: unfair) | 8 | 289.0 | 888 | 8 | the study, sky130_a0_v2 |

The tree is smaller and faster than the mask design, and the rotating design has the fewest flops but the
most logic: a real area/period frontier (JUDGED: matrix/LRU, one-hot vs binary pointer and parallel-prefix
variants are the next points). Fixed priority is the floor a cheat would aim at.

## 5. What `tests/run.py --only arbiter` runs

* `layout`: task.json against the schema (a ready task: the proved reference pair),
  tests/expected.json lists the 17 attacks on disk, `tasks.lean` / `tests.lean` import the Spec and the Refute.
* `build`: `lake build` of SvGolf (with `SvGolf.TaskReact`), tasks (with `tasks.arbiter.Spec`) and tests (with
  `tests.arbiter.negative.Refute`).
* `unit`: `tests/checker/test_clocked.py` (the kind, the goal, the clocked source rules on A13) and
  `tests/checker/test_clocked_post.py` (the goalpost passes the reactive check at a small point; a Mealy
  output, an unreset grant, fixed priority and a time bomb each fail on their own clause; the salt moves the
  stimulus).
* `references`: the reference through `check.py` with its proof: ACCEPTED, the reactive record at the scoring
  point and the three points in full mode, no unsupported construct at any probe point, the ranked score
  equal to tests/expected.json's.
* `negatives`: `negative/bit_ring.sv` and `negative/reset_edge.sv` (2026-11-06) through `check.py` with the
  reference's proof, rejected at `solution` (their kernel refutations are in `Refute.lean`); the other wrong
  designs are refuted in `Refute.lean` and pinned as attacks.
* `validate`: `tests/arbiter/sim.py --cycles 4000` (`--full`: 20000), with the harness's own regression
  `tests/arbiter/selftest/alias_ptr.sv` (section 8, F1).
* `attacks`: the 17 attacks through `check.py --unproved`, each rejected at its stage with its phrase.

MEASURED 2026-11-05, `tests/run.py --only arbiter`, one step per run through the shared Lean slot: layout 27
checks, 0 failed; build 1 (73 jobs, 82 s); unit 24, 0 failed (the site tests included, 655 s); leaderboard
PASS; drafts 2, 0 failed (the goalpost at N = 3, 5, 8: 210 519, 210 683, 211 527 cycles over 3 seeds, 0
failures; its score equal to tests/expected.json's); validate 2, 0 failed; attacks 17, 0 failed (549 s). And
`site/build.py --offline --strict`: built.

MEASURED 2026-11-05, after the task turned `ready` (`tests/run.py --only arbiter`, one step per acquisition of the
shared Lean slot): build 1, 0 failed (73 jobs, 61 s: SvGolf with `SvGolf.React` and `SvGolf.RoundRobin`, tasks,
tests with the shortened `Refute.lean`); layout 27, 0 failed; references 5, 0 failed (accepted in 85 s; the
reactive record at `N = 3, 5, 8` in full mode, 3 seeds each, 210 519, 210 683, 211 527 cycles, 0 failures; no
unsupported construct at the 5 probe points; the sky130 block consistent; the score equal to
tests/expected.json's). And `site/build.py --offline --strict`: built (the arbiter hidden). On a scratch overlay
of the public export branch's site code over this branch's tree with the arbiter listed `preview`, the site builds
`--strict` and its 121 site tests pass (1 skipped): the three that failed while the task had no design (F8) pass
now that it has its reference.

MEASURED 2026-11-05, the proved reference:
`check.py tasks/arbiter reference/rr_mask.sv reference/rr_mask.lean --postsynth full` ACCEPTS it in three cold
runs (a fresh `--stage-dir` each, one run per acquisition of the shared Lean slot, load average 7.4, 8.8 and 10.1
at the start): **solution 8.25, 11.08 and 9.41 s** (limit 120 s; `score/time_limits.json`), comparator 18.8 to
34.3 s, leanchecker 16.3 to 21.0 s; in the first, trusted 2.7 s and design 5.2 s (the 5 probe points free of
unsupported constructs) and the reactive post-synthesis check at `N = 3, 5, 8` in full mode, 3 seeds each,
70 134 to 70 597 cycles per seed, 0 failures; the score 769.488 µm² × 2826 ps, equal to tests/expected.json's.
Axioms `propext`, `Classical.choice`, `Quot.sound`. **Heartbeats**: 51.4 million for the whole proof, elaborated
synchronously with a counter around each of its 86 declarations; the largest are `comb_admits` 12.9 M (the
self-read guard at a symbolic width), `ff_run` 5.7 M, `comb_run` 5.1 M, `rr_driversOk` 4.6 M, each far under
the default limit of 200 M per declaration. A run of the same check at load average 76 (other users' jobs on
the shared machine) exceeded the limit (the solution stage killed after 120 s, 255 s wall clock): the proof is
quick, the limit is on wall-clock time.

MEASURED 2026-11-06, the reference RE-PROVED against the revised statement (the clocked statements' rules 2 and 3, §7; the
design unchanged): `check.py tasks/arbiter reference/rr_mask.sv reference/rr_mask.lean --postsynth full` ACCEPTS
it (a fresh `--stage-dir`, one acquisition of the shared Lean slot, load average 9.0 at the start, 113 s wall
clock): trusted 1.7 s, design 4.6 s, `clocked_rules` (the rule-3 twin) no finding at the 5 probe points,
**solution 4.79 s**, comparator 13.3 s, leanchecker 15.3 s, the `score` stage's never-loaded check no flop
removal, and the reactive post-synthesis check at `N = 3, 5, 8` in full mode from power-up states (seed 0 all
zeros, seeds 1 and 2 random, on the netlist and on ls-sv), 70 134 to 70 597 cycles per seed, 0 failures; the
score 769.488 µm² × 2826 ps, 16 flops, unchanged. Axioms `propext`, `Classical.choice`, `Quot.sound`. The proof
changed by +41 / -11 lines (`rr_powerUp`: every power-up state has the shape, by `powerUp_cons` once per
declaration; `rr_terminates` by `TerminatesPU.of_invariant`; `rr_xsafe`, `xsafeB` by `simp`; the rank model
lost its `known` field; `Interface` gained the distinct names, by `decide`). **Heartbeats**: 53.3 million for
the whole proof (51.4 million before), the same per-declaration counter around each of its 89 declarations; the
new and changed ones `rr_xsafe` 1.37 M, `model` 1.18 M, `rr_powerUp` 0.46 M, `rr_interface` 0.44 M,
`rr_terminates` 0.12 M, `solution` 0.04 M; the largest is still `comb_admits`, 12.8 M.

MEASURED 2026-11-07, after the merge round onto the rules of 2026-11-06 (one limit of 300 CPU s for every task,
run-time `/ % **` banned in every task, the range `1 <= N, N*N < 2^31`; the design and the proof unchanged):
three cold `check.py --no-score` runs (a fresh `--stage-dir` each, one acquisition of the shared Lean slot per run,
load average 4.3, 6.0 and 4.8 at the start): **solution 12.56, 12.71 and 11.18 CPU s** (9.75, 9.67 and 4.12 s of
wall clock; limit 300 CPU s; `score/time_limits.json`). `check.py tasks/arbiter reference/rr_mask.sv
reference/rr_mask.lean --postsynth full --ppa require` ACCEPTS it (solution 18.75 CPU s in 53.8 s of wall clock
on a busier machine): `clocked_rules` no finding, the reactive post-synthesis check at `N = 3, 5, 8` in full mode,
3 seeds each, 70 134 to 70 597 cycles per seed, 0 failures; the score 769.488 µm² × 2826 ps, 16 flops, unchanged.

## 6. Not done

* The real-world reference ((l)), once ls-sv instantiates generate-local declarations (F5).
* `load_sv` refutations of the SystemVerilog attacks (the Lean refutations use hand-built twins).
* The ls-sv generate-local declarations (F5), outside this task's files. (The netlist-lint false rejection,
  F6, is closed for the clocked kinds since 2026-11-07: `opt_clean -purge` in the clocked flow.)
* DONE since 2026-11-07: the reference's leaderboard record (`84da5a4152db` since its third re-seed on 2026-11-09, par)
  and the site listing ((k),
  (n)).
* DONE since 2026-11-06: the refusal register `docs/sv-refusals.json` of Proglib (formerly lean-surfaces),
  which generates `REFUSALS.md`, cites this task's 17 attacks, its 2 negatives and the mutants m004 and m007, and has rows for
  the never-loaded and `clocked_rules` refusals of every clocked kind; `tools/gen_sv_refusals.py --check` (a
  nightly repository check) passes (MEASURED 2026-11-07: 210 ls-sv entries, 78 svGolf entries; it failed with
  19 errors on 2026-11-06).
* DONE since 2026-11-13: the six register rows below, which this task's refusals rest on, are in this repository's
  `REFUSALS.md`. `REFUSALS.md` is what the refusal register of the pinned Proglib revision renders (the revision
  `lakefile.toml` and `lake-manifest.json` require); the pin moved from `bb5e58e0` to `178529f1`, which is
  `bb5e58e0` with the refusal register's newer rows and no other change (no Lean file, no extractor file), so no
  proof is checked against anything new. The rows are:

  | register row | what is refused | where |
  |---|---|---|
  | `sg-react-guar` | a reactive controller that misses the `ReactTask` guarantee: from some power-up state, a reset snapshot that does not show `atReset`, an unsafe cycle, an obligation triggered at `K + 1` consecutive entries and answered in none of them, or an output in the combinational cone of an input | the statement (`SvGolf/TaskReact.lean`, `ReactTask.Guar`); the reactive post-synthesis check (`check/postsynth.py`) |
  | `sg-clocked-edge` | (clocked tasks) an edge process other than `always_ff @(posedge <clock>)`: an asynchronous reset or a second clock in its sensitivity list, a `negedge`, `edge` or level-sensitive event, an `iff` guard on the clock, a clock other than the task's | the source gate (`score/srcgate.py`) |
  | `sg-clocked-rules` | (clocked tasks) an x-creating construct, refused before the proof by the twin of rule 3 (`XSafe`) | the stage `clocked_rules` (`check/clocked_rules.py`) |
  | `sg-never-loaded` | (clocked tasks) a never-loaded register: a flip-flop the pinned flow removes while reads of it remain | the `score` stage (`check.py`, `score/score.py`) |
  | `sg-never-loaded-mem` | (clocked tasks) a never-loaded memory lane: a bit lane of an unpacked array that no write loads, read | the `score` stage |
  | `sg-fsm-backstop` | (clocked tasks, a backstop) a state register re-implemented by Yosys's fsm pass, which the clocked flow does not run (`synth -nofsm`) | the `score` stage |

  The same pin brought the register's stage `clocked_rules` and group `g-clocked`, the newer text of eleven
  existing rows, and four rows that are not this task's own: `sg-ban-div-any` (a run-time `/ % **` in any
  task), `sg-ban-cmp` (a run-time ordering comparison in a task that bans `+` or `-`) and `sg-loopfree` (a
  combinational loop or a latch, the statement's `LoopFree`), which the svGolf README's Rules and The banlist
  describe, and `sg-txstream-moore` (an output of a transaction or stream task in the combinational cone of an
  input port, the reset included: the clocked statements' rule 1, `MooreOutDep d []`, nothing exempt since 2026-11-09),
  which the matmul and sorter READMEs describe as rule 1 (the sorter's attack `rst_gate` is its example).

## 7. The clocked statements' rules in the kind (2026-11-06)

The rulings of 2026-11-06 (svGolf README, "Rules": a design is valid when every admissible initial state,
input sequence and nondeterministic choice gives permitted behaviour; an `x` is an unknown 0/1 value; the
pinned Yosys is disallowed where it deviates from the semantics) and the second clocked statement's revision 3
(`design/soundness/TXTASK-V2-REVIEW.md`) are ported to `ReactTask`, with that statement's definitions
(`SvGolf/TaskSeq.lean`) and its x-free lemma (`SvGolf/XFree.lean`), no copies.

The statement diff (`SvGolf/TaskReact.lean`, definitions only):

```lean
-def KnownAt (clk : String) (tr : List SvState) (c n : Nat) : Prop := …      -- removed
-def Known (tr : List SvState) (c n : Nat) : Prop := KnownAt t.clk tr c n   -- removed
 def Interface (p : P) (d : Design2) : Prop :=
   inputPorts d = (t.clk, 1) :: (t.rst, 1) :: t.inputs p ∧ outputPorts d = t.outputs p ∧
+    (d.decls.toList.map Decl.name).Nodup
 def Follows (p : P) (K : Nat) (d : Design2) : Prop :=
-  d ⊨₂ spec2 fun stim tr =>
+  ModelsPU d fun stim tr =>
     ∀ c1 x0 xs, Released t.rst stim c1 (c1 + xs.length) → t.InsAt p stim (c1 - 1) (x0 :: xs) →
-      t.Known tr (c1 - 1) (xs.length + 1) ∧
       ∃ y0 ys, ys.length = xs.length ∧ t.ShowsAt p tr (c1 - 1) (y0 :: ys) ∧ t.Guar p K xs y0 ys
 def SatisfiedAt (p : P) (K : Nat) (d : Design2) : Prop :=
-  t.Interface p d ∧ (t.Disciplined d ∧ Terminates2 d) ∧ t.Follows p K d
+  t.Interface p d ∧ (t.Disciplined d ∧ TerminatesPU d) ∧ t.Follows p K d ∧ XSafe d
```

* **Rule 2** (`ModelsPU`, `TerminatesPU`): the claims and termination hold of every run from EVERY power-up
  state (every declared signal, 2-state ones included, at some 0/1 value of its width, one value for all its
  reads), under every schedule, on every known stimulus, replacing the one run from `initState2`. The first
  reset edge reads the power-up values.
* **Rule 3** (`XSafe`): no construct that can create an `x` from known operands. With rule 2, every value of
  every run is known (`ReactTask.snapshots_known`, by `xfree_runsAt`), so v1's known-state clause KS would
  only restate it, and it is removed.
* **Rule 1 is not added.** `MooreOut` (the kind's `OutDiscipline`) already forbids every combinational path
  from an input port, the reset included, to an output port, per process: more conservative than
  `MooreOutDep`, which follows each assignment's reads. The task's observation is Moore by decision
  (2026-11-05), so it does not permit a combinational grant, and needs no second rule.
* **Distinct declaration names** (`Interface`, DERIVED, found while porting): `KnownEntry` reads an input's
  width from the FIRST declaration of its name (`sigWidth`), so a design with an earlier, differently wide
  declaration of a port's name has no known entry that drives the port, and `ModelsPU` holds vacuously for it:
  with the claims empty, such a design meets the statement at every bound, `bound_tight` fails, and so would a
  never-granting arbiter. The kind requires distinct names (every loaded design has them: SystemVerilog
  forbids the redeclaration, and the loader refuses it in a flattened hierarchy at the defaults); with them,
  `knownEntry_of_interface` gives the known entry every refutation needs. The same reading of `KnownEntry` is
  in the clocked statement's three kinds; their `Interface` asks for distinct names too since 2026-11-06 (`SeqTask`,
  `TxTask` and `StreamTask` took this conjunct, decided 2026-11-06: design/soundness/TXTASK-V2-REVIEW.md section
  12.2, M3), so all four clocked kinds read it the same way.

What it closes (the universal-correctness audit's findings on this task):

| finding | the wrong design | v1 | now |
|---|---|---|---|
| F1, the power-up never quantified | `negative/bit_ring.sv`: a never-reset 2-state ring `u`, fixed priority when `&u` | accepted (ls-sv starts a 2-state `u` at 0) | refuted from `u` all ones (`ring_refuted`) |
| F2, the first reset edge reads pre-reset values | `negative/reset_edge.sv`: `bad` set at the reset from the pre-reset `&u` | accepted (the edge read `x`, `if (x)` took the else branch) | refuted from `u` all ones (`reset_edge_refuted`) |
| M3, an `x` laundered into a known 0 by a 2-state target | (DERIVED: `bad <= &u` with a 2-state `bad`) | accepted (`&x` = `x`, squashed to 0) | no run computes an `x` (rule 3, `xfree_runsAt`), so the squash only meets 0/1 values: the design is checked from every power-up of `u` |
| M1, a run-time `/`, `%`, `**` | (the audit's division design) | an `x` inside a decision | refused by rule 3 (a divisor must be a nonzero constant), and by the clocked rule-3 twin before the proof |
| A16, x-optimism | `attacks/a16_xopt.sv`: `if (!u)` on `u <= u` | rejected by KS | refuted from `u = 0` (`a16_refuted`, `xopt_refuted`); the checker refuses the never-loaded `u` at `score` |

The pipeline beside the statement: `check.py` runs the rule-3 twin (`clocked_rules`) and the never-loaded
check (`score`, `never_loaded`) for `react-family` as for every clocked kind; the reactive post-synthesis
check starts the netlist and ls-sv from power-up states (seed 0 all zeros on both sides, seeds 1 and 2
random), as the transaction kinds' check does. The never-loaded rule refuses a register the pinned flow
removes by `D = Q` while it is read (A16, MEASURED at `N = 3` and `8`; the goalpost's self-holding mutant of
`tests/checker/test_clocked_post.py`); it is the svGolf-side disallowance of that Yosys deviation, since ls-sv
gives a register one power-up value for every read. An undriven net is its combinational analogue, which the
`fourstate` stage's undriven check refuses. Since the adversarial round on those rules (2026-11-06,
design/soundness/TXTASK-V2-REVIEW.md section 12) the same check also refuses an array lane no write loads (opt_mem
connects its reads to an undefined value before any flop exists: the reference plus an unwritten `m [0:1]` read
at a constant index, decided both ways at `tick == 2^17 - 1`, passed every stage before and withheld the grant at
entry 131071, MEASURED); a state register the fsm pass re-implemented (its new flops powered up in codes that are no
value of the register: the same arbiter with a never-reset 2-bit state, MEASURED likewise) is no longer possible,
since the clocked flow runs `synth -nofsm` (decided 2026-11-06, TXTASK-V2-REVIEW.md section 12.2, M2; the
"Mapping FSM" refusal stays as a backstop that should never fire). Under the new flow the comparisons that arbiter's state
feeds fold to 1, its scored netlist (`N = 8`) is the reference's 16 flip-flops, and it agrees with ls-sv at every
cycle from five power-ups each (MEASURED, section 12.2); `check.py --unproved` passes it through `score` and stops
at `postsynth`, where the `N = 3` netlist's `case (s)`, a techmapped `$pmux`, leaves a dead, partly undriven wire
that Verilator's lint refuses (MEASURED: the over-rejection section 12.2 records for the counter's FSM fixtures, not
decided). The reference scores exactly as before (MEASURED: the same score record and byte-identical netlists at
`N = 3, 5, 8`). The
reactive check compares the netlist with ls-sv bit for bit only from the same all-zeros start: a reactive
guarantee admits several grants, so the reference with its mask not reset, correct from every power-up, shows
different legal grants from different power-ups and was rejected at `postsynth` ("seed 2, cycle 1: gnt: the
netlist (100) is not ls-sv (001)", MEASURED); from the random starts both runs are now held to the guarantee
(`test_clocked_post.py` `test_an_unreset_mask_passes_the_reactive_check`).

What the port does not close: the clocked statement's dependencies, which the kind shares
(design/soundness/TXTASK-V2-REVIEW.md sections 7 and 11.7). W4 (ls-sv validates a `unique`/`priority` case
on the snapshots): the source gate refuses the qualifiers. W5 (ls-sv reads every dynamic index unsigned):
rule 3 refuses an index that mentions a signal declared signed, and a `$signed` cast or a signed literal
inside an index, which the loaded design does not show, is refused only by `fourstate` (d). An undriven
variable, which rule 2 reads as a power-up value that never changes and Yosys as undefined, is refused only
by `fourstate` (e). Obligation C (the netlist equals ls-sv on defined values) stays sampled: the reactive
check compares the two bit for bit at seed 0 only (when the two zero starts agree) and holds both to the
guarantee at every seed, on the sampled stimulus.

MEASURED 2026-11-06, `tests/run.py --only arbiter`, every step, one step per acquisition of the shared Lean
slot (the tree at the commits of this section): layout 27, 0 failed; build 1, 1 failed: `lake build` stops at
`tests.add.negative.Refute`, `tests.mul.negative.Refute` and `tests.clmul.negative.Refute`, whose `only_n16.sv`
the loader refuses (`PDesign.int32Agrees`), a failure inherited from the development branch's ls-sv through a merge (the
same three fail on both branches merged; every other module builds,
`tests.arbiter.negative.Refute` and `SvGolf.React` included); unit 24, 0 failed (551 s: `test_clocked_post.py`
with the goalpost's mutants, G0 for the unreset grant, `score` for the self-holding register; `tests/site`
OK, 1 skipped); comparator 3, 0 failed (`test_xsafe_twin.py`: the twin and `xsafeB` agree on all 20 of the
arbiter's designs at `N = 1, 2, 3, 5, 8`, every one admitted, and on the three twins); leaderboard 2, 0 failed;
modes, canon, drafts, baselines, sandbox: nothing for this task; references 5, 0 failed (accepted in 75 s, the
reactive check at `N = 3, 5, 8` from power-up states, 210 519, 210 683, 211 527 cycles over 3 seeds, 0
failures; the score equal to tests/expected.json's); negatives 2, 0 failed (`bit_ring`, `reset_edge` at
`solution`); ppa 11, 0 failed; validate 2, 0 failed; attacks 17, 0 failed (374 s: A16 at `score`, the
never-loaded register `u`; A11 at `postsynth` on G0; A13 at `source`; the others at `postsynth` as before).

## 8. The mutation sweep (2026-11-07)

Every generated mutant of the reference must be killed by the task's checks or proved equivalent, with a
kernel-checked sample (required of a clocked task before it opens, decided 2026-11-06).

* **Generation** (`tests/mutate.py`, reusable: any source, any parameter points, `--selftest`): the
  mutation points are nodes and tokens of Slang's syntax tree (pyslang 11.0.0, the extractor's frontend),
  never the source text. Operators: relational, arithmetic, bitwise, shift and logical swaps; unary deletion
  and replacement; constant +1, -1 and bit flips (the parameter default, the declared ranges: index
  off-by-one, the shift amount: shift off-by-one); condition negation; branch swap; stuck-at-0/1 on every
  signal read; deletion of one assignment; the reset values; operand swap of non-commutative operators.
  MEASURED on `reference/rr_mask.sv`: **104 generated, 4 textual duplicates, 0 that do not elaborate**
  (pyslang at `N = 1, 2, 3, 4, 5, 8`), **100 kept**.
* **Classification** (`tests/arbiter/mutants/classify.py`, results in `tests/arbiter/mutants/MANIFEST.json`
  and `.txt`): the simulation statement (`sim.py`'s `run`, `tb.sv`, `N = 1, 2, 3, 4, 5, 8`, 3 modes, 20000
  cycles); `check.py --unproved --postsynth full` once per mutant; the reactive check alone at each `N`
  where the simulation is silent; and, at `N = 1, 2, 3, 4, 8`, two UNBOUNDED model checks on Yosys's reading
  of the RTL with every flip-flop powering up free (`write_aiger -zinit`): equivalence with the reference
  from the first reset entry on, and G0 to G4 by a monitor (ABC `pdr`, every proof confirmed by ABC `int`).
  The monitor was first run on the 17 attacks, the two negatives and `designs/rotate.sv` (MEASURED): it
  falsifies every wrong one at every `N` where it is wrong (A09 at `N = 3` only; A17 at depth 4097 at
  `N = 2, 4`, undecided in 600 s at `N = 3, 8`), proves `rotate.sv` at every `N`, and the two Mealy attacks
  are the ones flagged non-Moore.

| verdict (MEASURED) | N = 1 | N = 2 | N = 3 | N = 4 | N = 8 |
|---|---|---|---|---|---|
| KILLED (the simulation at `N`, or check.py: a submission is the whole family) | 85 | 85 | 85 | 85 | 85 |
| EQUIVALENT (proved at `N`) | 13 | 9 | 9 | 9 | 9 |
| SURVIVOR, correct at `N` (G0 to G4 proved, not equivalent) | 0 | 4 | 4 | 4 | 4 |
| SURVIVOR, wrong at `N` | 2 | 2 | 2 | 2 | 2 |

check.py's stages (MEASURED): `postsynth` 74 (73 at `N = 3`, one at `N = 5`: m099, equivalent to the
reference at `N ≤ 3`; 73 on the guarantee read on the netlist's grants, one, m076, on Verilator's lint of
the netlist), `design` 8 (two loader refusals of `[N-2:0]` ports at `N = 1`; six `if`/`?:` conditions
made of fills alone, `if ('0)` or `'0 != '0`, whose width ls-sv refuses to guess: `Fill:width`), `fourstate` 2 (an
assignment of the comb block deleted: an undriven variable), `unproved` (every no-proof check passed) 16.
The 9 equivalents at `N ≥ 2`: the parameter default ±1, the internal vectors one bit wider, `!=` as `>`
twice, `<<` as `<<<`, and the mask's reset value as `'0`, `1` or `'1 >> 1` (each still makes the first
grant the lowest requester).

**Survivors** (DERIVED from the proofs and counterexamples; the manifest has the rest):

* **m004, m007: a port one bit wider** (`input logic [N-0:0] req`, `output logic [N-0:0] gnt`). WRONG at
  every `N` (`Interface`), and no proof can exist; but the simulation, every stage of `check.py --unproved`
  and the reactive check at every `N` pass them: nothing before the proof compares the ports with
  task.json's `ports` (the harnesses drive what the netlist has, and the oracle never sets the extra bit).
  Proposed fix (for the maintainers): the `extract` or `design` stage refuses a top module whose ports at a probe
  point differ from task.json `ports` (names, directions, widths), for every kind. DONE 2026-11-07 (decided):
  the `extract` stage compares them (check.py `port_problems`); m004 and m007 are attacks rejected there
  (tests/expected.json `m004_wide_req`, `m007_wide_gnt`, `tests/arbiter/mutants/m004.sv`, `m007.sv`), and so are
  the four `[N-2:0]`-port mutants m003, m005, m006, m008 (before: the loader, at `design`, at `N = 1`).
* **m070, m072** (the mask's reset value `~('1 >> 1)`, `~1'b1`), **m083, m086** (`pick != '0` as `>=` or as
  `!= '1`: the mask is also cleared when nobody is granted): CORRECT, G0 to G4 proved at `N = 2, 3, 4, 8`
  (the first grant after a reset may differ from the reference's, a legal policy). Not findings.
* Two correct mutants are KILLED: **m067** (the mask's reset deleted, the case the second statement's review accepted)
  only by `tb.sv`'s `KN` check, a four-state artifact (the unreset mask is `x` in Icarus) that the statement
  no longer has (rule 3); and **m085** (`if ('1 != '0)`) by ls-sv's loud `Fill:width` refusal. Proposed fix
  for the first: run `tb.sv` from 0/1 power-up states (as the post-synthesis check does) and drop `KN`. DONE
  2026-11-07 (the re-run below: m067 survives, correctly).
* The simulation misses one wrong mutant at `N = 5, 8`: **m040** (`-mreq` for `~mreq`: no grant when client
  0 is the only masked requester), whose failing input, client 0 alone right after a reset or the wrap, is
  rare under `tb.sv`'s stimulus; check.py rejects it at `N = 3`, and the reactive check alone rejects it at
  every `N` (the oracle's `single` and `sparse` segments). DONE 2026-11-07: `tb.sv`'s sparse mode catches it at
  every `N` (the re-run below).

**Re-run (2026-11-07, after S3's checker round; MEASURED).** Three findings above were acted on: the `extract`
stage compares the ports with task.json's (F-a, every kind); `tb.sv` runs every design from a 0/1 power-up state
(`sim.py` `powerup`: Yosys's reading with every flip-flop and undriven variable set, all zeros in mode 0, seeded
random in the others), without the `KN` check, and with a fourth, sparse mode (one client alone or nobody, a reset
every 16 entries). With them, the clocked flow's `opt_clean -purge` and F5's 8 salted seeds per point, the sweep was
re-run (`gen` and `formal` reused: the mutants and Yosys's reading are unchanged; `sim`, `check` and `point`
anew; `tests/arbiter/mutants/MANIFEST.json` and `.txt` are this run's):

| verdict (MEASURED 2026-11-07) | N = 1 | N = 2 | N = 3 | N = 4 | N = 8 |
|---|---|---|---|---|---|
| KILLED | 86 | 86 | 86 | 86 | 86 |
| EQUIVALENT (proved at `N`) | 14 | 9 | 9 | 9 | 9 |
| SURVIVOR, correct at `N` | 0 | 5 | 5 | 5 | 5 |
| SURVIVOR, wrong at `N` | 0 | 0 | 0 | 0 | 0 |

What moved, and nothing else (the old and the new manifest compared mutant by mutant): m004 and m007 are KILLED
at `extract` (no wrong survivor is left); m003 and m005 move from `design` and m006 and m008 from `postsynth` to
`extract` (their `[N-2:0]` ports are not the task's at any point); m067 is no longer killed (the simulation is
silent from 0/1 power-ups; G0 to G4 proved): a correct SURVIVOR at `N >= 2`, EQUIVALENT at `N = 1`; m040 is now
caught by the simulation at `N = 5, 8` (G3), so at every `N`; m012 and m019, killed before by `KN` alone, are
killed by G2 to G4 (their undriven variable takes a 0/1 value). Every other check.py stage, failing point and
simulation verdict is the previous run's, so neither F5's salted seeds nor `-purge` changed a verdict. check.py's
stages: `postsynth` 72, `extract` 6, `design` 6 (the `Fill:width` refusals), `fourstate` 2, `unproved` (every
check that needs no proof passed) 14: the 9 equivalents, the 5 correct survivors (m067, m070, m072, m083, m086).
One check.py run of m070 failed with an infrastructure error (the C++ build of the Verilator model: `ranlib: can't
open file: VNET__ALL.a`, a make race, failing closed) and passed on a re-run; `tests/checker/test_clocked_post.py`
met the same build error once in the same session and passed on a re-run.

**The power-up of the simulation (the review's F1, 2026-11-07; MEASURED).** `sim.py` `powerup` gave every flip-flop
its 0/1 value with Yosys's `setundef -undriven -init`, which puts the value on one name of the flip-flop's output; when
that name is a copy (`base = ptr` in an `always_comb`), `write_verilog` drops it (an init on a wire), Icarus runs `ptr`
from `x`, and an all-`x` grant fires none of G0 to G4 and MO (`==`/`!=` on `x` give `x`, `if (x)` is false). The
review's design, a pointer that is never reset and grants nothing from a power-up `ptr >= N`, therefore PASSED every
`N` and mode with no grant at all. Now: `opt_clean` after `setundef` moves the value onto the flip-flop's own
variable; the written copy is read back by Yosys and a flip-flop or latch bit without a 0/1 value, or a memory, is an
ERROR (`uninitialized`); and `tb.sv` keeps a self-check `XK` that counts an unknown `gnt` in every snapshot and
pre-edge sample, which a correct power-up of an x-safe design cannot give. The review's design now FAILS (G3, G4 and
`XK`: its reads out of range are `x` in Icarus); its x-safe form is the harness's regression
`tests/arbiter/selftest/alias_ptr.sv` (FAIL on G3, `XK` silent, required by `sim.py`); with the old script the guard
refuses it, naming the four pointer bits (as `base[0]` to `base[3]`, the copy's name). m067 still passes. The sweep's `sim` step re-run with the fixed harness (100 mutants, the
same points, modes and 20000 cycles; `gen`, `check`, `point` and `formal` reused, as the harness is the only change)
gives the same checks at every `N` for every mutant, `XK` nowhere and no power-up error, and `merge` writes a
`MANIFEST.json` and `.txt` byte-identical to the committed ones. m016, the one mutant that had lost an init, was and is
killed by G2.

**Kernel sample** (`tests/arbiter/negative/Mutants.lean`, MEASURED: elaborated with the svGolf build of this
branch, 40 s, axioms `propext`, `Classical.choice`, `Quot.sound`): m061 (RST, G0), m032 (BOR, G1), m016
(SA1, G2), m056 (NEG, G3), m040 (UOR, G3), m089 (DEL, G4), m102 (CRP shift, G4) at `N = 2`, and m099 (OSW,
G4) at `N = 4`, each `¬ Statement` from the all-zero power-up on one stimulus, its twin checked equal to the
loaded `tests/arbiter/mutants/<id>.sv` at `N = 2` (and 4) and 8, the reference's own twin likewise.

Environment of these runs (MEASURED): check.py on a Linux host with Yosys 0.53+81 and Verilator 5.037 and
`--sandbox off` (its bwrap profile did not bind Verilator's include tree there); the reference through the
same runs: clean `unproved`, 769.488 µm² × 2826 ps, equal to tests/expected.json. `lake build tests`: every
module builds but `tests.add`, `tests.mul`, `tests.clmul` `negative.Refute`, the inherited `only_n16.sv`
failure of section 7.

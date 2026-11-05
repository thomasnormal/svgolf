# X1-NOTE: E-core-0 and the keystone refinement R-COMB-0

**Status.** Design note, Day 1 of WS1 (2026-11-02), agent A, branch `arch-x1` from `integ1102` (`d5fbdbc4`). Slot-free: nothing
here has been built yet. Labels: READ (file:line), JUDGED (my choice, the lead may overrule). Status labels of the deliverables:
the E-core-0 definitions are *trusted* (they are the authority for this fragment); R-COMB-0 is *derived from E*; the agreement
with `combSettle2` is the first slice of a *transport theorem*; the executor is a test instrument with one soundness lemma.

**Scope (EXECUTION-PLAN, E-core-0; ARCH-NOTE §7 X1).** One flat module, one time slot, the Active region only: continuous
assigns first (G-A), then one blocking `always_comb` (G-B). 4-state, one driver per bit, a given rank. No timing, NBA,
hierarchy, arrays, loops or parameters. New module `LeanModels/Sv/Kernel/Core0.lean`, imported by nothing; it imports
`Comb2` (later `Comb2Proc`) and `Core.Outcome`. No existing file is edited.

## 1 Types

```lean
inductive Seg | inst (k : Nat) | gen (k : Nat) (i : Int) | blk (k : Nat)   -- unused in E-core-0 (flat: path = [])
structure VarId where path : List Seg := []; decl : Nat                      -- decl = index into the scope's declarations
structure VType where width : Nat; signed : Bool; fourState : Bool
structure Val   where ty : VType; bits : LVec; width_eq : bits.width = ty.width   -- width kept by construction
abbrev Store := VarId → Val
inductive Proc0 | assign (target : Lhs2) (rhs : Expr2) | comb (body : Stmt2)   -- syntax reused, Stmt2 frozen
structure Elab   where decls : Array Decl; procs : Array Proc0               -- flat scope; ProcId := Nat
inductive Status | ready | waiting (sens : List ReadWin)                     -- no `done`, no frames in E-core-0
structure ProcState where status : Status                                    -- derived: ready iff ∈ active
structure Config where store : Store; active : List ProcId; k : Nat           -- k = Choice invocation counter
inductive StepResult | next (c : Config) | slotClosed (c : Config) | refused (r : Loud String Unit)
```

- **Writes are typed.** `Val.write x lo part` keeps `x.ty`; its bits are `x.ty.conv (x.bits.insertAt lo part)`, where `conv`
  squashes x/z for a 2-state type (LRM 6.11). X1 is 4-state: the profile asks every declaration to be 4-state, so `conv = id`.
- **Names.** Expressions keep `Expr2`'s string identifiers; E-core-0 resolves them through the flat declaration table, i.e.
  `evalPure2 (E.view s) e` with `E.view s : SvState := [(decls[i].name, (s ⟨[], i⟩).bits) | i]`. `evalPure2` is thereby E's
  expression evaluator (ARCH-NOTE D1), not a twin. When `Sv.Ast` carries resolved references, `view` disappears (JUDGED).
- **Monad.** One activation is written in the family monad: `activate E p : SemMWith Store Empty String Unit Unit`
  (ρ = `Empty`: a comb activation cannot raise; π = `String` because `SvClause` lives in `World.lean`, whose import chain is
  not built in the shared cache; switching π to `SvClause` is a one-line change). `step` itself is a plain total function.

## 2 Step, legality, closure, executor

- **`Choice := ScheduleOracle`** (READ `Semantics.lean:154`). The legal-schedule predicate is
  `Legal choose := ∀ k ready, (choose k ready).Perm ready`, which is exactly `choose_perm`.
- **`step E ch c`** (no recursion, so no fuel and no `partial`): `match ch.choose c.k c.active with`
  - `[]` → `slotClosed c` (by `Legal`, only when `active = []`);
  - `p :: rest` → run `activate E p` on `c.store` as ONE process-atomic activation; on `.ok s'`, return
    `next ⟨s', rest ++ (E.triggered c.store s').filter (· ∉ rest), c.k + 1⟩`; on a halt, `refused`.
  The Choice is consulted when the running process finishes (ARCH-NOTE §4.1) and may pick ANY ready process (the head of a
  permutation of the whole current ready list), so E admits every LRM order of ready processes under the process-atomic
  ruling. A round-based order (`combSettle2`'s passes) is one particular Choice.
- **Triggering = sensitivity.** `q` is triggered when some element of `E.sens q` changed: for an assign `sens = rhs.reads`
  (longest static prefix: `.whole n`, or a constant window `.win n lo w`; `Comb2Base.lean:763`); for an `always_comb`, the
  body's reads minus the windows the body writes (LRM 9.2.2.2.1, exclusion b). An assign may re-trigger itself; an
  `always_comb` never does. One activation of an assign is its evaluation event plus its update event, fused (a consequence
  of the declared process-atomic profile, JUDGED).
- **No-skip lemma** (`step_legal`): if `step E ch c = next c'` then for the `p` that ran: `p ∈ c.active` (only a ready process
  runs, so none runs after it is done unless re-triggered); `∀ q ∈ c.active, q ≠ p → q ∈ c'.active` (a ready process leaves
  the Active set only by running); and `∀ q ∈ c'.active, (q ∈ c.active ∧ q ≠ p) ∨ Triggered E c.store c'.store q`.
- **Closure.** `inductive Steps E ch : Config → Config → Prop | refl | head (h : step E ch c = .next c') (t : Steps E ch c' c'')`;
  `SlotCloses E ch c c' := Steps E ch c c' ∧ step E ch c' = .slotClosed c'`.
- **Executor** (the only fuel): `exec E ch : Nat → Config → ExecResult` iterates `step`; `exec_sound : exec E ch n c = .closed c'
  → SlotCloses E ch c c'`, by induction on `n`.

## 3 R-COMB-0, assign-only (gate G-A)

Profile `Profile0 E := CombDesign E.toDesign2 ∧ ∀ dc ∈ E.decls, dc.twoState = false`, where `E.toDesign2` is the corresponding
Design2 (same declarations, `Proc0.assign t e ↦ Process2.assign t e`). Reusing `CombDesign` (READ `Comb2Base.lean:801`) is a
JUDGED shortcut for the spike: it is a static fact about the same source. Rank: `AcyclicBy E.toDesign2 rank`
(`Comb2Term.lean:313`), which for assigns is literally "q's sensitivity overlaps p's write window → rank p < rank q".
Invariant `SettleInv E c`: store typed, `active` duplicate-free and in range, and every process NOT in `active` satisfies its
equation in `E.view c.store` (one conjunct of `CombEqs`). `Config.init E s := ⟨s, List.range n, 0⟩` satisfies it.

1. `slot_closes : Profile0 E → AcyclicBy E.toDesign2 rank → ∀ ch c, SettleInv E c → ∃ c', SlotCloses E ch c c'`, by the explicit
   measure `Φ c = Σ_{q ∈ c.active} (N+1)^(N − rank q)` (N processes, rank compressed below N by `Acyclic.exists_rank_lt`):
   running `p` removes `(N+1)^(N−rank p)` and adds at most N processes, each of rank > rank p (a trigger needs a changed bit,
   which lies in p's windows), each worth at most `(N+1)^(N−rank p−1)`. Corollary: `exec E ch (Φ c + 1) c = .closed c'`.
2. `closed_combEqs : SettleInv E c → SlotCloses E ch c c' → CombEqs E.toDesign2 (E.view c'.store)` and every bit no process
   writes is unchanged.
3. `combEqs_unique : CombDesign d → AcyclicBy d rank → StateShape d st → StateShape d st' → CombEqs d st → CombEqs d st' →
   (st, st' agree on every undriven bit) → st = st'` (the rank induction of `CombPassSeq.combAgreeLow`, without passes).
   Hence the closed store is the same for every legal schedule.
4. Negative cases: `osc` (`assign y = ~y`): `¬ Acyclic osc.toDesign2`, and from `y = 0` no schedule closes the slot
   (`¬ ∃ c', SlotCloses osc ch (init) c'`, by an invariant: `active = [0]` forever). `swap` (`assign a = b; assign b = a`):
   `¬ Acyclic`, and `σ_src` and `σ_rev` close at different stores, so uniqueness genuinely needs the rank.

**Agreement with `combSettle2`** (transport, first slice): under `Profile0 E`, `Acyclic E.toDesign2`, a typed `s`,
`settleFuel ≤ fuel`, for every `ch`, `σ`, `k`:
`∃ c' S k', SlotCloses E ch (Config.init E s) c' ∧ combSettle2 E.toDesign2 σ fuel (E.view s) k = .ok (S, k') ∧ E.view c'.store = S`,
plus the fuel-free conditional form (any successful `combSettle2` equals E's closed view). Proof: both are shaped `CombEqs`
solutions with the same undriven bits (`combSettle2_eqs`, `Comb2Sound.lean:158`; a bit-level frame for the settle), then 3.

## 4 With one `always_comb` (gate G-B, after the lead's go)

`execBody E : Stmt2 → SemMWith Store Empty String Unit Unit`, structural (mutual over the `Array` children like `symExec`),
fuel-free, built from `evalPure2`; blocking assigns to static targets, `if`, `case`/`case inside`, `begin…end`; NBA and dynamic
targets refused. The activation of `comb body` is `execBody E body`, run whole (no statement-level micro-steps in E-core-0:
no comb body has a suspension point; frames arrive with E-core-1, JUDGED).
- **R-BODY-0**: with `E.toDesign2.lowerComb = some d'`, `CombDesign d'`, `body.symExec d [] = some S`, on typed stores:
  `(execBody E body).run.run s = .ok ((), s') → ∃ v, evalPure2 (E.view s) S.rhs = .ok v ∧ E.view s' = combWrite d' (E.view s) S.target v`,
  and the activation succeeds. Route: `execBody` ≡ `runCombProcess2 f (view s) (.alwaysComb body)` at `f ≥ body.fuelB`, then
  `runCombProcess2_alwaysComb_ok/_fwd` (READ `Comb2Proc.lean:2324,2345`).
- **R-COMB-0 with `always_comb`**: items 1–3 with `d'` in place of `E.toDesign2`; the rank is stated on E's own sensitivity.
- **Chain to `combSettle2`**: `CombSim.of_lowerComb` + `CombSim.combSettle2` (READ `Comb2Proc.lean:2546,2621`) carry
  `combSettle2 d` to `combSettle2 d'`, then the §3 agreement.
- **Negative**: `always_comb begin y = t; t = a; end` (self-read): `lowerComb = none`, and E closes at a store where
  `y ≠ a` after `a` changes (the block is not re-triggered by its own write of `t`).

## 5 Reuse, and what the lead should check

Reused unchanged: `evalPure2`, `evalPure2_congr_reads`, `ReadWin.agree*`, `SvState.writeWins` and its frame/read-back/identity
lemmas, `combWrite_eq_self`, `CombDesign.combWrite_readBack`, `StateShape.ext`/`eq_of_agree_bits`, `AcyclicBy`,
`Acyclic.exists_rank_lt`, `evalPure2_eq_of_combAgreeLow`, `Comb2Term.agree_bit_of_extract`, `combSettle2_eqs`,
`combSettle2_terminates_shape_of_le`, `combPass2_frame`; for G-B `symExec_sound/_total`, `runCombProcess2_alwaysComb_*`, `CombSim`.
New plumbing: `view` commutes with E's write (`E.view (E.writeWins s v pl) = SvState.writeWins (E.view s) v pl`, names nodup).

Choices (a)–(f) below were ruled YES by the lead (2026-11-02): (a) E-core-0 reuses `Expr2/Lhs2/Stmt2` as syntax and
`CombDesign E.toDesign2` as profile; (b) names resolved via `view`; (c) π = `String`; (d) pick-any-ready Choice with
`Legal = choose_perm` (strictly more schedules than passes; the plan's §7 legality, no separate fairness hypothesis);
(e) trigger at longest-static-prefix windows, with the `always_comb` exclusion of its own written windows (LRM 9.2.2.2.1);
(f) one micro-step per `always_comb` activation (frames come with suspension points in E-core-1). Stop rule: if items 1–3 do
not close in the first slice, I report the same day and do not grow E. Measurements for G-A: heartbeats per theorem
(`maxHeartbeats` probes), kernel time (`trace.profiler`), proof-term size, `.olean` size, lines.

**Trusted cone.** Because E-core-0 evaluates expressions as `evalPure2 (E.view s) e`, `evalPure2` (and the `LVec` operator
tables and `readSignal` it calls, `Pure2.lean`, `Semantics.lean`, `Basic.lean`) is inside the trusted cone of E-core-0, together
with `Lhs2.wins`/`Win.placed` (the static target windows E writes) and `Expr2.reads` (E's sensitivity).

## 6 Debts (ruled by the lead, 2026-11-02)

| id | debt | retirement condition |
|---|---|---|
| D-X1a | The R-COMB-0 profile hypothesis is `CombDesign E.toDesign2` (a Design2 predicate on the image of E's source). It is a hypothesis, never E's meaning. | An E-native profile checker (decidable, with a soundness theorem against `CombDesign`'s uses) lands before E-core-1. |
| D-X1b | Identifiers are resolved through `E.view` (string lookup over the flat declaration table); this puts `evalPure2` in E's trusted cone. | `view` disappears when `Sv.Ast` carries resolved references and the evaluator reads a `VarId → Val` store directly. |
| D-X1c | Refusal payload π = `String`, not `SvClause`. Refusal texts are kept in the form `"<clause>: <message>"` so the switch is mechanical. | Move to `SvClause` when E-core-1 brings in the `World`/`Step` import chain. |

## 7 Gate G-A: result (2026-11-02, agent A)

**Built.** `LeanModels/Sv/Kernel/Core0.lean` (E-core-0, *trusted*; commit `0e4aa7a0`) and
`LeanModels/Sv/Kernel/Core0Comb.lean` (R-COMB-0 assign-only, *derived from E*, with the first *transport* slice; commit
`1d28a0ee`). Both are imported by nothing and build clean with no warnings (MEASURED, `lake build LeanModels.Sv.Kernel.Core0Comb`).
The stop rule did not fire: the assign-only half closed in its first slice (three builds of `Core0Comb`, the first two failing
only on plumbing tactics: `find?` rewrites, an `ite` reduction, a matcher `rfl`).

**The six acceptance items.**
1. *Legality.* `Legal` (= `choose_perm`), `Choice := ScheduleOracle`, and the no-skip lemma `step_legal` (Core0): the process
   that runs was ready, every other ready process stays ready, every newly ready one was triggered by this step, and the ready
   set stays duplicate-free.
2. *Every legal schedule closes the slot, by an explicit rank measure.* `potential N rank c = Σ_{q ∈ active} (N+1)^(N − rank q)`
   strictly decreases at every step (`step_decreases`); `exec_closes`: the executor closes the slot within `potential c + 1`
   steps under every Choice; `slot_closes`: `∃ c', SlotCloses E ch c c'` for every `ch`. No fairness hypothesis was needed.
3. *`CombEqs`, unique under the rank.* `SlotCloses.combEqs` (the closed view solves `CombEqs` and keeps every undriven bit),
   `combEqs_unique` (two shaped solutions agreeing on undriven bits are equal), hence `rcomb0_schedule_independent` and the
   packaged `rcomb0`. Beyond G-A, already for assigns: `closed_eq_combSettle2` (fuel-free: any successful `combSettle2` from the
   start view returns E's closed view) and `rcomb0_combSettle2` (for every Choice and every `ScheduleOracle`, both terminate and
   agree), by uniqueness, not by a fixture.
4. *Negative cyclic case.* Theorems `osc_not_acyclic` (`assign y = ~y`) and `swap_not_acyclic` (`a = b; b = a`); `#guard` rows:
   `osc` does not close within 1000 steps under `σ_src` or `σ_rev`; `swap` closes at `(1,1)` under `σ_src` and `(0,0)` under
   `σ_rev`.
5. *Axioms.* Every theorem: `[propext, Classical.choice, Quot.sound]` or fewer (pinned by `#print axioms` at the end of
   `Core0Comb.lean`). No `sorry`, `native_decide` or `decide` on large terms.
6. *Cost* (MEASURED on the loaded machine; scripts and raw output in `$SP/arch/x1probe/`):

| item | Core0 (defs + 6 theorems) | Core0Comb (56 theorems) |
|---|---|---|
| code lines (non-blank, non-comment) | 263 (trusted defs 148, executor + `exec_sound` 33, `step_legal` 43, smoke 35) | 618 |
| elaboration, thousand-heartbeats (`#count_heartbeats in`, `Elab.async=false`) | 757 total, max 358 (`step_legal`) | 9,526 total, max 743 (`wsum_higher_lt`) |
| kernel re-check of the proof terms (`addDecl` of a copy) | 4.5 ms, 41k raw heartbeats | 39.6 ms total, max 4.2 ms (`step_inv`), 349k raw heartbeats |
| proof-term size (`Expr.numObjs`, shared DAG) | 3,247 objects total, max 1,922 | 26,137 total, max 3,695 (`step_inv`) |
| `.olean` | 1.21 MB | 1.35 MB |

**Trusted cone of E-core-0, exactly.** In `Core0.lean`: `Seg`, `VarId`, `VType` (`ofDecl`, `conv`), `Val` (`ofLVec`,
`write`), `Store` (`set`), `Proc0`, `Elab`, `Proc0.toProcess2` and `Elab.toDesign2` (read by `activate` only for declared
widths), `Elab.declOf`, `resolveAux`/`Elab.resolve`, `viewAux`/`Elab.view`, `Elab.initStore`, `Elab.writeWin`/`writeWins`,
`EM`, `refuse0`, `ofRes`, `activate`, the `Decidable (ReadWin.agree …)` instance, `Elab.sens`, `Elab.triggered`, `Config`,
`Config.init`, `Legal`, `Choice`, `StepResult`, `step`, `Steps`, `SlotCloses` (148 code lines); NOT in it: `exec`/`ExecResult`
(instrument, `exec_sound`), `Elab.Typed`, `Elab.Triggered`, `ProcState`/`Status`/`Config.procState` (derived), `Elab.setName`
(test helper). Imported into the cone: `evalPure2`/`evalPures2` with `readSignal` and the `LVec` operator tables they call
(`Pure2.lean`, `Semantics.lean`, `Basic.lean`, `Sem2.lean`'s `LVec` additions), `Lhs2.windows?`/`window?`/`listWindows?`,
`Design2.declWidth`, `Win.placed`/`sumWidth`, `Expr2.reads`, `ReadWin.agree`, `SvState.lookup` (`Comb2Base.lean`,
`Semantics.lean`), `ScheduleOracle`, and Core's `SemMWith`/`Loud`/`refuse`/`exhausted`.

Where the 618 lines go: name resolution and the view (102), typed stores and E's write as `SvState.writeWins` (66), one
activation (31) — together the plumbing, 199 lines (32%); the settle invariant and one step (165), the measure (72), closing
(46), uniqueness (53) — the semantic argument, 336 lines; transport to `combSettle2` (39); negatives (25). For scale: the whole
R-COMB-0 proof elaborates in about 9.5k thousand-heartbeats, below the 15.7k per template site that ARCH-NOTE §7 X7 records for
today's `symExec` route (JUDGED comparison: different work).

**What was reused unchanged:** `evalPure2_congr_reads`, `ReadWin.agree_combWrite`, `CombDesign.combWrite_readBack`,
`CombAgreeLow`/`evalPure2_eq_of_combAgreeLow`/`agree_bit_of_extract` (the uniqueness induction is `CombPassSeq.combAgreeLow`
without passes), `StateShape.eq_of_agree_bits`, `Acyclic.exists_rank_lt` (rank compression gives the measure's `N`),
`combSettle2_eqs`, `combSettle2_terminates_of_le`, `combPass2_frame`/`_width`.

**Not done at G-A, by choice:** non-closure of `osc` and the two `swap` closures are `#guard` rows, not theorems (the lead
accepted either). `SettleInv` asks for a typed store and `AllFour` (X1 is 4-state).

## 8 Gate G-B: result (2026-11-02, agent A)

**Built** (commits `c279523c`, `92c5e25d`, `dcc95d55`; all modules build clean with no warnings; no `sorry`, `native_decide`,
`partial` or `decreasing_by`):
- **E grows by one construct** (`Core0.lean`, *trusted*): an `always_comb` activation runs its whole body through `execBody`, a
  fuel-free structural recursion over the frozen `Stmt2` built from `evalPure2` (blocking assignments to static targets, `if`,
  `case`/`case inside`, `begin…end`; NBA, dynamic and concatenated targets refused). Its sensitivity is the body's longest
  static prefixes minus those overlapping a window the body writes (ruling (e)). `#guard`s: the fixture `mux1` (two assigns
  around one `always_comb`) under two schedules, and the self-reading body closing with a stale output.
- **The settle argument is generic** (`Core0Comb.lean`, refactor): every step, measure, closing, uniqueness and `combSettle2`
  lemma is stated for an *equation design* `d` with `Settles E d rank` (each activation writes on the view what process `p` of
  `d` writes; E's sensitivity covers `d`'s reads; a trigger goes up in rank). The G-A theorems keep their names and meaning
  (`SettleInv` now names its equation design, `E.toDesign2` for assigns) and are proved through `Settles.ofProfile0`: the
  assign-only transport stays a special case with no new hypothesis (`completeB`/`rankedB` are derived there from `Acyclic`).
- **The chain** (`Core0Proc.lean`, *derived from E*; transport, second slice):
  1. **R-BODY-0** `activate_comb`: on a typed store, an `always_comb` activation succeeds and is, on the view, `combWrite` of the
     assign its body lowers to. Via `execBody_of_execStmt2` (a fuel induction over the interpreter's mutual block: `execBody` is
     `execStmt2` without fuel on static bodies) and the existing `runCombProcess2_alwaysComb_fwd`.
  2. **R-COMB-0 with `always_comb`** `Settles.ofLower`: the lowered design `d'` is an equation design for E, so all of §7's
     generic theorems apply (every legal schedule closes the slot, within `potential + 1` steps; the closed store solves
     `CombEqs d'` and is its unique solution with the start's undriven bits).
  3. **To `combSettle2`** `rcomb1` (existence, every Choice and every `ScheduleOracle`) and `closed_eq_combSettle2_lower`
     (fuel-free): E's closed store is what `combSettle2` returns on the DESIGN itself (through `CombSim`), by uniqueness.
- **Fixture** `mux1` (`w = z ^ a`, `z = y + 1`, `always_comb begin t = a & b; if (c) y = t; else y = ~t; end`): `mux1_lower`
  (the lowering, by `rfl`), `mux1Low_comb` (by hand), `mux1_settles` (`AllFour` by `decide`, `completeB`/`rankedB`/`boundB` by
  `rfl`), `mux1_rcomb1` (the chain instantiated from the startup store).
- **Negative**: `selfRead_not_lowered` (the body `y = t; t = a;` fails the hypotheses: its lowering is `none`), and two
  `#guard`s showing the conclusion is then false: E closes with `y = x` (stale; the block is never woken by its own write of
  `t`), `combSettle2` returns `y = 0`.

**The trusted cone grows by** `Lhs2.staticWin`, `Stmt2.rawReads`/`targetWins` with their list/option/case-arm helpers, the
`execBody` mutual block (`execBody`, `execBodyOpt`, `execBodyList`, `execArm`, `execArms`), and the `always_comb` arms of
`activate` and `Elab.sens` (121 code lines); imported into it: `caseHit`, `LVec.condTrue`, `Lhs2.window?`. `Elab.toDesign2`
now maps over the process list instead of the array (kernel-reducible; same value).

**Cost** (MEASURED, same instruments as §7; raw output in `$SP/arch/x1probe/`):

| module | code lines | elaboration, thousand-heartbeats | kernel re-check | proof terms (objects) | `.olean` |
|---|---|---|---|---|---|
| `Core0` (E, now with `always_comb`) | 412 (always_comb machinery 121) | 2,943 (max 1,405: the `execBody` mutual block) | 4.6 ms (6 theorems) | 3,247 | 1.54 MB |
| `Core0Comb` (generic + assign-only) | 739 (`Settles` instance 87) | 10,655 (max 743) | 45.4 ms | 30,073 (max 3,612) | 1.48 MB |
| `Core0Proc` (G-B) | 580: static bodies 128, adequacy 180, R-BODY 24, checks 45, instance 32, chain 24, fixture 100, negative 8 | 16,796 (max 3,761: `mux1Low_comb`; 3,271: `execBody_of_execStmt2`) | 106.6 ms (max 27.4 ms: `mux1Low_comb`; `mux1_lower` by `rfl` 15.1 ms) | 27,795 (max 7,162) | 2.05 MB |

The generic part of G-B (everything but the fixture) is 480 lines and about 9.4k thousand-heartbeats; per-design cost is the
fixture's 100 lines, almost all of it the hand proof of `CombDesign d'` (the next item below would make it `rfl`).

**Debts added at G-B.**

| id | debt | retirement condition |
|---|---|---|
| D-X1d | Sensitivity-completeness (`completeB`: the lowered right-hand sides read only what E's sensitivity covers) and the rank certificate on E's sensitivity (`rankedB`) are decided per design, not proved once from `symExec`. For assign-only designs both are derived (`Settles.ofProfile0`). | A lemma `symExec … = some S → selfReadFree S → completeB` (the lowered reads are raw body reads not overlapping the write set; estimated 200–300 lines, the zero-width-window corner included), and `rankedB` from `Acyclic d'` for bodies whose raw reads all survive in the lowering. |
| D-X1e | `CombDesign` of a lowered fixture is proved by hand (100 lines for `mux1`). | The E-native decidable profile checker of D-X1a, with its soundness theorem; fixtures then discharge every hypothesis by `rfl`. |

**Open question for the lead (JUDGED).** E's `always_comb` sensitivity drops a read that *overlaps* a written window. The LRM
text (9.2.2.2.1 b) drops an *expression that is also written*. They differ only on partial overlaps (a whole read of `y` in a
body that writes `y[1]`); every such body is outside the R-COMB profile (the lowering refuses it), so no theorem depends on the
choice, but E's meaning for such a body does. It should be settled by an Xcelium row before E-core-1.

## 9 R-DESIGN2, comb slice: result (2026-11-02, agent A). Status: transport theorem

arch-obs is merged at exactly `223b596f` (merge commit `cf848c4b`); P's files are unchanged (READ, `git diff 223b596f -- `
P's paths is empty). Code: `LeanModels/Sv/Kernel/Core0Obs.lean` (E-core-0 as a backend, both inclusions, the negative),
`svgolf/design/architecture/ObsCombE.lean` (the `CombTask` transport) and `ObsCombEExample.lean`/`ObsCombEAdd.lean` (the
record instances; compiled by `compile-obsE.sh` against a check.py `--stage-dir` tree). Every theorem below depends only
on `propext`, `Classical.choice`, `Quot.sound` (MEASURED, `#print axioms` in the build logs).

**(a) The backend `Obs_E0`** (an instance of P's `ESig`). No clocks; the environment is a stimulus list; each cycle takes
two slots. Slot `2c` opens with entry `c`'s input events (`Config.nextSlot`, `Core0.lean`: each bound input is converted
to its declared type, LRM 10.7, and the processes that read it are woken), slot `2c + 1` is quiet and is the sample slot.
So pre sample = Postponed sample = the closed store of slot `2c`. `Config := SvState` (the view), `Disciplined := True`.

**(b) The inclusions**, for every design with an equation design `d` (`Settles E d rank`) and `SettleAgree E d` (no edge
or reset process; a closed store is what any completed `combSettle2` returns; some fuel completes it). `SettleAgree.ofSettles`
gives it for assign-only designs, `SettleAgree.ofLower` for `always_comb` designs through G-B's lowering and `CombSim`.

| direction | theorem | hypotheses |
|---|---|---|
| E → `run2` | `included_E0_run2_agree`; assign-only at `run2`'s own `settleFuel`: `included_E0_run2`; `always_comb`: `included_E0_run2_lower` | `InitTyped` (every initializer at its declared width) |
| `run2` → E | `included_run2_E0_of_typed`: `IncludedOn Obs_run2 Obs_E0 k d E (StimTyped d)`, same schedule, same stimulus | `InitTyped`, typed stimulus |
| `run2` → E, unrestricted | FALSE: `not_included_run2_E0` (every assign-only design with an input) | — |

Non-vacuity: `Core0Smoke.mux1_included`, `mux1_included_typed` (G-B's fixture, one `always_comb` between two assigns), the
records below, and `example_not_included` (the `_example` record's own design, stimulus `a := (N+1)`-bit 0).

**Finding (proved).** `run2` stores a stimulus value as given (`applyInputs2`); E converts it to the port's declared type
(LRM 10.7). So a stimulus binding an input at the wrong width gives a `run2` behaviour that E has no counterpart for: E's
samples are typed (`E0_pre_width`). The E → `run2` direction needs no restriction: the `run2` stimulus is the one that
re-drives every input to its pre-sample value, which is typed. Consequence (JUDGED): R-DESIGN2's equivalence must be stated
on typed environments. P's `Included` has no design-dependent environment predicate, so `IncludedOn` is defined locally in
`Core0Obs.lean`. Moving it into `Observe.lean`, or making `Obs_run2.Disciplined` see the design, is P's call, routed
through the lead. v1 records are unaffected: their stimulus convention (`entryOf`) only builds typed entries.

**(c) The transport** (`ObsCombE.lean`). `satisfiedAt_E0`/`statement_E0`: from a v1 `t.Statement sem` (over `run2`) and,
at every `N` in range, `CombDesign (sem N)`, `Acyclic (sem N)`, every declaration 4-state and `InitTyped (sem N)`, the
task's `Statement_obs ty Obs_E0 (fun _ => True) (Elab.ofDesign2 ∘ sem)` at every declared-type predicate `ty`. Instances,
MEASURED (each record re-checked by `check.py --stage-dir --no-trusted-build --no-score --ppa off`, accepted, then the
instance compiled against the staged `Submission.Solution`):

| record | theorem | fragment hypotheses discharged by |
|---|---|---|
| `_example` `6b60e573…` | `RecExample.example_E0` | `band_comb`, `band_acyclic`; 4-state and `InitTyped` by `simp` on `band_sem_decls` |
| `_example` `fc1173e2…` (localparam variant) | `RecExample.example_E0` (same file, same lemma names) | same |
| `add` `d4a292db…` | `RecAdd.add_E0` | `ripple_comb`, `ripple_acyclic`; `ripple_sem_decls` |

**Which hypotheses are missing, exactly.** The v1 statement does not contain the fragment hypotheses: `CombDesign`,
`Acyclic`, 4-state declarations, `InitTyped`. A record that does not export them cannot be transported by this theorem. All
three accepted records export the first two as named lemmas, and the last two follow by `simp` from their `*_sem_decls`.

**Route (JUDGED, read against P's lemmas).** The lead's route was `Safe.of_included` plus P's `statement_iff` lemmas. It
needs the v1 statement in the pre-sample convention over `Obs_run2`. P proved only the other direction
(`computes_of_computes_obs`, "the converse (the direction records need) is costed … and not proved", READ
`ObsComb.lean:227-228`). The transport therefore uses the strong form of E → `run2` (`runObs2_of_runs_E0`). It keeps the
stimulus that reproduces each E behaviour, namely the re-driving stimulus, so v1's stimulus-convention conjunct applies
directly. On that stimulus the known inputs are exactly the pre sample's. The same re-drive argument should also give
P's missing direction over `run2` itself (on assign-only designs inputs are undriven, so re-driving them changes nothing).
That is not done.

**Cost** (MEASURED): `Core0Obs.lean` is 1,055 lines. By section: header, backend and assign-only E → `run2` 541;
`SettleAgree` and generic E → `run2` 171; typed converse 168; negative 97; `ofDesign2` 40; instances 23; pins 15. It elaborates in 2.1 to 4.2 s
wall, 1.4 s user, with peak RSS 0.70 GB (`lake env lean -DElab.async=false`, two runs). `ObsCombE.lean` is 163 lines; each
record instance is 39 to 60 lines and compiles in 4 to 6 s against its staged record. A record staging with the slot held:
`_example` 1 min 35 s; with per-call slot queueing, 3 min 46 s and 8 min 22 s. One queued run timed out at check.py's
900 s design limit while waiting for the shared slot (an infrastructure artefact, JUDGED: the same record passed with the
slot held).

**Not done in (1).** Clocked designs (R-EDGE: X4). R-COMB-1 (the window rank, queue item 2) is untouched. Every
theorem here is at process rank.

## 10 R-COMB-1: the window rank (2026-11-02, agent A). Status: derived from E

Code: `LeanModels/Sv/Kernel/Core0Win.lean` (new; imports `Core0Proc`, imported by nothing). Every
theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (MEASURED).

**What changed.** The rank now orders WRITTEN WINDOWS, not processes.
- **Per-window lowering** (`Design2.lowerWin`): an assign is one equation. An `always_comb` body in
  the profile becomes one assign per entry of its symbolic state (`W.lhs = E_W`), tagged with the
  process it comes from. `Design2.winDesign` is the equation design; `winOwn ps p` is what `p` owns.
- **Interface** `WSettles E d own rank`. Activating `p` writes exactly `p`'s equations at their
  pre-state values (`WriteRel`). E's sensitivity of `p` covers their reads (`complete`). No equation
  of `p` reads a window of `p` (`group`). The rank is a certificate of the EQUATION design
  (`AcyclicBy d rank`). G-A/G-B's `ranked` field (a triggered process ranks higher) is gone.
- **Measure** `wpotential = dirtyW · (P + 1) + |ready|`. `dirtyW` weighs every violated equation by
  `(M + 1)^(M − rank)`. A step either cleans a violated equation of the lowest rank among those it
  writes, and can only violate equations of strictly higher rank (`WSettles.dirty_source`, by the
  bit-level frame `WriteRel.agree`); or it changes nothing and shrinks the ready list.

**Theorems.**

| statement | theorem |
|---|---|
| every legal schedule closes the slot, within `wpotential + 1` steps | `WSettles.exec_closes`, `slot_closes` (via `step_decreases`) |
| the closed store solves the window equations, keeps the undriven bits, is their unique solution, is schedule-independent | `WSettles.slotCloses_combEqs`, `rcomb`, `schedule_independent` |
| `combSettle2` on the design itself returns E's closed store whenever it completes (fuel-free) | `WSettles.closed_eq_combSettle2` (`CombSim` to the process-level lowering, then `combEqs_win_of_lower`) |
| the per-window lowering is an equation design for E | `WSettles.ofLowerWin` (with `activate_comb_symRel`, R-BODY-0 per window) |
| **the process rank is the special case** `own p = [p]` | `Settles.toW`; instance `Core0Smoke.mux1_wsettles` |

**Acceptance (the ibex_controller shape).** `Core0Smoke.ibex` is
`always_comb begin a = x; c = b; end` beside `assign b = a + 1`. Results:
- the lowering by `rfl` (`ibex_lowerWin`);
- the profile by hand (`ibexEq_comb`), the rank certificate by `rfl`;
- `ibex_rcomb`: every legal schedule closes at the unique solution;
- `ibex_schedule_independent`;
- `ibex_closed_eq_combSettle2`;
- `ibexLow_not_acyclic` and `ibex_no_settles`: the process-level lowering is in the comb profile
  (`ibexLow_comb`), but no rank orders its two processes, so G-B's interface has no instance.

`#guard` rows (MEASURED): from `x = 5`, both source and reverse order close at `a = 5, b = 6,
c = 6`, and `combSettle2` on the design returns the same. No new negative was added. `osc` and `swap`
remain the negatives; they are cyclic at window level too.

**Debts added.**

| id | debt | retirement condition |
|---|---|---|
| D-X1f | Termination of `combSettle2` on a design that is only window-acyclic (the existence half of G-B's `rcomb1`) is not proved. MEASURED on `ibex`: it completes from fuel 8. Consequence: R-DESIGN2's `SettleAgree.settles` and the E → `run2` inclusion are not yet available for such designs. The `run2` → E direction needs only the fuel-free half, which is proved. | A pass argument over windows: after `r` passes every equation of rank `< r` is final (the window version of `CombPassSeq.combAgreeLow`). JUDGED 200 to 300 lines. |
| D-X1g | `Core0Obs` (R-DESIGN2) is stated over the process-rank `Settles`. | Restate `SettleAgree` and the cycle lemmas over `WSettles` (they use only `act`/`complete`/closure facts, which `WSettles` has), after D-X1f. |
| D-X1e (grows) | The profile (`CombDesign`) of the per-window equation design is by hand (`ibexEq_comb` with its helper lemmas, 82 lines; the fuel-free link also needs the process-level lowering's, `ibexLow_comb`, 82 lines). | Unchanged: the decidable profile checker. |

**Finding (MEASURED, not a window-rank issue).** `Design2.settleFuel` (`combFuel + #processes + 1`)
does not count an `always_comb` body's statement fuel (`Process2.rhsSize` is 0 for it), so
`combSettle2` times out at `settleFuel` on designs with `always_comb` blocks:

| design | `settleFuel` | fuel needed (σ_src / σ_rev) |
|---|---|---|
| `ibex.toDesign2` | 5 | 8 / 8 |
| G-B's `mux1.toDesign2` | 6 | 10 / 8 |

Nothing trusted is affected, JUDGED from READ:
- `Runs2`/`Terminates2` quantify fuel existentially (`Spec2.lean:124,144`).
- `svgolf-eval` runs at fuel 100000 (`check/SvEval.lean:25`).
- The explicit-fuel lemmas are stated for assign-only designs (`CombDesign`).

The name invites the wrong expectation. A fix (adding `Stmt2.fuelB` to `combFuel` for `always_comb`)
would be in `Comb2Base.lean`, an existing module, so it is for the lead to route.

**Cost** (MEASURED): `Core0Win.lean` is 1,498 lines. By section:

| section | lines |
|---|---|
| lowering and its spec | 150 |
| `WriteRel` and the bit-level frame | 155 |
| interface, invariant, step lemmas | 180 |
| measure | 165 |
| closing and uniqueness | 65 |
| special case | 35 |
| instance | 220 |
| `combSettle2` link | 165 |
| fixture (the two hand profiles 164 of it) | 265 |

It elaborates in 3.2 to 4.6 s wall, 2.4 to 2.6 s user, peak RSS 0.70 GB (`lake env lean
-DElab.async=false`, two runs).

## 11 X4: E-core-1's edge fragment, R-EDGE, and the discipline audit (2026-11-02, agent A). Status: derived from E

Code (new modules, imported by nothing):
- `LeanModels/Sv/Kernel/Core1Edge.lean`: the edge fragment of E-core-1, and R-EDGE.
- `LeanModels/Sv/Kernel/Core1Disc.lean`: the clocking discipline, and `clockExpand_disciplined`.
- `svgolf/design/architecture/audit_discipline.py`: the testbench audit.

**E-core-1, edge fragment.**
- **Processes.** An edge process `FF` is `always_ff @(posedge clk)` or `@(posedge clk or negedge
  rst_n)`. Its body is NBA-only: nonblocking assignments under `if`/`begin-end`, and anything else
  refuses. It reads the view, which does not change while it runs, and returns `run2`'s
  `NbaQueue2` (`execFF`).
- **Configuration and step.** `Config1` adds the NBA queue. `step1` runs a chosen ready process
  atomically and appends its updates. With Active empty and the queue not, it commits the whole
  queue in issue order and readies the edge processes whose clock rose or reset fell across the
  commit. Otherwise the slot closes.
- **Slot opening.** Input events fire the edge processes (`Config1.nextSlot`).
- **Modelling choice (JUDGED).** The queue commits as one step, with triggering read off the
  stores before and after it. An LRM simulator commits one NBA at a time and can see a glitch.
  No theorem depends on this, because no edge process may write a clock or a reset.

**R-EDGE** (`rEdge`). In a slot whose ready set is any duplicate-free set of edge processes, from a
store `s` with an empty queue, EVERY legal schedule closes the slot. The closed view is
`commitNba2 (view s) (queue s act)`: every ready process's updates, computed on `s`, committed in
index order. The result does not mention the schedule.

Hypotheses (`EdgeProfile`, discharged by decided checks on the bodies' static NBA windows,
`EdgeProfile.ofChecks`): bodies in the fragment; one edge writer per slice; no NBA writes a clock
or a reset.

Route:
1. During Active the store is fixed, so the queue collects every ready process's block in run
   order (`active_phase`).
2. Disjoint updates commute (`nbaStep_comm`, on `LVec.insertAt_comm`), so blocks commute and any
   permutation of the blocks commits the same view (`commitNba2_perm`).
3. The commit writes no clock or reset bit, so nothing re-triggers and the slot closes.

Asynchronous active-low reset is the same theorem. A falling `rst_n` fires the processes that list
it, and their `if (!rst_n)` branch runs.

Fixtures:
- `Core1Smoke.cnt`, a counter with asynchronous reset.
- `Core1Smoke.nbaSwap`, `a <= b` beside `b <= a`, Core0's blocking `swap` made nonblocking.
- Checks by `rfl`/`decide`; instances `cnt_rEdge`, `nbaSwap_rEdge`.
- `#guard` rows (MEASURED): the swap closes at the swapped values under both orders; the counter
  counts on a rising clock, clears on a falling reset with the clock low, and holds on a falling
  clock.

**The discipline** (`Core1Disc.lean`). `Disciplined edge clk inputs env`: in every slot where
`clk` makes its ACTIVE edge (`edge`: `isPosedge` or `isNegedge`; the parameter is D-X1k, accepted by
the lead), no other input of `inputs` changes. The edge and the values are read from the
environment alone (`inputAt`). With the reset among `inputs`, a synchronous reset is held across
the edge and an asynchronous one falls in a slot of its own. `clockExpand_disciplined`: the
harness's `clockExpand` satisfies the rising-edge instance (`Disciplined isPosedge`) for every
stimulus and input list. This retires ARCH-NOTE §4.3's "hidden in the harness" half.

**Audit of the testbenches** (`audit_discipline.py`, a heuristic reader over `initial` blocks;
findings READ).

| source | verdict |
|---|---|
| `clockExpand` | disciplined, by theorem |
| `harness/sv/gen_tb.py`, `gen_tb2.py`, hence every Xcelium golden `xcelium_batch.py` runs (it calls `gen_tb2.generate_tb2`) and `sv_divergence_probe.py` | disciplined by construction (READ `gen_tb2.py:10-12, 55-90`, `gen_tb.py:10-23, 101-108`): inputs at time 3k with the clock low, the posedge alone at 3k+1, sampling at the negedge; the clock is declaration-initialised, so there is no time-0 transition |
| svGolf validate testbenches, `always-comb/fixtures/tb_add.sv` | no clock: vacuous |
| `Examples/system-verilog` (63 files with a clock and an `initial` block) | ok 22, no clock edge 38, deliberate scheduling tests 3, undisciplined 0 (MEASURED) |

The three deliberate scheduling tests (lead's ruling: listed with the rule that excludes each, not
changed):

| test | what it does | rule that excludes it |
|---|---|---|
| `always_ff_capture.sv` | clock and `d` change in one time step, plus a `#0` clock pulse | the discipline (no other input changes in an active-edge slot); E-core-1's slot model (no `#0`/Inactive-region events) |
| `intra_assignment/events.sv` | intra-assignment event controls (`repeat (n) @(posedge clk)`) while the testbench changes `source` with the clock | the profile (no timing control inside an assignment) |
| `always_ff_event_iff_neg.sv` | `@(negedge clk iff en)`, with `en`/`d` changing on the posedge | disciplined under the active-edge rule (the changes fall on its inactive edge); its `iff` guard is outside the profile |

**What the audit says about the rule (JUDGED).** The discipline is the right rely: the generated
stimulus satisfies it by construction, `clockExpand` by theorem, and every hand-written row that
does not satisfy it is a deliberate scheduling test. The one refinement it forced is the
active-edge parameter (D-X1k).

**Not done in X4.**
- **D-X1h.** Comb processes beside edge processes in one design: R-EDGE's `settle` half, the
  composition with R-COMB's `WSettles` after the commit.
- **D-X1i.** Blocking writes to locals inside `always_ff` (ARCH-NOTE's "written before read").
- **D-X1j.** `case` in edge bodies (refused today).
- **D-X1f, extended by the lead.** The `settleFuel` fix: a statement-fuel bound for an
  `always_comb` body, proved sufficient for `runCombProcess2`, used additively in the `alwaysComb`
  arm of `Process2.rhsSize` (`Comb2Base.lean`, with every dependent module built). Next after X4.
- **Xcelium row.** The one-step NBA commit against a per-update commit, needed only once a design
  can write a clock (outside the profile).

**Cost** (MEASURED; `lake env lean -DElab.async=false`, two runs each):

| module | lines | wall | user | peak RSS |
|---|---|---|---|---|
| `Core1Edge.lean` | 804 | 2.1 to 3.1 s | 1.5 s | 0.70 GB |
| `Core1Disc.lean` | 175 | 2.0 to 4.7 s | 1.0 s | 1.38 GB (it imports `Adequacy`, hence the M0 loader chain) |

`Core1Edge.lean` by section:

| section | lines |
|---|---|
| static NBA windows and checks | 67 |
| commit algebra | 118 |
| kernel | 132 |
| `execFF` lemmas | 113 |
| commit on the view | 17 |
| profile | 83 |
| R-EDGE | 137 |
| fixtures | 74 |

Every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (MEASURED, `#print axioms`).
The audit script is 115 lines.

## 12 D-X1f (fuel half), the fidelity batch, and D-X1h (the counter) (2026-11-03, agent A)

Every theorem below depends only on `propext`, `Classical.choice`, `Quot.sound` (MEASURED).

**D-X1f, fuel half** (`b47a2cab`). In `Comb2Base.lean`, additive only:
- `Stmt2.combFuelB`, the equations of `Comb2Proc`'s `Stmt2.fuelB`;
- the `alwaysComb` arm of `Process2.rhsSize`;
- `Design2.combFuelB_lt_combFuel`.

In the new module `Comb2Fuel.lean`:
- `combFuelB_eq_fuelB`;
- `runCombProcess2_alwaysComb_of_combFuelB`/`_of_combFuel`: sufficiency for the bodies the
  lowering accepts. Scope: the comb profile only; bodies outside it have no claim.

The 93 dependents of `Comb2Base` (master's `check_sv_chain.sh --dependents`: 36 library modules,
57 Examples) rebuild green. The termination half is D-X1f2 (plan accepted). A symbolic-N version
needs an equation design built without `symExec` (L, `SingleE`).

**D-X1f2, the termination half** (`Kernel/Core0WinTerm.lean`, new, imported by nothing; 312
lines MEASURED). `combSettle2_terminates_win`: under `WSettles E dW (winOwn ps) rank`,
`combSettle2` on the design itself returns from every state shaped for the process-level lowering
`d'`, under every schedule, with a result shaped for `d'`. Route:
- a process of `d'` and the window equations it owns write the same state (`run_writeRel`,
  `seq_run`; `WriteRel.unique`);
- so a pass of `d'` is a pass of `dW` (`pass_win`), and the settle sequence of `d'` is a
  `CombPassSeq` of `dW`, constant from pass `|dW|` on (`CombPassSeq.stable`);
- `combSettle2_ok_of_stable` closes the settle on `d'`; `CombSim.of_lowerComb'` carries it to the
  design.

Fixture: `Core0Smoke.ibex_terminates`, whose process-level lowering is cyclic. Scope: concrete
lowerings (`lowerWin` goes through `symExec`).

**D-X1g, R-DESIGN2 over the window rank** (`Kernel/Core0ObsWin.lean`, new, imported by nothing;
238 lines MEASURED, all restatement). `WSettleAgree` is `SettleAgree` with `WSettleInv`;
`WSettleAgree.ofLowerWin` takes `closed` from `WSettles.closed_eq_combSettle2` and `settles` from
`combSettle2_terminates_win`. The cycle lemmas are restated word for word (`WSettles.nextSlot_inv`,
`behaves0_inv`, `slot_start`, `slot_quiet`, `cycleObs2_of_slot_wagree`,
`runFromObs2_of_behaves0_wagree`, `runs2_of_runs_E0_wagree`). `included_E0_run2_win`: every E
behaviour is a `run2` behaviour of the design itself, for designs whose process-level lowering may
be cyclic. Payoff fixture: `Core0Smoke.ibex_included`, where the process-rank route has no
instance (`ibex_no_settles`). Not restated: the typed converse (`run2` → E) and the progress
lemma over the window rank.

**Week-2 candidate (not started): the symbolic-N lowering.** `lowerWin` goes through `symExec`,
which has no normal form at a symbolic parameter (L's finding), so `combSettle2_terminates_win`
and `included_E0_run2_win` apply only at concrete lowerings. The fix is an equation design built
without `symExec`: a per-window lowering defined on the body's syntax with windows as functions of
`N`, and its soundness (each activation is `WriteRel` of its equations) proved once, so that
`WSettles.ofLowerWin`'s hypotheses become statements about `N`. JUDGED 400 to 700 lines for a
general version (the soundness argument is `symExec_sound`'s shape). The per-family route L used
(`SingleE`: a hand-built equation design and one equality lemma per family) is JUDGED 100 to 150
lines per family.

**Fidelity batch** (from M's X2 and L's reading):

| item | decision | change |
|---|---|---|
| `acg_xproc_bits` (`33dc39c8`) | fixed, to LRM 9.2.2.2.1 as Xcelium reads it | `Elab.sens` keeps the unwritten bits of a partly written read (`Stmt2.partialSens`) |
| `dyn32` | deliberate profile choice, not changed | needs a register row (see below) |
| case qualifiers (`2d4cdd55`) | (a): a violated `unique`/`unique0`/`priority` claim refuses loudly with `run2`'s `CaseCheck:<qualifier>` | first match when the claim holds; a plain case unchanged |

- **`acg_xproc_bits`.** `Core0Smoke.xprocBits` reproduces the pinned Xcelium trace under both
  orders. Before the fix the whole read was dropped (Icarus's reading).
- **`dyn32`.** E, like `run2`, follows LRM 11.5.1: in-range bits are read, out-of-range bits are
  x. The repo already argues that Xcelium's all-x is a departure (`xcelium-runtime-partial-part-
  select-all-x`). The row `dyn32` needs a declaration.
- **Case qualifiers.** `caseClaimOk` mirrors master's `checkCaseObligation`. The lowering theorems
  exclude qualified cases (`Stmt2.qualFree`, `Elab.qualFreeB`, decided), as `run2`'s take
  `hasQualifiedCase = false`. `Core0Smoke.uniqueDup` pins both outcomes.

For L's re-merge, one proof changes: `Loop2Slot.sens_of_read` becomes `Elab.mem_sens_of_raw`.

**D-X1h, the counter** (`CounterE.lean`, `728b6ee2`; P's files read-only).
- `cntE N`: the counter as an E-core-1 edge process.
- `cntE_profile` at every `N`, its checks by `rfl`.
- `cnt_low`: the clock-low slot fires nothing.
- `cnt_rise`: by `rEdge`, every legal schedule closes the rising slot with `q = cntNext N r e q`.
- `cnt_rise_step`: through P's `Rel`, reset gives `cntTask.init` and otherwise `cntTask.step`.

This is the counter's cycle-machine step derived from E, the first R-CYCLE slice against the
authority.

**D-X1h, the Obs-level inclusion** (`Kernel/Core1Obs.lean`, `CounterEObs.lean`; P's files
read-only).
- `E1 clk`/`Obs_E1 clk`: E-core-1 as an `ESig`. The environment is one entry per cycle, as
  `run2`'s, and the backend drives the clock: slot `2c` applies entry `c` with `clk` low, slot
  `2c + 1` raises `clk` and changes nothing else. The edge slot of cycle `c` is `2c + 1`.
  `Disciplined k` is `k.clk = some clk`; the slot list is disciplined by construction (JUDGED, not
  proved: data and reset change only in clock-low slots). It differs from `clockExpand` only in
  not re-driving the entry's data in the high slot, which leaves every input value as it is
  (JUDGED). Environments that change data in other slots are not covered.
- `progress_E1`: every edge-profile design has a behaviour under every choice and environment.
- `IncludedOnPorts M₁ M₂ k d₁ d₂ xs`: `Included` with both behaviours compared after hiding the
  ports `xs` (`hidePorts`). `Safe.of_includedOnPorts` moves any statement that does not read `xs`.
  Inclusion up to hidden ports is `IncludedOnPorts`, not `IncludedOn`, because `IncludedOn`
  restricts environments and cannot hide a port.
- `cnt_included N : IncludedOnPorts (Obs_E1 "clk") Obs_run2 cntTask.clocking (cntE N) (cntD N)
  ["clk"]`, at every `N`. The `run2` environment is E's own `rst`/`en` before each edge. Per
  cycle the two pre samples agree off `clk` (the inputs, the old `q`), and so do the two post
  samples (`q` stepped by `cntNext`: E by `cnt_rise`, `run2` by P's `cnt_cycleObs_ok`).

**The clock's observation: an assumption of the statement.** A trusted sample includes the clock
port, and the two backends disagree there by construction. E's pre sample shows the clock low and
its post sample shows it high, because E drives the edge. `run2`'s two samples both show whatever
value the stimulus entry gives the clock (none, in `cnt_included`'s environment). The inclusion is
therefore stated with `clk` hidden. It transports exactly the statements that read no clock value
from a sample. P's `cntTask` statement is one (JUDGED from `TaskV2.lean`: `Holds` reads the reset
and data inputs from the pre sample, `ObsOKS` the outputs from the post sample, `free` excludes
the clock). The assumption is that a task's guarantee never reads its clock port from a sample:
the clock belongs to the clocking discipline, not to the observed data.

**The counter's task statement over `Obs_E1` (a transport theorem).** `cnt_follows_E1 N`: over `Obs_E1 "clk"`, at
every `N`, progress, and `cntTask.Follows_obs` (P's `cnt_satisfiedAt_obs` moved along
`cnt_included` by `Safe.of_includedOnPorts`; `cnt_holds_hide`/`cnt_obsOK_hide` are the READ check
above, as theorems). The first sequential task statement over an E backend. Label (review,
integ1103): a TRANSPORT theorem, not derived from E: its safety conjunct is P's `run2` proof moved
along `cnt_included`, and "derived from E" is reserved for chains with no `run2` constant. The same
holds for `cnt_included` itself, the R-DESIGN2 inclusions and the record instances. Not covered: the
interface, admission and receptiveness conjuncts of `SatisfiedAt_obs` over `Obs_E1`.
`progress_E1` is not used by the inclusion; it is generic E-core-1 groundwork, used here only for
the progress conjunct.

**What the general comb-plus-edge composition needs** (stated, not proved): E-core-1 with comb
processes (`Proc1 := comb Proc0 | ff FF`), and one cycle as three phases. Each phase:

| phase | argument |
|---|---|
| (i) input events, comb settle | `WSettles` on the comb part, the edge processes not ready (no edge in a clock-low slot) |
| (ii) the edge slot's Active region | `rEdge`'s argument with comb processes present: no clock is a comb input; comb processes woken in Active only re-settle values the edge bodies do not read before the NBA region, so an edge body must read only signals stable in that slot |
| (iii) NBA commit, then comb settle | `WSettles` again, from the committed store |

The new hypotheses are an edge-read discipline (edge bodies read registers and settled comb
values only) and `WSettles`' invariant re-established after the commit. JUDGED about 300 lines.

## 13 Day-9 integration (integ1103): the `case` mode profile row (2026-11-03, agent A)

Master's `case` carries `mode : CaseMode` (`normal | inside | casez | casex`) where E-core-0 had
`inside : Bool`. The drift fixes (`30246aea`, `334251df`) keep E's meaning and add one profile row.

| construct | E-core-0 | `run2` | consequence |
|---|---|---|---|
| `casez`, `casex` (LRM 12.5.1) | refused: `refuse0 "12.5.1"`, `caseModeRefusal` (pinned by `Core0Smoke.casezProbe`) | executed since master `9237c380` (`caseHit` in `execStmt2`, `hitGuard` in `symExec`) | E → `run2` holds; `run2` → E fails on such designs (a narrowing). R-BODY excludes them (`staticB`/`qualFree` require `caseModeInE0`) |

The refusal is deliberate: a construct enters E with pinned rows and its own decision, not as a
side effect of a drift fix (coordinator's ruling).

**Week-2 candidate: `casez`/`casex` in E.** Needs (1) Xcelium-pinned rows for wildcard matching
under 4-state values, and (2) the one-line change (pass `mode` to the shared `caseHit`) with the
R-BODY exclusion lifted. Evidence on (1): `9237c380`'s row `symbolic_casez_casex` (cases2, six X/Z
cycles) is checked against Icarus only (READ, `docs/sv-changelog.md` 0.1.423 and
`docs/sv-charter.md`), and `harness/sv/xcelium_golden.json` has no row mentioning `casez` or
`casex` (MEASURED: string count 0). So (1) is open: an Xcelium run of `symbolic_casez_casex` and
of the wildcard 256-pair table. JUDGED cost of (2) once (1) lands: about 20 lines (the `caseHit`
change, the exclusion removed from `staticB`/`qualFree`, the probe turned into a positive pin).

**Qualified `case`: what runs, and when the violation is reported** (READ, IEEE 1800-2023, for the
review's item 1).
- 12.5.3: "The implementation shall issue a violation report and execute the statement associated
  with the matching case_item that appears first in the case statement, but not the statements
  associated with other matching case_items." And: "A priority-case shall act on the first match
  only." And: "If the case is qualified as priority or unique, the simulator shall issue a violation
  report if no case_item matches." (`default` is a case_item in the grammar, so a default that runs is
  a match; `run2`'s `checkCaseObligation` counts it the same way.)
- 12.5.3.1: the reports "shall be immune to false violation reports due to zero-delay glitches in the
  active region set", with the mechanics of 12.4.2.1.
- 12.4.2.1: the check "is evaluated at the time the statement is executed, but violation reporting
  is deferred until the Observed region of the current time step"; the pending report sits on "a
  violation report queue associated with the currently executing process"; a flush point is reached
  when an `always_comb` "is resumed due to a transition on one of its dependent signals", and then
  "its violation report queue is cleared".
- So the arm choice is fixed by the LRM (the first matching item; nothing when none matches and there
  is no default), not a profile ruling. E-core-0 today (`2d4cdd55`) refuses at the violating
  activation, which reports glitch-only violations the LRM discards; the fix (per-process pending
  report, flushed on re-activation, refused at slot close) is pending the coordinator's ruling on its
  shape (2026-11-03).

**Known divergence of E-core-0 from the LRM: qualified-case violations are refused immediately**
(coordinator's ruling (b), 2026-11-03; scheduled for week 2 with L). E-core-0 (`2d4cdd55`) checks a
`unique`/`unique0`/`priority` claim at EVERY activation of an `always_comb`, including zero-delay
transient ones, and refuses at once (`refuse0 "12.5.3"`). LRM 12.4.2.1 (12.5.3.1 by reference)
defers the report to the Observed region and flushes it when the process is re-triggered in the
same time step. So E refuses glitch-only violations that the LRM (and `run2`, which checks the
settled snapshot) accept, and whether E refuses depends on the schedule. The divergence is loud:
E refuses, it never produces a wrong value.

Retirement: the option-C design above (per-process pending report in `Config`, flushed on
re-activation, refused at slot close; a second walker `caseViol` declared beside `execBody`), plus,
in L's chain, a `SingleE.noViol` field and a lemma `claims → caseViol = none` for `slot_claimed`.
JUDGED 300–350 lines. Week-2 item for A and L.

Register row, drafted here (NOT added to `docs/sv-declared-divergences.json`: E is not on master, so
the guards would point at files master does not have; the coordinator lands it with E's push):

```json
{
  "id": "sv-div-E0-1 (number assigned on landing)",
  "kind": "semantic",
  "clause": "IEEE 1800-2023 12.5.3.1, 12.4.2.1",
  "site": "LeanModels/Sv/Kernel/Core0.lean: execBody's caseStmt arm (a violated unique/unique0/priority claim refuses inside the activation, refuse0 \"12.5.3\" (caseCheckName chk))",
  "oracle": "12.4.2.1: the check 'is evaluated at the time the statement is executed, but violation reporting is deferred until the Observed region of the current time step'; a pending report is flushed when an always_comb 'is resumed due to a transition on one of its dependent signals'. run2 checks the settled snapshot only (validateCaseChecks2, master 2218821b).",
  "model": "E-core-0 refuses at the first activation whose claim fails, including zero-delay transient activations later re-triggered with the claim holding. So it refuses glitch-only violations the LRM discards, and the refusal depends on the schedule. Loud only: no wrong value is ever produced.",
  "inherited_from": null,
  "inherited_note": "ORIGINATED in E-core-0 (arch-x1 2d4cdd55, the fidelity batch's option (a)); found by the integ1103 review.",
  "declared": "2026-11-03",
  "retirement_condition": "E-core-0's Config carries a per-process pending violation report, set by a failing claim, cleared on the process's next activation, and refused at slot close (the option-C design, X1-NOTE section 13), with L's SingleE.noViol and claims -> caseViol = none; pinned by two-schedule rows (a transient glitch flushed, a surviving violation refused under both orders, a transient priority no-match flushed).",
  "guards": ["sv_div_E0_1_still_divergent", "sv_div_E0_1_has_not_widened"],
  "guard_sketch": "still_divergent: Core0.lean's execBody still contains the in-activation refusal refuse0 \"12.5.3\" and Config has no pending field. has_not_widened: that refusal is the only 12.5.3 site in Core0.lean, and it sits in the caseStmt arm behind check != none.",
  "gated": "No claim may say E-core-0's qualified-case semantics is the LRM's, or schedule-independent, for designs whose claims can fail transiently, until this row retires."
}
```


# WP-G, G2.0: the lowering-mirror spike (plan, one page)

Status: PLAN. Nothing here has been run. The spike needs the Lean slot, which the lead will release after the Q0 agent's
L2 (`~^`) report. Until then no Lean process of mine runs.

## What the spike builds

One plain-Lean file, `spike/G20.lean`, compiled against the BUILT oleans (`LeanModels.Sv.CombViewThm`, `Comb2Proc`,
`CombGuard2Sound`, `Hier2`): no tactic, no summary, no edit to `LeanModels/**`, no `lake build` of the tree. Command
(slot rule): `$SVGOLF_LEAN_WRAP lake env lean spike/G20.lean` from the repo root. While exploring the file lives in the
work dir (`sorry` allowed there); only a `sorry`-free file is copied under `svgolf/design/always-comb/spike/`.
It proves, for ONE-LEVEL `if/else` bodies with a single window `W` and symbolic indices, the facts the lowered
`always_comb` site needs. Bodies: leaf `t = e`, `if (c) A else B`, singleton `begin S end`. Windows are abstract
`(n, lo, w)` values; every comparison between two windows is a HYPOTHESIS, never evaluated.

| id | statement (informal) | why it is here |
|---|---|---|
| A3 | generic: if every read window of `s` has a width-0 intersection (`BWin.inter`) with every write window of `s` (`Stmt2.mayW`), then `Stmt2.combViol wd M A s = none` for all `M`, `A` inside that set; so `combAdmits` holds and `combGuardProc` is the identity | the riskiest piece: a path-sensitive walk with `M`/`A` sets and `subAll` arithmetic, and the one place the carry body (reads `c[i]`, writes `c[i+1]`, same signal) needs more than "different signals" |
| S-B | the instantiation fact for the real template shape: `instStmt2 E elems (ifStmt c (assignL t v1) (some (assignL t v2)))` is `.ifStmt (instExpr2 .. none c) (.blockingAssign (acc.lhs σ') (fitExpr2 .. v1)) (some ..)` with `symWin = some (acc.win σ' dw)`, built from the existing `instLhs_acc` / `inst_leaf` / `rhs_ok` under a `Ctx` hypothesis | measures the L2 plumbing |
| A1 | `symExec d [] s = (iteExpr d s).map (fun E => [(W, E)])`, `iteExpr` = leaf `.resize w e`, if `Expr2.joinIte (ifGuard c) A B`; only reflexivity-level window facts (`W == W`, `allDisjoint [W]`), because `S = []` at every branch start; plus the helper `e.wfB d → e.symSubst d [] = some e` (a mutual induction on `Expr2`, about 50 lines: with no entry, `readWhole` gives `.ident n` and `readWin` gives the plain slice) | exact lowered shape for L1; expected mechanical |
| A2 | `[(W, E)].selfReadFree = true` from the same width-0 hypothesis, via `Expr2.reads (iteExpr s) ⊆` reads of `s` | feeds `lowerComb` |
| A4 | `∀ w ∈ s.drvWins, w = (W.1, some (W.2.1, W.2.2))` | feeds the `driversOk` guard removal |
| S-C | **headline**: for the carry template of `add_proc` (`if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i];`) at symbolic `N`, `i` with `0 ≤ i < N`: `Process2.lowerComb m (instProcess2 E elems (.alwaysComb body)) = some (.assign (.concat [W.lhs]) (.concat #[E]))`, with every window hypothesis of A1 to A4 discharged | the end-to-end test |

The semantic half (`evalPure2`/`xfBits` of `E` equals the tree's Boolean semantics), the list case (default then
override: `symSubst` against a non-empty state), `case` and multi-window states are NOT in the spike; they reuse the same
inductions and are G2.1.

## Order and checkpoints (clock starts when the slot is granted, queue time excluded)

1. T+0:45 warm-up: definitions, A1, A2, A4 compile (mechanical).
2. T+2:00 A3 compiles. If not, switch to fallback F2 for at most one hour: the `as_symExec` recipe, `simp` over
   `combViol`/`readsViol`/`BWin.inter` on the INSTANTIATED carry body with the one arithmetic fact (`i.toNat` against
   `(i+1).toNat`) by `omega`. F2 is per-design, not generic: it keeps the payoff but costs a re-proof per body shape.
3. T+3:15 S-B compiles.
4. T+4:00 S-C compiles. Stop at T+4:00 whatever the state.

## Criteria

* **GO**: S-C is proved; the only side goals are `omega`, `rfl`, string inequality of signal names and `simp` on
  `BWin.inter`; no `maxHeartbeats` above 400000; each theorem elaborates in under 20 s; the file is about 400 lines or
  fewer and `sorry`-free; `#print axioms` shows `[propext, Classical.choice, Quot.sound]`; A3 is the GENERIC lemma.
  The file then becomes the first draft of `CombProcStmt.lean`, so the work is not thrown away.
* **GO with restriction**: A3 only by F2. Proceed, but record that each new body shape (S1b, `case`, temporaries) pays a
  per-design `simp` proof; the lead decides whether S2 and S3 stay in the week.
* **NO-GO** (report and stop, as the lead ruled): A3 and F2 both open at T+3:00, or S-B needs a rewrite of `inst_leaf`/`Ctx`
  (more than about 100 lines of new infrastructure), or a heartbeat or `whnf` storm that no `simp only` set fixes. The
  report gives the goal state at the stop, the message, and the smallest library lemma that would unblock it (for
  example a statement about `SymState.write` or `BWin.subAll` on equal windows), so the lead can decide whether to
  request it from the ls-sv side.

## Pre-flight (no Lean needed by me, run through the slot)

`$SVGOLF_LEAN_WRAP lake build --no-build LeanModels.Sv.CombViewThm LeanModels.Sv.Comb2Proc LeanModels.Sv.CombGuard2Sound
LeanModels.Sv.Hier2` (if this Lake has no `--no-build`, compare the `.olean.hash` files with the source hashes instead) must report the oleans up to date; the Q0 agent's changes (genvar step, `~^`) may have touched
`Param2`/`Basic` and made some stale. If so, ask the lead whether to build the missing targets (targeted, never the root
`lake build`) or to wait. The fixtures `fixtures/add_proc.sv.json` and `add_proc_m.sv.json` (envelopes, already generated,
zero Unsupported nodes) are what `load_design_sv2` reads if S-C is run on the real design instead of a hand-built
template; the first attempt uses a hand-built `PStmt` literal, which is faster to elaborate.

## Deliverable at the end of G2.0

A one-paragraph result for the lead (GO / GO with restriction / NO-GO with numbers: lines, seconds per theorem,
heartbeats), the `sorry`-free file if GO, and the updated G2.1 estimate.

---

## RESULT (2026-10-30, 22:36 to 22:49 wall clock, queue time about 1 minute): GO

`spike/G20.lean` (629 lines with comments, 527 without; `sorry`-free; no `native_decide`/`bv_decide`), compiled with
`$SVGOLF_LEAN_WRAP lake env lean` from the repo root against the built oleans (pre-flight: `lake build --no-build` of
CombViewThm, Comb2Proc, CombGuard2Sound, Hier2 reported all targets up to date; nothing under LeanModels was touched).
Whole file: 7.3 s wall including the 4 s import and the 9 s-class `load_design_sv2` check; elaboration about 1.9 s
(simp 0.83 s, tactic execution 0.71 s); NO single theorem over the profiler's 100 ms threshold except one simp at 126 ms;
it compiles with `-DmaxHeartbeats=40000` (a fifth of the default). Axioms: `[propext, Classical.choice, Quot.sound]`
at most (several theorems need only `propext, Quot.sound`).

| item | theorem | note |
|---|---|---|
| helper | `symSubst_nil` : `e.wfB d` implies `e.symSubst d [] = some e` | generic, mutual size induction, about 70 lines |
| A1 | `symExec_tree` | `(t.toStmt tgt).symExec d [] = some [(W, t.low W.2.2)]`, for ANY target `tgt` with `tgt.symWin d = some W` (whole signal or slice) |
| A2 | `selfReadFree_tree`, `low_reads` | |
| A3 | `combViol_tree`, `combAdmits_tree` (+ `BWin.subAll_nil_of_zero`, `readsViol_none`, `mayW_tree`) | the generic lemma; the whole proof is "a zero-width intersection subtracts to `[]`", no symbolic window arithmetic |
| A4 | `drvWins_tree` | members of `(t.toStmt tgt).drvWins` are members of `tgt.drvWins` |
| bridge | `rdW_of_reads`, `noRdW_of_noRead` | the summary's window-level (`ReadWin`) non-overlap implies the bit-level one the guard walks; needs only "no `index` node" (`Expr2.idxFree`), true after instantiation of constant selects |
| semantics | `low_xfWidth`, `low_xfBits` | the lowered `joinIte (ifGuard c) A B` has width `w` and Boolean bit `if c.bit 0 then A.bit k else B.bit k` (the `Expr2.same` collapse included): exactly the displayed equation shape |
| S-B | `instStmt2_tree`, `instProcess2_tree` | the instantiation of a template tree IS the Expr2 tree, with the guard on top; 25 lines |
| generic S-C | `lower_tree`, `lower_tree'` | `Process2.lowerComb d (combGuardProc wd (t.body tgt)) = some (.assign (.concat [W.lhs]) (.concat #[t.low W.2.2]))` from window-level hypotheses only |
| S-C | `carry_lowers` | the `add_proc` carry cell (`if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i];`) at SYMBOLIC `N`, `k < N`, an arbitrary `IEnv`/`elems` satisfying three lookups, lowers to the explicit assign `{c[k+1]} = {ifGuard(p[k]) ? resize(c[k]) : resize(a[k])}`; plus a `#guard` that the template really is the process the extractor's envelope for `fixtures/add_proc.sv` ingests |

Criteria check: S-C proved (yes); side goals only `omega`, `rfl`, string inequality and `simp` on `BWin.inter` (yes); no
`maxHeartbeats` above the default (yes, 40000 suffices); each theorem well under 20 s (yes); about 400 lines (527 without
comments: over, because the semantic half, the rdW bridge and the helper were added after S-C passed; the core A1 to A4,
S-B and S-C is about 330); A3 generic (yes). No fallback F2 was needed.

What the spike does NOT cover (the remaining risk, all in G2.1/G2.2): the summary-side plumbing, i.e. the `Acc` target forms
reaching `instLhs2 ... = .ok (tgt, w)` with `w = W.2.2` (existing `instLhs_acc`, which does not state the width equality),
`wfB` of the fitted leaves from `RdOK`, `Realized` over the lowered pairs, `sound_pairs` without `pairs_desc`, the driver-guard
removal (`driversOk` from `DisjObl` via A4), and `eq_of_summary` for the lowered design. The updated estimate is in the report.
One slot-rule slip: a single 5 s `lake env lean` ran without the wrapper (an unset shell variable in my command); nothing
else ran outside the Lean-slot wrapper.

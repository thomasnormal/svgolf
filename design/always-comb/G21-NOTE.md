# WP-G, G2.1: the template side of `always_comb`, and the G2.2 plan

Status (2026-10-30, 23:40): **G2.1 is complete.** Two NEW, additive modules in `LeanModels/Sv/`, built with
targeted `lake build LeanModels.Sv.<Module>` through the slot; no existing LeanModels file was edited
(`git status`: the two files are the only untracked entries under `LeanModels/`, `git diff -- LeanModels` is empty).

| file | lines | declarations | build | warnings | sorry/admit/native_decide/bv_decide |
|---|---|---|---|---|---|
| `LeanModels/Sv/CombProcStmt.lean` | 674 | 35 (24 theorems pinned) | 1.2 s (lake), 2.6 s CPU standalone | 0 | 0 |
| `LeanModels/Sv/CombProc.lean` | 752 | 38 (19 theorems pinned, 8 `#guard`s) | 1.2 s (lake), 5.7 s wall / 2.4 s CPU standalone incl. the 4 s import | 0 | 0 |

Every theorem carries a `#guard_msgs` pin on `#print axioms`; the results are `[propext, Classical.choice,
Quot.sound]` at most (several need only `propext`, `treeStmt?_spec` and `treeStmts?_spec` exactly `[propext]`,
`lhs_eq_win_lhs` and `ap_symNames` none). Default heartbeats throughout; no `set_option` except a linter switch
on one theorem. Module docstrings carry the fragment S1 statement and the soundness story.

## 1. The two items the lead named

**The `Acc` target forms reach `instLhs2 ... = .ok (tgt, w)` with `w = W.2.2`: this is already a library
theorem, `CombEq.instLhs_acc_w`** (CombEqShape.lean), stated for every `Acc` form the summary writes (whole
signal, bit, 1-D cell, row, 2-D cell, part of a 1-D vector, part of a row). The G2.0 spike had used it only by
hand for `bit`. `CombProc.tree_tgt` lifts it to every leaf of a template tree (`PT.Tgt`), and `CombProc.tgt_facts`
derives from `AccOK` and the in-range fact `hin` (the summary's `InRangeObl`) the three facts the lowering and
the guard read about the lowered target: `(tg.lhs σ).symWin d = some (tg.win σ dw)`, `mayW = [tg.win σ dw]`,
`rdW = []`. A whole-signal target (`Acc.whole`, lowered to `.ident n`) and every other form are covered
(`lhs_eq_win_lhs` for the slice forms).

**`wfB` of the fitted leaves comes from `RdOK`.** `CombProc.low_wf`: every expression of the instantiated tree
satisfies `Expr2.wfB d`, with `unsupportedFree` and `idents ⊆ names` from `CombViewThm.rhs_ok` (leaves, fitted to
the target width) and `CombViewThm.inst_rd` (conditions), and the names declared in `d` because
`d.declWidth = DW` (the summary's widths, `CombView.declWidth_eq`). No width obligation is needed.

Two further facts were not in the library and are proved: the instantiated expressions contain no `index` node
(`inst_idxFree`, `rhs_idxFree`, `low_idxFree`, from `CombEq.leaf_eq`), which is what lets the summary's
window-level non-overlap (`low_noRead`, from the `noSelfRead` obligation) give the guard's bit-level one
(`CombProcStmt.rdW_of_reads`, `noRdW_of_noRead`).

## 2. What is in the files

`CombProcStmt.lean` (generic: `PTree` = leaf | `if/else` | `begin..end`, expressions as hypotheses; G2.0 plus the
`blk` node, plus the guard applied to the tree statement itself): `symSubst_nil`, `symExec_tree`,
`selfReadFree_tree`, `low_reads`, `drvWins_tree`, `mayW_tree`, `combViol_tree`, `combAdmits_tree`,
`readsViol_none`, `BWin.subAll_nil_of_zero`, `rdW_of_reads(_aux)`, `noRdW_of_noRead`, `ifGuard_xfWidth/Bits`,
`low_xfWidth`, `low_xfBits`, `lower_tree`, **`lower_tree'`**.

`CombProc.lean` (template side): `PT`/`PTR` (template tree, and the tree annotated with the reads `rdsOf?`
found), `PT.toPStmt`, `PT.low`, `PT.Tgt`, `instStmt2_tree`, **`instProcess2_tree`** (the instantiation of a
template tree IS the `PTree` statement under `combGuardProc`), `inst_idxFree`, `low_idxFree`, `low_wf`,
`low_noRead`, `tgt_facts`, `tree_tgt`, **`lower_site`**, the recognizer `treeStmt?`/`treeStmts?`/`procTree?` with
the tactic's messages and its inversion `treeStmt?_spec`/`treeStmts?_spec`, and the non-vacuity section.

**`lower_site`** (the headline): for a recognized tree `ptr` (all leaves assign the access `tg`, every node passed
`rhsRds?/fragOk` or `rdsOf?/fragG`), `tg` and every read in range and declared, and no read window overlapping
`tg.win σ dw`, in any `Ctx`:
`Process2.lowerComb d (instProcess2 E elems ptr.pt.toProc) = some (.assign (.concat [(tg.win σ dw).lhs])
(.concat #[(ptr.pt.low E elems (tg.win σ dw).2.2).low (tg.win σ dw).2.2]))`.

Non-vacuity (`#guard`s and one theorem, in `CombProc.lean`): the recognizer accepts the `add_proc` carry cell
(hand-built `DeclT`s with symbolic `N`), finds target `c[i+1]` and the reads `[p[i], c[i], a[i]]`, accepts a
whole-signal `else if` chain, and refuses with the planned message: `if` without `else`, a second target, several
statements, `case`, nonblocking assignment. `carry_lowers`: the carry cell lowers, at symbolic `N` and any bit
`k < N`, to `assign {c[k+1]} = {ifGuard(p[k]) ? c[k] : a[k]}`. `Examples/system-verilog/comb_proc` (G2.3) will
check that the template equals what `load_design_sv2` ingests from `fixtures/add_proc.sv`.

## 3. The fragment S1 as implemented

`always_comb` whose body is a tree: `begin T end`, `T ::= t = v; | n = v; | if (c) T else T | begin T end`; each
leaf assigns the SAME access (`tgtOf?` result, compared with `=` on `Acc`: `c[i+1]` and `c[1+i]` are one window), each
`v` in the `sv_equations` right-hand-side fragment (`rhsRds?`, `fragOk`), each `c` a gate tree (`rdsOf?`, `fragG`).
Refused with a message: `if` without `else` (latch), a second target, a block of several statements (this
includes `y = a; if (c) y = b;`), `case`, nonblocking assignments, unsupported kinds. The self-read rule is the
obligation `noSelfRead_k` (`low_noRead`'s hypothesis); the loader's own guard refuses the same bodies earlier.
Deferred (sequential substitution, Gate-1 note S3): default-then-override and temporaries; S2: `?:`, `!`, `~`,
reductions, `&& ||`.

## 4. G2.2: what it touches in EXISTING files

The lowered design `d'` is what the settle theory sees, so `sv_structure`/`sv_equations` need, about `d'`, the
facts they have today about `instantiate2`'s output. Everything below is the minimal set found by reading the
users of each declaration (`grep` over `LeanModels/Sv`); "A" = purely additive (new lemma/def, no existing text
changes), "D" = a definition changes (same signature), "S" = a statement or signature changes (consumers must
follow), "T" = shared tactic code.

| file | declaration | change | kind |
|---|---|---|---|
| new `CombProcLower.lean` | `Summary.sound_core`, `Summary.pairsL`, `Summary.sound_lowered`, `driversOk_of_lowered`, `realized_lowered`, `eq_of_summary_lowered`, `CombLowered` | the lowered chain (R2, R3, R4 below) | A |
| new `CombProcTactic.lean` | `elab_rules` for `sv_structure`, `sv_interface`, `sv_equations` on the lowered goal | additional rules that `throwUnsupportedSyntax` unless the goal is `∃ d', lowerComb .. ∧ CombDesign d' ∧ Acyclic d'`; the old rules and their output are untouched | A (T-adjacent: new elaborators, shared syntax) |
| `CombView.lean` | `siteOf?` | the `.alwaysComb` arm (today the error `procedural process (`always`): outside the combinational-assign fragment`) calls `procTree?`; sets `tgt := tg`, `rds := ptr.rds`, `proc := p` | D |
| `CombView.lean` | `LSite.inst` | `tgt` for a proc site (`ls.site.proc = .alwaysComb _`) is `.concat [(win).lhs]`, the lowered target | D (a `match` in one field; proofs that unfold `LSite.inst` re-check) |
| `CombViewThm.lean` | `siteOf?_cases` | a third disjunct (the `alwaysComb` case) | S: consumers `site_desc` (CombViewThm:721), `proc_shape` (CombEqShape:377), `site_sk` (CombEqThm:117) and the `siteOf?_proc` users get a third branch |
| `CombViewThm.lean` | `site_desc` | proc branch: `Desc` of the LOWERED process (from `lower_site` + `low_noRead`-style reads inclusion); `pairs_desc` case-splits | S (new case; statement of `pairs_desc` is about the lowered process list) |
| `CombViewMain.lean` | `inst_facts`, `realized_comb`, `realized_acyclic` | the conjunct `∀ ps, a.tgt ≠ .concat ps` becomes "`a.tgt.wins m = [a.win]`" (a one-leaf concat has one window); `selfDisjoint` uses it instead of `Lhs2.wins_pairwise_of_leaf` | S (one conjunct; three use sites) |
| `CombViewSound.lean` | `Summary.sound` | unchanged; its body is factored (a copy suffices) into `sound_core` without `pairs_desc` | A (copy) or D (refactor) |
| `CombEqThm.lean` | `sound_pairs`, `eq_of_summary`, `eq_view`, `EqSite` | `eq_of_summary_lowered` is a COPY with the lowered process list; `EqSite` for a proc site is a new def `EqSiteP` (the tree's Boolean reading) with a dispatcher | A (copy) + S if `EqSite` itself gains the dispatch |
| `CombEqBase.lean` | `rhsOf`, `EqFrag` | `EqFrag`/`fragOk` of a proc site is `PTR.Ok` | D |
| `CombViewTactic.lean`, `CombEqTactic.lean` | `sv_norm_core`, `sv_eq_norm`, `sv_eq_norm_at` simp sets; `runSvStructure`'s goal shapes | the new definitions (`PTree.*`, `PTR.*`, `EqSiteP`) join the simp sets; the goal-shape detection learns the lowered shape (or the new elab_rules do it) | T |

Order of the edits that keeps the old outputs byte-identical (checked as WP-F did, goal dumps of `add_n`,
`mul_n`, `mul_tree`, `mul_tree_h`, `mul_wallace`): first the additive modules (they compile against the
unchanged library), then the D/S edits in dependency order (CombView, CombViewThm, CombViewMain/CombViewSound,
CombEqBase/Shape/Thm), then the tactic files last. Everything below `CombView.lean` rebuilds on the D edit of
`LSite.inst`: about the whole `Sv` comb chain plus every Example and svGolf reference (the 75-minute suite).

**Recommendation: a worktree from `github/master`** for the D/S/T rows (they touch 7 existing files and force a full
rebuild), with the additive modules (`CombProcStmt`, `CombProc` now; `CombProcLower`, `CombProcTactic` later) developed
against it. The two modules already in the shared tree do not depend on any pending edit.

## 5. The G2.2 risks, each with a plan (updated)

**R1. `Realized` over the lowered pairs.** `Desc` is `p = .assign si.tgt e ∧ reads ⊆ si.rd ∧ unsupportedFree ∧
idents ⊆ names`. For a proc site the lowered process is `.assign (.concat [W.lhs]) (.concat #[low])`; with
`LSite.inst` as in section 4 the equality is definitional, `reads ⊆ rds` is the inclusion version of `low_noRead`
(same induction, `joinIte`'s two shapes), the rest is `low_wf`. `realized_comb`/`realized_acyclic` then run
unchanged but for the `inst_facts` conjunct. Medium, 1/2 day.

**R2. The `sound_pairs` variant.** `Summary.sound_core` = `sound_pairs` minus `pairs_desc` (the instantiation `m`,
`m.processes.toList = (s.pairs ..).map snd`, `Ctx`). `Summary.pairsL` replaces each pair's process by
`(p.lowerComb m).getD p`; `sound_lowered : ∃ m d', instantiate2 = .ok m ∧ m.lowerComb = some d' ∧
d'.processes.toList = (pairsL ..).map snd`, from `Design2.lowerComb`'s definition (`lowerProcs` is a map when
each process lowers) and, per site, `site_desc` (assign) or `lower_site` (proc). Medium, 1/2 day.

**R3. Removing the driver guard.** `instantiateGD2 = driverGuard (instantiate2 ..)`; today
`instantiateGD2_of_combDesign` derives `driversOk` from `CombDesign m`. For a design with `always_comb`, `m` is not a
comb design. `driversOk_of_lowered`: from `CombDesign d'` (disjoint windows, no input driven), `drvWins_tree` (each
body's `Stmt2.drvWins` is its target's), and `Hier2`'s `driverWins`/`procWins`/`procExclusiveOk`/`DrvWin.overlaps`
(`DrvWin = (name, Option (lo, w))`; for the slice/ident targets of the fragment `DrvWin.overlaps` is
`Win.overlaps`, a whole-signal target is `none`, "every bit"). List lemmas on `flatMap`/`filter`. Medium, the largest
single item, 1 day.

**R4. `eq_of_summary` for the lowered design.** `CombKnown.settled` applies to `d'` unchanged (a one-leaf concat
target is a placed window of offset 0). New: `EqSiteP` = `st.boolAt n (lo+k) = PSk.bit ..`. Plan: (a)
`cond_shape`: `instExpr2 E elems none c = (skT c rc).low σ 1` for a width-1 gate tree (the `none`-context twin of
`CombEq.gate_shape`: `selfWidth2 = some 1` for gate trees, then `instExpr2_gate` with `maxW2 (some 1) (some 1)`);
(b) `PSk` (skeleton tree) with `PSk.bit`; `PT.low = PSk.low` under `WidthOk` (`rhs_shape` for leaves); (c)
`CombProcStmt.low_xfWidth/low_xfBits` (done) with `CombEq.low_xfWidth/low_xfBits` give `d'`'s `XFree` and the
equation `if c then a else b`; (d) `Covered`/`Sourced` for the lowered reads (the `cover_k` obligation already
quantifies over the site's reads, conditions included). The knownness of a CONDITION is not a separate step: it is
a read of the process, covered like any other (`reads_known`). The aliases (Gate-1 note, 3.4) need no change for
single-window sites. High on plumbing, not on mathematics; 1 to 1.5 days.

**R5. Tactic front end, messages, names.** `sv_structure` on `∃ d', (X.sem N).lowerComb = some d' ∧ CombDesign d' ∧
Acyclic d'` applies `sound_lowered` and returns the same obligations as today plus `noSelfRead_k`; `sv_interface`
takes the lowering hypothesis; `sv_equations` finds `heqs : CombEqs d' st` and the lowering. The recognizer's text
is prefixed by the site as today. 1 day with the examples (G2.3).

Total G2.2: about 4 to 5 days if R3 and R4 go as planned; the first measurable milestone is R2 (the lowered
`Realized`), after which `CombDesign d' ∧ Acyclic d'` for `add_proc` is a `decide`-and-`omega` proof away.

## 6. Not done in G2.1, and why

* Default-then-override and temporaries (sequential substitution; S3). `?:`, `!`, `~`, reductions, logical
  operators (S2).
* Wiring `procTree?` into `siteOf?` (a G2.2 edit to an existing definition).
* A `load_design_sv2` check of the template (needs the fixture envelope: `Examples`, G2.3).

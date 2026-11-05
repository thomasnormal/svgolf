/-
# X12: `Std.Do` / `mvcgen` on E-core-0's `execBody` (a measurement probe)

**Historical, not ported.** Pinned to the commit it measured (`c7b56d30`, arch-loop, the build it compiled against).
It does not typecheck against master's `CaseMode`, and nothing builds it (`compile-measure.sh` builds the
current instruments only).

ARCH-NOTE §7 X12 / EXECUTION-PLAN Day 8. Imported by nothing. It needs agent A's `Kernel.Core0*` (arch-x1) and agent
L's `Loop2E` (arch-loop, which merges arch-x1), so it is compiled against arch-loop's build, read-only:

  cd <arch-loop worktree> && $SLOT lake env lean <this file>

Every theorem is wrapped in `count_hb` (core's `IO.getNumHeartbeats` before and after the command, with
`Elab.async false`, as in X7). Three routes prove the same statement about two `always_comb` bodies:
* **L**: L's `DenotesE` primitives (`Loop2E.lean`), composed;
* **A**: A's one-step lemmas (`execBody_assign_run`, `execBody_if_run`, `SemMWith.run_bind_ok`), by hand;
* **mvcgen**: a `Std.Do` triple, closed by `mvcgen`, then turned into the same statement by a bridge.
-/
import LeanModels.Sv.Loop2E
import Lean

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Lean Elab Command in
elab "count_hb " "in " cmd:command : command => do
  let h0 ← IO.getNumHeartbeats
  elabCommand cmd
  let h1 ← IO.getNumHeartbeats
  let pos := (← getFileMap).toPosition (cmd.raw.getPos?.getD 0)
  logInfo m!"X12HB {pos.line} {h1 - h0}"

open Std.Do LeanModels LeanModels.Sv LeanModels.Sv.Kernel LeanModels.Sv.Loop2

namespace X12

/-! ## The two bodies -/

abbrev E1 : Elab := Core0Smoke.mux1

def B1a : Stmt2 := .blockingAssign (.ident "t") (.binary .and (.ident "a") (.ident "b"))
def B1b : Stmt2 := .ifStmt (.ident "c") (.blockingAssign (.ident "y") (.ident "t"))
  (some (.blockingAssign (.ident "y") (.unary .bnot (.ident "t"))))

/-- G-B's fixture body: `begin t = a & b; if (c) y = t; else y = ~t; end`. -/
def B1 : Stmt2 := .block #[B1a, B1b]

/-- `B1` is `mux1`'s `always_comb` body, verbatim. -/
example : (match E1.procs[2]? with | some (Proc0.comb b) => some b | _ => none) = some B1 := rfl

/-- A loop-free `always_comb` with an `if/else` and two writes per branch: `if (c) begin x = a; y = b; end else
begin x = b; y = a; end`. -/
def B2t : Stmt2 := .block #[.blockingAssign (.ident "x") (.ident "a"), .blockingAssign (.ident "y") (.ident "b")]
def B2e : Stmt2 := .block #[.blockingAssign (.ident "x") (.ident "b"), .blockingAssign (.ident "y") (.ident "a")]
def B2 : Stmt2 := .ifStmt (.ident "c") B2t (some B2e)

def E2 : Elab where
  decls := #[{ name := "a", width := 4, isInput := true }, { name := "b", width := 4, isInput := true },
             { name := "c", width := 1, isInput := true }, { name := "x", width := 4 }, { name := "y", width := 4 }]
  procs := #[.comb B2]

/-! ## The specifications (what L's primitives compose to) -/

abbrev I1 : SvState → Prop := BoundAll ["a", "b", "c", "t", "y"]
abbrev I2 : SvState → Prop := BoundAll ["a", "b", "c", "x", "y"]

def eT : Expr2 := .binary .and (.ident "a") (.ident "b")

/-- One whole-signal write on the view: `DenotesE.assignE`'s function. -/
def wr (n : String) (e : Expr2) (st : SvState) : SvState :=
  SvState.set st n ((valE st e).resizeU (sig st n).width)

def g1 (st : SvState) : SvState :=
  if (valE (wr "t" eT st) (.ident "c")).condTrue then wr "y" (.ident "t") (wr "t" eT st)
  else wr "y" (.unary .bnot (.ident "t")) (wr "t" eT st)

def g2 (st : SvState) : SvState :=
  if (valE st (.ident "c")).condTrue then wr "y" (.ident "b") (wr "x" (.ident "a") st)
  else wr "y" (.ident "a") (wr "x" (.ident "b") st)

theorem bnd {ns : List String} {st : SvState} (h : BoundAll ns st) {l : List String}
    (hl : ∀ x ∈ l, x ∈ ns) : ∀ x ∈ l, ∃ v, SvState.lookup st x = some v := fun x hx => h x (hl x hx)

theorem h4_1 : AllFour E1 := by unfold AllFour; decide
theorem h4_2 : AllFour E2 := by unfold AllFour; decide

/-! ## Route L: L's `DenotesE` primitives -/

count_hb in
theorem B1_L : DenotesE E1 I1 B1 g1 := by
  refine (DenotesE.block (DenotesLE.cons (DenotesE.assignE (W := 4) h4_1 rfl rfl ?_) ?_
    (DenotesLE.cons (DenotesE.ite (b := some _) rfl ?_ (DenotesE.assignE (W := 4) h4_1 rfl rfl ?_)
      (DenotesE.assignE (W := 4) h4_1 rfl rfl ?_)) ?_ (DenotesLE.nil _ _)))).congr fun st _ => rfl
  all_goals first
    | (intro st h; exact bnd h (by decide))
    | (intro st h; exact h.set _ _)
    | (intro st h; split <;> exact h.set _ _)

count_hb in
theorem B2_L : DenotesE E2 I2 B2 g2 := by
  refine (DenotesE.ite (b := some _) rfl ?_
    (DenotesE.block (DenotesLE.cons (DenotesE.assignE (W := 4) h4_2 rfl rfl ?_) ?_
      (DenotesLE.cons (DenotesE.assignE (W := 4) h4_2 rfl rfl ?_) ?_ (DenotesLE.nil _ _))))
    (DenotesE.block (DenotesLE.cons (DenotesE.assignE (W := 4) h4_2 rfl rfl ?_) ?_
      (DenotesLE.cons (DenotesE.assignE (W := 4) h4_2 rfl rfl ?_) ?_ (DenotesLE.nil _ _))))).congr
    fun st _ => rfl
  all_goals first
    | (intro st h; exact bnd h (by decide))
    | (intro st h; exact h.set _ _)

/-! ## Route A: A's one-step lemmas, by hand -/

/-- One whole-signal write of a declared 4-bit signal, on the store and on the view (the step every hand proof
repeats). -/
theorem step_wr {E : Elab} (h4 : AllFour E) {σ : Store} (hT : E.Typed σ) {n : String} {e : Expr2}
    {I : SvState → Prop} (hW : E.toDesign2.declWidth n = some 4) (hs : simpleExpr e = true)
    (hb : ∀ x ∈ e.idents, ∃ v, SvState.lookup (E.view σ) x = some v) :
    execBody E (.blockingAssign (.ident n) e) σ
        = .ok (.ok (), E.writeWin σ n 0 ((valE (E.view σ) e).resizeU 4)) ∧
      E.Typed (E.writeWin σ n 0 ((valE (E.view σ) e).resizeU 4)) ∧
      E.view (E.writeWin σ n 0 ((valE (E.view σ) e).resizeU 4)) = wr n e (E.view σ) := by
  refine ⟨execBody_assign_run (staticWin_ident hW) (evalPure2_valE hs hb), hT.writeWin _ _ _, ?_⟩
  obtain ⟨h1, h2⟩ := view_writeWin_decl hT h4 hW 0 ((valE (E.view σ) e).resizeU 4)
  rw [h1, insertAt_full (by rw [width_resizeU, h2])]
  simp only [wr, h2]

count_hb in
theorem B1_A : DenotesE E1 I1 B1 g1 := fun σ hT hI => by
  obtain ⟨r1, hT1, hv1⟩ := step_wr (E := E1) (n := "t") (e := eT) (I := I1) h4_1 hT rfl rfl (bnd hI (by decide))
  obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = E1.writeWin σ "t" 0 ((valE (E1.view σ) eT).resizeU 4) := ⟨_, rfl⟩
  rw [← hσ1] at r1 hT1 hv1
  have hI1 : I1 (E1.view σ1) := by rw [hv1]; exact hI.set _ _
  have hc := evalPure2_valE (st := E1.view σ1) (e := .ident "c") rfl (bnd hI1 (by decide))
  have key : ∃ σ2, execBody E1 B1b σ1 = .ok (.ok (), σ2) ∧ E1.Typed σ2 ∧ E1.view σ2 = g1 (E1.view σ) := by
    rw [show B1b = .ifStmt (.ident "c") (.blockingAssign (.ident "y") (.ident "t"))
      (some (.blockingAssign (.ident "y") (.unary .bnot (.ident "t")))) from rfl, execBody_if_run hc]
    by_cases hC : (valE (E1.view σ1) (.ident "c")).condTrue = true
    · obtain ⟨r2, hT2, hv2⟩ := step_wr (E := E1) (n := "y") (e := .ident "t") (I := I1) h4_1 hT1 rfl rfl
        (bnd hI1 (by decide))
      refine ⟨_, by rw [if_pos hC]; exact r2, hT2, ?_⟩
      rw [hv2, hv1, g1, if_pos (by rw [← hv1]; exact hC)]
    · obtain ⟨r2, hT2, hv2⟩ := step_wr (E := E1) (n := "y") (e := .unary .bnot (.ident "t")) (I := I1) h4_1 hT1
        rfl rfl (bnd hI1 (by decide))
      refine ⟨_, by rw [if_neg hC, execBodyOpt_some]; exact r2, hT2, ?_⟩
      rw [hv2, hv1, g1, if_neg (by rw [← hv1]; exact hC)]
  obtain ⟨σ2, r2, hT2, hv2⟩ := key
  refine ⟨σ2, ?_, hT2, hv2⟩
  rw [show execBody E1 B1 = execBodyList E1 [.blockingAssign (.ident "t") eT, B1b] from rfl, execBodyList_cons,
    SemMWith.run_bind_ok r1, execBodyList_cons, SemMWith.run_bind_ok r2, execBodyList_nil]

count_hb in
theorem B2_A : DenotesE E2 I2 B2 g2 := fun σ hT hI => by
  have hc := evalPure2_valE (st := E2.view σ) (e := .ident "c") rfl (bnd hI (by decide))
  rw [show B2 = .ifStmt (.ident "c") B2t (some B2e) from rfl, execBody_if_run hc]
  by_cases hC : (valE (E2.view σ) (.ident "c")).condTrue = true
  · rw [if_pos hC, show execBody E2 B2t = execBodyList E2 [.blockingAssign (.ident "x") (.ident "a"),
      .blockingAssign (.ident "y") (.ident "b")] from rfl]
    obtain ⟨r1, hT1, hv1⟩ := step_wr (E := E2) (n := "x") (e := .ident "a") (I := I2) h4_2 hT rfl rfl
      (bnd hI (by decide))
    obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = E2.writeWin σ "x" 0 ((valE (E2.view σ) (.ident "a")).resizeU 4) := ⟨_, rfl⟩
    rw [← hσ1] at r1 hT1 hv1
    have hI1 : I2 (E2.view σ1) := by rw [hv1]; exact hI.set _ _
    obtain ⟨r2, hT2, hv2⟩ := step_wr (E := E2) (n := "y") (e := .ident "b") (I := I2) h4_2 hT1 rfl rfl
      (bnd hI1 (by decide))
    refine ⟨_, ?_, hT2, ?_⟩
    · rw [execBodyList_cons, SemMWith.run_bind_ok r1, execBodyList_cons, SemMWith.run_bind_ok r2, execBodyList_nil]
    · rw [hv2, hv1, g2, if_pos hC]
  · rw [if_neg hC, execBodyOpt_some, show execBody E2 B2e = execBodyList E2 [.blockingAssign (.ident "x") (.ident "b"),
      .blockingAssign (.ident "y") (.ident "a")] from rfl]
    obtain ⟨r1, hT1, hv1⟩ := step_wr (E := E2) (n := "x") (e := .ident "b") (I := I2) h4_2 hT rfl rfl
      (bnd hI (by decide))
    obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = E2.writeWin σ "x" 0 ((valE (E2.view σ) (.ident "b")).resizeU 4) := ⟨_, rfl⟩
    rw [← hσ1] at r1 hT1 hv1
    have hI1 : I2 (E2.view σ1) := by rw [hv1]; exact hI.set _ _
    obtain ⟨r2, hT2, hv2⟩ := step_wr (E := E2) (n := "y") (e := .ident "a") (I := I2) h4_2 hT1 rfl rfl
      (bnd hI1 (by decide))
    refine ⟨_, ?_, hT2, ?_⟩
    · rw [execBodyList_cons, SemMWith.run_bind_ok r1, execBodyList_cons, SemMWith.run_bind_ok r2, execBodyList_nil]
    · rw [hv2, hv1, g2, if_neg hC]

/-! ## Route mvcgen: a `Std.Do` triple -/

-- `ofRes` of a successful evaluation: the value, the store unchanged. The answer is in the postcondition (the
-- pilot's lesson, docs/mvcgen-pilot.lean). The `.ok v = r` orientation matters: the other one makes `simp_all`
-- rewrite the evaluated value into the bound variable, after which no `writeWin … (v.resizeU 4)` lemma matches.
count_hb in
@[spec] theorem ofRes_spec {α : Type} (r : Res α) (s0 : Store) (h : ∃ v, r = .ok v) :
    ⦃fun s => ⌜s = s0⌝⦄ ofRes r ⦃⇓ v => fun s => ⌜.ok v = r ∧ s = s0⌝⦄ := by
  obtain ⟨v, rfl⟩ := h
  mvcgen [ofRes]

theorem stW_t : Lhs2.staticWin E1.toDesign2 (.ident "t") = some ("t", 0, 4) := rfl
theorem stW_y : Lhs2.staticWin E1.toDesign2 (.ident "y") = some ("y", 0, 4) := rfl

theorem stW_x2 : Lhs2.staticWin E2.toDesign2 (.ident "x") = some ("x", 0, 4) := rfl
theorem stW_y2 : Lhs2.staticWin E2.toDesign2 (.ident "y") = some ("y", 0, 4) := rfl

/-! ## Route mvcgen, closed

The verification conditions are closed by `simp_all` over the facts every route needs: the declared signals are
bound in a typed store (`Elab.lookup_declared`), a whole-signal write is `SvState.set` on the view (`vw`, from L's
`view_writeWin_decl`), typedness is preserved (`Elab.Typed.writeWin`). -/

theorem vw {E : Elab} (h4 : AllFour E) {σ : Store} (hT : E.Typed σ) {n : String}
    (hW : E.toDesign2.declWidth n = some 4) (v : LVec) :
    E.view (E.writeWin σ n 0 (v.resizeU 4)) = SvState.set (E.view σ) n (v.resizeU 4) := by
  obtain ⟨h1, h2⟩ := view_writeWin_decl hT h4 hW 0 (v.resizeU 4)
  rw [h1, insertAt_full (by rw [width_resizeU, h2])]

theorem vw1_t {σ : Store} (hT : E1.Typed σ) (v : LVec) :
    E1.view (E1.writeWin σ "t" 0 (v.resizeU 4)) = SvState.set (E1.view σ) "t" (v.resizeU 4) := vw h4_1 hT rfl v
theorem vw1_y {σ : Store} (hT : E1.Typed σ) (v : LVec) :
    E1.view (E1.writeWin σ "y" 0 (v.resizeU 4)) = SvState.set (E1.view σ) "y" (v.resizeU 4) := vw h4_1 hT rfl v
theorem vw2_x {σ : Store} (hT : E2.Typed σ) (v : LVec) :
    E2.view (E2.writeWin σ "x" 0 (v.resizeU 4)) = SvState.set (E2.view σ) "x" (v.resizeU 4) := vw h4_2 hT rfl v
theorem vw2_y {σ : Store} (hT : E2.Typed σ) (v : LVec) :
    E2.view (E2.writeWin σ "y" 0 (v.resizeU 4)) = SvState.set (E2.view σ) "y" (v.resizeU 4) := vw h4_2 hT rfl v

count_hb in
theorem B1_mv (σ0 : Store) (hT : E1.Typed σ0) (hI : I1 (E1.view σ0)) :
    ⦃fun s => ⌜s = σ0⌝⦄ execBody E1 B1
    ⦃⇓ _ => fun s => ⌜E1.Typed s ∧ E1.view s = g1 (E1.view σ0)⌝⦄ := by
  obtain ⟨va, ha, wa⟩ := Elab.lookup_declared hT (E := E1) (n := "a") (dw := 4) rfl
  obtain ⟨vb, hb, wb⟩ := Elab.lookup_declared hT (E := E1) (n := "b") (dw := 4) rfl
  obtain ⟨vc, hc, wc⟩ := Elab.lookup_declared hT (E := E1) (n := "c") (dw := 1) rfl
  obtain ⟨vt, ht, wt⟩ := Elab.lookup_declared hT (E := E1) (n := "t") (dw := 4) rfl
  obtain ⟨vy, hy, wy⟩ := Elab.lookup_declared hT (E := E1) (n := "y") (dw := 4) rfl
  rw [show execBody E1 B1 = execBodyList E1 [B1a, B1b] from rfl]
  simp only [B1a, B1b, execBody, execBodyList, execBodyOpt, stW_t, stW_y]
  mvcgen
  all_goals simp_all [vw1_t, vw1_y, Elab.Typed.writeWin, CombGuard.lookup_set_self, CombGuard.lookup_set_ne,
    g1, wr, eT, valE, sig, readSignal]

count_hb in
theorem B2_mv (σ0 : Store) (hT : E2.Typed σ0) (hI : I2 (E2.view σ0)) :
    ⦃fun s => ⌜s = σ0⌝⦄ execBody E2 B2
    ⦃⇓ _ => fun s => ⌜E2.Typed s ∧ E2.view s = g2 (E2.view σ0)⌝⦄ := by
  obtain ⟨va, ha, wa⟩ := Elab.lookup_declared hT (E := E2) (n := "a") (dw := 4) rfl
  obtain ⟨vb, hb, wb⟩ := Elab.lookup_declared hT (E := E2) (n := "b") (dw := 4) rfl
  obtain ⟨vc, hc, wc⟩ := Elab.lookup_declared hT (E := E2) (n := "c") (dw := 1) rfl
  obtain ⟨vx, hx, wx⟩ := Elab.lookup_declared hT (E := E2) (n := "x") (dw := 4) rfl
  obtain ⟨vy, hy, wy⟩ := Elab.lookup_declared hT (E := E2) (n := "y") (dw := 4) rfl
  rw [show execBody E2 B2 = execBody E2 (.ifStmt (.ident "c") B2t (some B2e)) from rfl]
  simp only [B2t, B2e, execBody, execBodyList, execBodyOpt, stW_x2, stW_y2]
  mvcgen
  all_goals simp_all [vw2_x, vw2_y, Elab.Typed.writeWin, CombGuard.lookup_set_self, CombGuard.lookup_set_ne,
    g2, wr, valE, sig, readSignal]

/-! ## Scaling and coverage: a five-statement chain (B3) and a `case` (B4)

B3 `begin p = a & b; q = p | a; r = q ^ b; s = ~r; if (c) y = s; else y = p; end`: routes L and mvcgen.
B4 `case (sel) 2'd0: y = a; 2'd1: y = b; default: y = d; endcase`: L has no `case` primitive, so routes A and mvcgen. -/

def e3p : Expr2 := .binary .and (.ident "a") (.ident "b")
def e3q : Expr2 := .binary .or (.ident "p") (.ident "a")
def e3r : Expr2 := .binary .xor (.ident "q") (.ident "b")
def e3s : Expr2 := .unary .bnot (.ident "r")
def B3 : Stmt2 := .block #[.blockingAssign (.ident "p") e3p, .blockingAssign (.ident "q") e3q,
  .blockingAssign (.ident "r") e3r, .blockingAssign (.ident "s") e3s,
  .ifStmt (.ident "c") (.blockingAssign (.ident "y") (.ident "s")) (some (.blockingAssign (.ident "y") (.ident "p")))]

def E3 : Elab where
  decls := #[{ name := "a", width := 4, isInput := true }, { name := "b", width := 4, isInput := true },
             { name := "c", width := 1, isInput := true }, { name := "p", width := 4 }, { name := "q", width := 4 },
             { name := "r", width := 4 }, { name := "s", width := 4 }, { name := "y", width := 4 }]
  procs := #[.comb B3]

abbrev I3 : SvState → Prop := BoundAll ["a", "b", "c", "p", "q", "r", "s", "y"]

def g3 (st : SvState) : SvState :=
  let s4 := wr "s" e3s (wr "r" e3r (wr "q" e3q (wr "p" e3p st)))
  if (valE s4 (.ident "c")).condTrue then wr "y" (.ident "s") s4 else wr "y" (.ident "p") s4

theorem h4_3 : AllFour E3 := by unfold AllFour; decide

count_hb in
theorem B3_L : DenotesE E3 I3 B3 g3 := by
  refine (DenotesE.block (DenotesLE.cons (DenotesE.assignE (W := 4) h4_3 rfl rfl ?_) ?_
    (DenotesLE.cons (DenotesE.assignE (W := 4) h4_3 rfl rfl ?_) ?_
    (DenotesLE.cons (DenotesE.assignE (W := 4) h4_3 rfl rfl ?_) ?_
    (DenotesLE.cons (DenotesE.assignE (W := 4) h4_3 rfl rfl ?_) ?_
    (DenotesLE.cons (DenotesE.ite (b := some _) rfl ?_ (DenotesE.assignE (W := 4) h4_3 rfl rfl ?_)
      (DenotesE.assignE (W := 4) h4_3 rfl rfl ?_)) ?_ (DenotesLE.nil _ _))))))).congr fun st _ => rfl
  all_goals first
    | (intro st h; exact bnd h (by decide))
    | (intro st h; exact h.set _ _)
    | (intro st h; split <;> exact h.set _ _)

theorem stW3 (n : String) (hn : n ∈ ["p", "q", "r", "s", "y"]) :
    Lhs2.staticWin E3.toDesign2 (.ident n) = some (n, 0, 4) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem vw3_p {σ : Store} (hT : E3.Typed σ) (v : LVec) :
    E3.view (E3.writeWin σ "p" 0 (v.resizeU 4)) = SvState.set (E3.view σ) "p" (v.resizeU 4) := vw h4_3 hT rfl v
theorem vw3_q {σ : Store} (hT : E3.Typed σ) (v : LVec) :
    E3.view (E3.writeWin σ "q" 0 (v.resizeU 4)) = SvState.set (E3.view σ) "q" (v.resizeU 4) := vw h4_3 hT rfl v
theorem vw3_r {σ : Store} (hT : E3.Typed σ) (v : LVec) :
    E3.view (E3.writeWin σ "r" 0 (v.resizeU 4)) = SvState.set (E3.view σ) "r" (v.resizeU 4) := vw h4_3 hT rfl v
theorem vw3_s {σ : Store} (hT : E3.Typed σ) (v : LVec) :
    E3.view (E3.writeWin σ "s" 0 (v.resizeU 4)) = SvState.set (E3.view σ) "s" (v.resizeU 4) := vw h4_3 hT rfl v
theorem vw3_y {σ : Store} (hT : E3.Typed σ) (v : LVec) :
    E3.view (E3.writeWin σ "y" 0 (v.resizeU 4)) = SvState.set (E3.view σ) "y" (v.resizeU 4) := vw h4_3 hT rfl v

count_hb in
theorem B3_mv (σ0 : Store) (hT : E3.Typed σ0) (hI : I3 (E3.view σ0)) :
    ⦃fun s => ⌜s = σ0⌝⦄ execBody E3 B3
    ⦃⇓ _ => fun s => ⌜E3.Typed s ∧ E3.view s = g3 (E3.view σ0)⌝⦄ := by
  obtain ⟨va, ha, wa⟩ := Elab.lookup_declared hT (E := E3) (n := "a") (dw := 4) rfl
  obtain ⟨vb, hb, wb⟩ := Elab.lookup_declared hT (E := E3) (n := "b") (dw := 4) rfl
  obtain ⟨vc, hc, wc⟩ := Elab.lookup_declared hT (E := E3) (n := "c") (dw := 1) rfl
  obtain ⟨vp, hp, wp⟩ := Elab.lookup_declared hT (E := E3) (n := "p") (dw := 4) rfl
  obtain ⟨vq, hq, wq⟩ := Elab.lookup_declared hT (E := E3) (n := "q") (dw := 4) rfl
  obtain ⟨vr, hr, wr'⟩ := Elab.lookup_declared hT (E := E3) (n := "r") (dw := 4) rfl
  obtain ⟨vs, hs, ws⟩ := Elab.lookup_declared hT (E := E3) (n := "s") (dw := 4) rfl
  obtain ⟨vy, hy, wy⟩ := Elab.lookup_declared hT (E := E3) (n := "y") (dw := 4) rfl
  simp only [B3, execBody, execBodyList, execBodyOpt, List.toList_toArray,
    stW3 "p" (by decide), stW3 "q" (by decide), stW3 "r" (by decide), stW3 "s" (by decide), stW3 "y" (by decide)]
  mvcgen
  -- the store is threaded as nested `writeWin` terms: each `vw3_*` rewrite needs `Typed` of the store under it,
  -- discharged through `Elab.Typed.writeWin` once per enclosing write (simp's default depth is 2)
  all_goals simp_all (maxDischargeDepth := 8) [vw3_p, vw3_q, vw3_r, vw3_s, vw3_y, Elab.Typed.writeWin, CombGuard.lookup_set_self, CombGuard.lookup_set_ne,
    g3, wr, e3p, e3q, e3r, e3s, valE, sig, readSignal]

def B4 : Stmt2 := .caseStmt (.ident "sel")
  #[.mk #[.lit (.ofNat 2 0)] (.blockingAssign (.ident "y") (.ident "a")),
    .mk #[.lit (.ofNat 2 1)] (.blockingAssign (.ident "y") (.ident "b"))]
  (some (.blockingAssign (.ident "y") (.ident "d"))) false .none

def E4 : Elab where
  decls := #[{ name := "sel", width := 2, isInput := true }, { name := "a", width := 4, isInput := true },
             { name := "b", width := 4, isInput := true }, { name := "d", width := 4, isInput := true },
             { name := "y", width := 4 }]
  procs := #[.comb B4]

abbrev I4 : SvState → Prop := BoundAll ["sel", "a", "b", "d", "y"]

def g4 (st : SvState) : SvState :=
  if caseHit false (valE st (.ident "sel")) (.ofNat 2 0) then wr "y" (.ident "a") st
  else if caseHit false (valE st (.ident "sel")) (.ofNat 2 1) then wr "y" (.ident "b") st
  else wr "y" (.ident "d") st

theorem h4_4 : AllFour E4 := by unfold AllFour; decide
theorem stW4 : Lhs2.staticWin E4.toDesign2 (.ident "y") = some ("y", 0, 4) := rfl
theorem vw4 {σ : Store} (hT : E4.Typed σ) (v : LVec) :
    E4.view (E4.writeWin σ "y" 0 (v.resizeU 4)) = SvState.set (E4.view σ) "y" (v.resizeU 4) := vw h4_4 hT rfl v

count_hb in
theorem B4_A : DenotesE E4 I4 B4 g4 := fun σ hT hI => by
  have hsv := evalPure2_valE (st := E4.view σ) (e := .ident "sel") rfl (bnd hI (by decide))
  have e0 := execArm_run (E := E4) (s := σ) (sv := valE (E4.view σ) (.ident "sel")) (inside := false)
    (pats := #[.lit (.ofNat 2 0)]) (body := .blockingAssign (.ident "y") (.ident "a")) (pvs := [.ofNat 2 0]) rfl
  have e1 := execArm_run (E := E4) (s := σ) (sv := valE (E4.view σ) (.ident "sel")) (inside := false)
    (pats := #[.lit (.ofNat 2 1)]) (body := .blockingAssign (.ident "y") (.ident "b")) (pvs := [.ofNat 2 1]) rfl
  rw [show B4 = .caseStmt (.ident "sel")
    #[.mk #[.lit (.ofNat 2 0)] (.blockingAssign (.ident "y") (.ident "a")),
      .mk #[.lit (.ofNat 2 1)] (.blockingAssign (.ident "y") (.ident "b"))]
    (some (.blockingAssign (.ident "y") (.ident "d"))) false .none from rfl, execBody_case_run hsv]
  by_cases h0 : caseHit false (valE (E4.view σ) (.ident "sel")) (.ofNat 2 0) = true
  · obtain ⟨r, hT2, hv2⟩ := step_wr (E := E4) (n := "y") (e := .ident "a") (I := I4) h4_4 hT rfl rfl
      (bnd hI (by decide))
    refine ⟨_, ?_, hT2, by rw [hv2, g4, if_pos h0]⟩
    simp only [List.toList_toArray, execArms, SemMWith.run_bind, e0, List.any_cons, List.any_nil,
      Bool.or_false, h0, ↓reduceIte, r, SemMWith.run_pure]
  · by_cases h1 : caseHit false (valE (E4.view σ) (.ident "sel")) (.ofNat 2 1) = true
    · obtain ⟨r, hT2, hv2⟩ := step_wr (E := E4) (n := "y") (e := .ident "b") (I := I4) h4_4 hT rfl rfl
        (bnd hI (by decide))
      refine ⟨_, ?_, hT2, by rw [hv2, g4, if_neg h0, if_pos h1]⟩
      simp only [List.toList_toArray, execArms, SemMWith.run_bind, e0, e1, List.any_cons, List.any_nil,
        Bool.or_false, h0, h1, Bool.false_eq_true, ↓reduceIte, r, SemMWith.run_pure]
    · obtain ⟨r, hT2, hv2⟩ := step_wr (E := E4) (n := "y") (e := .ident "d") (I := I4) h4_4 hT rfl rfl
        (bnd hI (by decide))
      refine ⟨_, ?_, hT2, by rw [hv2, g4, if_neg h0, if_neg h1]⟩
      simp only [List.toList_toArray, execArms, SemMWith.run_bind, e0, e1, List.any_cons, List.any_nil,
        Bool.or_false, h0, h1, Bool.false_eq_true, ↓reduceIte, r, SemMWith.run_pure, execBodyOpt]

count_hb in
theorem B4_mv (σ0 : Store) (hT : E4.Typed σ0) (hI : I4 (E4.view σ0)) :
    ⦃fun s => ⌜s = σ0⌝⦄ execBody E4 B4
    ⦃⇓ _ => fun s => ⌜E4.Typed s ∧ E4.view s = g4 (E4.view σ0)⌝⦄ := by
  obtain ⟨vsel, hsel, wsel⟩ := Elab.lookup_declared hT (E := E4) (n := "sel") (dw := 2) rfl
  obtain ⟨va, ha, wa⟩ := Elab.lookup_declared hT (E := E4) (n := "a") (dw := 4) rfl
  obtain ⟨vb, hb, wb⟩ := Elab.lookup_declared hT (E := E4) (n := "b") (dw := 4) rfl
  obtain ⟨vd, hd, wd⟩ := Elab.lookup_declared hT (E := E4) (n := "d") (dw := 4) rfl
  obtain ⟨vy, hy, wy⟩ := Elab.lookup_declared hT (E := E4) (n := "y") (dw := 4) rfl
  simp only [B4, execBody, execArms, execArm, execBodyOpt, List.toList_toArray, stW4]
  mvcgen
  all_goals simp_all [vw4, Elab.Typed.writeWin, CombGuard.lookup_set_self, CombGuard.lookup_set_ne,
    g4, wr, valE, sig, readSignal]

/-! ## The bridge: a total-correctness triple on E-core-0's monad gives the run -/

count_hb in
theorem run_of_triple {α : Type} {x : EM α} {s0 : Store} {Q : α → Store → Prop}
    (h : ⦃fun s => ⌜s = s0⌝⦄ x ⦃⇓ a => fun s => ⌜Q a s⌝⦄) :
    ∃ a s', x s0 = .ok (.ok a, s') ∧ Q a s' := by
  have hw := h s0 rfl
  simp only [WP.wp, PredTrans.apply_pushExcept, PredTrans.apply_pushArg, ExceptT.run, StateT.run] at hw
  rcases hx : x s0 with l | ⟨r, s'⟩
  · rw [hx] at hw
    exact (show False from hw).elim
  · rcases r with e | a
    · exact nomatch e
    · rw [hx] at hw
      exact ⟨a, s', rfl, hw⟩

-- Route mvcgen, to the routes' common statement (the bridge applied: B3 and B4 below are the same two lines).
count_hb in
theorem B1_mvD : DenotesE E1 I1 B1 g1 := fun σ hT hI => by
  obtain ⟨_, σ', h1, h2, h3⟩ := run_of_triple (B1_mv σ hT hI)
  exact ⟨σ', h1, h2, h3⟩

count_hb in
theorem B2_mvD : DenotesE E2 I2 B2 g2 := fun σ hT hI => by
  obtain ⟨_, σ', h1, h2, h3⟩ := run_of_triple (B2_mv σ hT hI)
  exact ⟨σ', h1, h2, h3⟩

count_hb in
theorem B3_mvD : DenotesE E3 I3 B3 g3 := fun σ hT hI => by
  obtain ⟨_, σ', h1, h2, h3⟩ := run_of_triple (B3_mv σ hT hI)
  exact ⟨σ', h1, h2, h3⟩

count_hb in
theorem B4_mvD : DenotesE E4 I4 B4 g4 := fun σ hT hI => by
  obtain ⟨_, σ', h1, h2, h3⟩ := run_of_triple (B4_mv σ hT hI)
  exact ⟨σ', h1, h2, h3⟩

#print axioms B1_L
#print axioms B2_L
#print axioms B1_A
#print axioms B2_A
#print axioms B1_mvD
#print axioms B2_mvD
#print axioms B3_L
#print axioms B3_mvD
#print axioms B4_A
#print axioms B4_mvD
#print axioms run_of_triple
#print axioms ofRes_spec

end X12

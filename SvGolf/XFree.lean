import SvGolf.TaskSeq
import LeanModels.Sv.CombKnownBits
import LeanModels.Sv.Observe

/-!
# `xfree`: rule 3 makes every value of a concrete run known (untrusted, kernel-checked)

The coverage argument of txtask-v2's rule 3 (`XSafe`, `SvGolf/TaskSeq.lean`). A state is
**known** (`KnownState d st`) when every signal it binds holds a value of its declared width whose
every bit is `0` or `1`. Then, for a design `d` that passes rule 3:

* `xfree_expr`: every expression rule 3 admits (`xsWidth d e = some w`) evaluates, on a known
  state, to a known value of width `w` (by induction over `evalExpr2`/`evalExprs2`);
* `xfree_stmt`: every statement (`execStmt2`, `execCase2`, `execStmts2`) keeps the state known
  and issues only known nonblocking updates;
* `xfree_combSettle`, `xfree_resetPass`, `xfree_edgePass`, `xfree_commit`, `xfree_apply`: the
  settle, the two passes, the NBA commit and the input application keep the state known (the last
  on a known stimulus entry, `KnownEntry`);
* **`xfree_cycle`**: one clock cycle (`cycleStep2`) from a known state on a known entry ends in a
  known state; **`xfree_run`** and **`xfree_runsAt`**: every snapshot of a run from a power-up
  state (`PowerUp`, `KnownState.of_powerUp`) on a known stimulus is known.

Every condition, case subject, case pattern, dynamic index and right-hand side the interpreter
evaluates during such a run is evaluated on a state the induction keeps known, so by `xfree_expr`
its value is known: **no decision of a concrete run of a rule-3 design reads an `x`**, and no
simulator resolution of an unknown value (the else branch of `if (x)`, a case falling to its
default on an `x` subject) is ever taken. Rule 2 (every power-up, known stimuli) and rule 3
together are what make every value of every run of the statement a 0/1 value, in ls-sv's
semantics. That the scored netlist computes the same values is not shown here: it is ls-sv's
faithfulness to IEEE 1800 on defined values and the pinned flow's to ls-sv, which only the
sampled post-synthesis check looks at (`design/soundness/TXTASK-V2-REVIEW.md`, sections 3 and 10).

The cases where the evaluator yields `x` from known operands, and the rule-3 condition each
needs, are listed at `xsWidth` (`SvGolf/TaskSeq.lean`); here each shows up as the hypothesis
that closes one case. The value lemmas go through ls-sv's known-vector calculus (`LVec.ofBoolFn`,
`LeanModels/Sv/CombKnownBits.lean`).
-/

namespace SvGolf

open LeanModels.Sv

set_option autoImplicit false

/-! ## Known values and states -/

/-- `v` is a known value of width `w`. -/
def KV (w : Nat) (v : LVec) : Prop := v.allKnown = true ∧ v.width = w

theorem KV.of_ofBoolFn (w : Nat) (f : Nat → Bool) : KV w (LVec.ofBoolFn w f) :=
  ⟨LVec.allKnown_ofBoolFn w f, LVec.width_ofBoolFn w f⟩

theorem KV.ex {w : Nat} {v : LVec} (h : KV w v) : ∃ f, v = LVec.ofBoolFn w f := by
  refine ⟨v.boolAt, ?_⟩
  have e := LVec.eq_ofBoolFn_of_allKnown h.1
  rw [h.2] at e
  exact e

theorem KV.of_ofNat (w n : Nat) : KV w (LVec.ofNat w n) :=
  ⟨LVec.allKnown_ofNat w n, LVec.width_ofNat w n⟩

theorem KV.of_ofBitVec {w : Nat} (x : BitVec w) : KV w (LVec.ofBitVec x) :=
  ⟨LVec.allKnown_ofBitVec x, LVec.width_ofBitVec x⟩

theorem KV.ofLogic_ofBool (b : Bool) : KV 1 (LVec.ofLogic (Logic.ofBool b)) := by
  rw [LVec.ofLogic_ofBool]; exact KV.of_ofBitVec _

theorem KV.ofLogic {l : Logic} (h : l.isKnown = true) : KV 1 (LVec.ofLogic l) := by
  cases l
  · exact KV.ofLogic_ofBool false
  · exact KV.ofLogic_ofBool true
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem KV.ite_l1_l0 (c : Prop) [Decidable c] : KV 1 (LVec.ofLogic (if c then .l1 else .l0)) := by
  split
  · exact KV.ofLogic_ofBool true
  · exact KV.ofLogic_ofBool false

theorem Logic.isKnown_not' {a : Logic} : a.isKnown = true → a.not.isKnown = true := by
  cases a <;> decide

theorem Logic.isKnown_and' {a b : Logic} :
    a.isKnown = true → b.isKnown = true → (Logic.and a b).isKnown = true := by
  cases a <;> cases b <;> decide

theorem Logic.isKnown_or' {a b : Logic} :
    a.isKnown = true → b.isKnown = true → (Logic.or a b).isKnown = true := by
  cases a <;> cases b <;> decide

/-- The value of a known vector: its Boolean bits' value. -/
theorem toNat_ofBoolFn (w : Nat) (f : Nat → Bool) : (LVec.ofBoolFn w f).toNat = XF.val f w := by
  have h := LVec.toNat?_ofBoolFn w f
  simp only [LVec.toNat?, LVec.allKnown_ofBoolFn, if_true, Option.some.injEq] at h
  exact h

/-- **A known state** of `d`: every signal it binds holds a known value of its declared width. -/
def KnownState (d : Design2) (st : SvState) : Prop :=
  ∀ n v, SvState.lookup st n = some v → v.allKnown = true ∧ sigWidth d n = some v.width

theorem KnownState.set {d : Design2} {st : SvState} {n : String} {v : LVec}
    (hst : KnownState d st) (hv : v.allKnown = true) (hw : sigWidth d n = some v.width) :
    KnownState d (SvState.set st n v) := by
  intro m u h
  rw [SvState.lookup_set] at h
  by_cases hnm : n = m
  · subst hnm
    rw [if_pos rfl, Option.some.injEq] at h
    subst h
    exact ⟨hv, hw⟩
  · rw [if_neg hnm] at h
    exact hst m u h

/-- Every update of a nonblocking queue is a known value. -/
def NbaKnown (nba : NbaQueue2) : Prop := ∀ u ∈ nba, u.2.2.allKnown = true

/-! ## Value lemmas: known operands give known results -/

theorem allKnown_mk_ofFn {n : Nat} (F : Fin n → Logic) (h : ∀ i, (F i).isKnown = true) :
    (LVec.mk (Array.ofFn F)).allKnown = true := by
  unfold LVec.allKnown
  rw [Array.all_eq_true]
  intro i hi
  simp only [Array.getElem_ofFn]
  exact h _

theorem KV.toTwoState (v : LVec) : KV v.width v.toTwoState := by
  refine ⟨?_, by simp [LVec.toTwoState, LVec.width]⟩
  unfold LVec.toTwoState LVec.allKnown
  rw [Array.all_eq_true]
  intro i hi
  simp only [Array.getElem_map]
  split <;> rfl

theorem KV.insertAt {w : Nat} {v p : LVec} (hv : KV w v) (hp : p.allKnown = true) (lo : Nat) :
    KV w (v.insertAt lo p) := by
  refine ⟨?_, by rw [LVec.width_insertAt]; exact hv.2⟩
  unfold LVec.insertAt
  refine allKnown_mk_ofFn _ fun i => ?_
  have hpk := Array.all_eq_true.mp hp
  have hvk := Array.all_eq_true.mp hv.1
  split
  · rename_i h
    have hlt : i.val - lo < p.bits.size := by
      have : i.val < lo + p.width := h.2
      simp only [LVec.width] at this; omega
    rw [Array.getElem?_eq_getElem hlt, Option.getD_some]
    exact hpk _ hlt
  · have hlt : i.val < v.bits.size := i.isLt
    rw [Array.getElem?_eq_getElem hlt, Option.getD_some]
    exact hvk _ hlt

theorem KV.resizeU {w : Nat} {v : LVec} (hv : KV w v) (w' : Nat) : KV w' (v.resizeU w') := by
  obtain ⟨f, rfl⟩ := hv.ex
  rw [LVec.resizeU_ofBoolFn]; exact KV.of_ofBoolFn _ _

theorem KV.extract {w : Nat} {v : LVec} (hv : KV w v) {lo k : Nat} (h : lo + k ≤ w) :
    KV k (v.extract lo k) := by
  obtain ⟨f, rfl⟩ := hv.ex
  rw [LVec.extract_ofBoolFn f h]; exact KV.of_ofBoolFn _ _

theorem lnot_isKnown {w : Nat} {a : LVec} (h : KV w a) : a.lnot.isKnown = true := by
  obtain ⟨f, rfl⟩ := h.ex
  unfold LVec.lnot
  rw [XF.condTrue_ofBoolFn, XF.isKnownZero_ofBoolFn, XF.all_not]
  generalize XF.any w f = b
  cases b <;> rfl

theorem condTrue_or_isKnownZero {w : Nat} {a : LVec} (h : KV w a) :
    a.isKnownZero = !a.condTrue := by
  obtain ⟨f, rfl⟩ := h.ex
  rw [XF.condTrue_ofBoolFn, XF.isKnownZero_ofBoolFn, XF.all_not]

theorem truthy_list : ∀ (l : List Logic), (∀ x ∈ l, x.isKnown = true) →
    LVec.hasKnownOne l = true ∨ LVec.allKnownZero l = true
  | [], _ => Or.inr rfl
  | x :: l, h => by
      have hl : ∀ y ∈ l, y.isKnown = true := fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hx := h x List.mem_cons_self
      cases x with
      | l1 => exact Or.inl rfl
      | l0 =>
          rcases truthy_list l hl with h1 | h1
          · exact Or.inl (by simpa [LVec.hasKnownOne] using h1)
          · exact Or.inr (by simpa [LVec.allKnownZero] using h1)
      | lx => exact absurd hx (by decide)
      | lz => exact absurd hx (by decide)

theorem truthy_isKnown {w : Nat} {a : LVec} (h : KV w a) : (LVec.truthy a).isKnown = true := by
  have hl : ∀ x ∈ a.bits.toList, x.isKnown = true := by
    have := h.1
    unfold LVec.allKnown at this
    rw [← Array.all_toList, List.all_eq_true] at this
    exact this
  unfold LVec.truthy
  rcases truthy_list _ hl with h1 | h1
  · rw [if_pos h1]; rfl
  · by_cases hk : LVec.hasKnownOne a.bits.toList = true
    · rw [if_pos hk]; rfl
    · rw [if_neg hk, if_pos h1]; rfl

theorem signedRelOp_isKnown (cmp : Int → Int → Bool) {wa wb : Nat} {a b : LVec} (ha : KV wa a)
    (hb : KV wb b) : (LVec.signedRelOp cmp a b).isKnown = true := by
  obtain ⟨f, rfl⟩ := ha.ex
  obtain ⟨g, rfl⟩ := hb.ex
  unfold LVec.signedRelOp
  rw [LVec.toNat?_ofBoolFn, LVec.toNat?_ofBoolFn]
  dsimp only
  split <;> rfl

theorem toInt?_isSome {w : Nat} {a : LVec} (h : KV w a) : ∃ x, a.toInt? = some x := by
  obtain ⟨f, rfl⟩ := h.ex
  unfold LVec.toInt?
  rw [LVec.toNat?_ofBoolFn]
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem eqWildcard_isKnown {w : Nat} {a b : LVec} (ha : KV w a) (hb : KV w b) :
    (a.eqWildcard b).isKnown = true := by
  have hak := Array.all_eq_true.mp ha.1
  unfold LVec.eqWildcard
  rw [if_neg (by rw [ha.2, hb.2]; exact fun h => h rfl)]
  dsimp only
  split
  · rfl
  · split
    · rename_i _ h2
      exfalso
      rw [Array.any_eq_true] at h2
      obtain ⟨i, hi, h⟩ := h2
      have hia : i < a.bits.size := by rw [Array.size_zip] at hi; omega
      rw [Array.getElem_zip] at h
      have hk : a.bits[i].isKnown = true := hak i hia
      simp [hk] at h
    · rfl

theorem redOp_isKnown (op : RedOp) {w : Nat} {v : LVec} (h : KV w v) :
    (evalRedOp op v).isKnown = true := by
  obtain ⟨f, rfl⟩ := h.ex
  cases op <;> simp [evalRedOp, XF.redOr_ofBoolFn, XF.redAnd_ofBoolFn, XF.redXor_ofBoolFn,
    Logic.isKnown_ofBool]

theorem KV.concatMany : ∀ (vs : List LVec) (acc : LVec), acc.allKnown = true →
    (∀ v ∈ vs, v.allKnown = true) →
    (vs.foldl (fun acc p => (⟨p.bits ++ acc.bits⟩ : LVec)) acc).allKnown = true ∧
    (vs.foldl (fun acc p => (⟨p.bits ++ acc.bits⟩ : LVec)) acc).width =
      acc.width + (vs.map LVec.width).sum
  | [], acc, ha, _ => ⟨ha, by simp⟩
  | v :: vs, acc, ha, hv => by
      have h1 : (⟨v.bits ++ acc.bits⟩ : LVec).allKnown = true := by
        simp only [LVec.allKnown, Array.all_append, Bool.and_eq_true]
        exact ⟨hv v List.mem_cons_self, ha⟩
      obtain ⟨k, hw⟩ := KV.concatMany vs _ h1 (fun u hu => hv u (List.mem_cons_of_mem _ hu))
      refine ⟨k, ?_⟩
      rw [List.foldl_cons, hw]
      simp only [LVec.width, Array.size_append, List.map_cons, List.sum_cons]
      omega

theorem KV.concat {vs : List LVec} (h : ∀ v ∈ vs, v.allKnown = true) :
    KV (vs.map LVec.width).sum (LVec.concatMany vs.toArray) := by
  unfold LVec.concatMany
  rw [List.foldl_toArray]
  have h0 : (⟨#[]⟩ : LVec).allKnown = true := by
    unfold LVec.allKnown; rw [Array.all_eq_true]; intro i hi; simp at hi
  obtain ⟨k, hw⟩ := KV.concatMany vs ⟨#[]⟩ h0 h
  exact ⟨k, by rw [hw]; simp [LVec.width]⟩

/-! ## The binary operators -/

/-- A constant evaluates to its value. -/
theorem constVal_eval : ∀ (fuel : Nat) (st : SvState) (e : Expr2) (c v : LVec),
    constVal? e = some c → evalExpr2 fuel st e = .ok v → v = c
  | 0, _, _, _, _, _, h => by simp [evalExpr2] at h
  | fuel + 1, st, e, c, v, hc, h => by
      cases e with
      | lit lv =>
          simp only [constVal?, Option.some.injEq] at hc
          simp only [evalExpr2, Res.ok.injEq] at h
          rw [← h, hc]
      | resize w a =>
          simp only [constVal?, Option.map_eq_some_iff] at hc
          obtain ⟨c', hc', rfl⟩ := hc
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨va, ha, rfl⟩ := h
          rw [constVal_eval fuel st a c' va hc' ha]
      | resizeSigned w a =>
          simp only [constVal?, Option.map_eq_some_iff] at hc
          obtain ⟨c', hc', rfl⟩ := hc
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨va, ha, rfl⟩ := h
          rw [constVal_eval fuel st a c' va hc' ha]
      | _ => simp [constVal?] at hc

/-- The value of a nonzero constant. -/
theorem constNZ_eval {fuel : Nat} {st : SvState} {e : Expr2} {v : LVec} (hc : constNZ e = true)
    (h : evalExpr2 fuel st e = .ok v) : v.allKnown = true ∧ v.toNat ≠ 0 := by
  unfold constNZ at hc
  split at hc
  · rename_i c hcv
    rw [constVal_eval fuel st e c v hcv h]
    simpa using hc
  · cases hc

/-- **The binary operators**: rule 3's condition at an operator (`binW`), known operands of the
widths it names, and the constants it names evaluated, give a known result of the width it names. -/
theorem binW_known {op : BinOp} {l r : Expr2} {wl wr : Option Nat} {w : Nat} {a b : LVec}
    (hw : binW op l r wl wr = some w) (ha : ∀ x, wl = some x → KV x a)
    (hb : ∀ x, wr = some x → KV x b)
    (hca : constNZ l = true → a.allKnown = true ∧ a.toNat ≠ 0)
    (hcb : constNZ r = true → b.allKnown = true ∧ b.toNat ≠ 0) :
    KV w (evalBinOp op a b) := by
  rcases wl with _ | x
  · cases op <;> simp [binW] at hw
  rcases wr with _ | y
  · cases op <;> simp [binW] at hw
  have ka := ha x rfl
  have kb := hb y rfl
  obtain ⟨f, rfl⟩ := ka.ex
  obtain ⟨g, rfl⟩ := kb.ex
  cases op with
  | add =>
      have hw' : some (max x y) = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; rw [LVec.add_ofBoolFn]; exact KV.of_ofBoolFn _ _
  | sub =>
      have hw' : some (max x y) = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; rw [LVec.sub_ofBoolFn]; exact KV.of_ofBoolFn _ _
  | mul =>
      have hw' : some (max x y) = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; rw [LVec.mul_ofBoolFn]; exact KV.of_ofBoolFn _ _
  | div =>
      have hw' : (if constNZ r = true then some (max x y) else none) = some w := hw
      split at hw'
      · rename_i hnz
        obtain rfl := Option.some.inj hw'
        have h0 := (hcb hnz).2
        rw [toNat_ofBoolFn] at h0
        simp only [evalBinOp, LVec.div, LVec.toNat?_ofBoolFn, LVec.arithWidth, LVec.width_ofBoolFn]
        rw [if_neg (by simpa using h0)]
        exact KV.of_ofNat _ _
      · cases hw'
  | sdiv =>
      have hw' : (if constNZ r = true then some (max x y) else none) = some w := hw
      split at hw'
      · rename_i hnz
        obtain rfl := Option.some.inj hw'
        have h0 := (hcb hnz).2
        rw [toNat_ofBoolFn] at h0
        simp only [evalBinOp, LVec.sdiv, LVec.toNat?_ofBoolFn, LVec.arithWidth, LVec.width_ofBoolFn]
        rw [if_neg (by simpa using h0)]
        exact ⟨LVec.allKnown_ofBitVec _, by simp [LVec.width_ofBitVec, LVec.width_ofBoolFn]⟩
      · cases hw'
  | rem =>
      have hw' : (if constNZ r = true then some (max x y) else none) = some w := hw
      split at hw'
      · rename_i hnz
        obtain rfl := Option.some.inj hw'
        have h0 := (hcb hnz).2
        rw [toNat_ofBoolFn] at h0
        simp only [evalBinOp, LVec.rem, LVec.toNat?_ofBoolFn, LVec.arithWidth, LVec.width_ofBoolFn]
        rw [if_neg (by simpa using h0)]
        exact KV.of_ofNat _ _
      · cases hw'
  | srem =>
      have hw' : (if constNZ r = true then some (max x y) else none) = some w := hw
      split at hw'
      · rename_i hnz
        obtain rfl := Option.some.inj hw'
        have h0 := (hcb hnz).2
        rw [toNat_ofBoolFn] at h0
        simp only [evalBinOp, LVec.srem, LVec.toNat?_ofBoolFn, LVec.arithWidth, LVec.width_ofBoolFn]
        rw [if_neg (by simpa using h0)]
        exact ⟨LVec.allKnown_ofBitVec _, by simp [LVec.width_ofBitVec, LVec.width_ofBoolFn]⟩
      · cases hw'
  | pow sb se =>
      have hw' : (if (!se || constNZ l) = true then some x else none) = some w := hw
      split at hw'
      · rename_i hcond
        obtain rfl := Option.some.inj hw'
        have key : ∀ k, KV x (LVec.ofNat (LVec.ofBoolFn x f).width k) := fun k =>
          ⟨LVec.allKnown_ofNat _ _, by rw [LVec.width_ofNat, LVec.width_ofBoolFn]⟩
        have hc2 : se = false ∨ constNZ l = true := by simpa using hcond
        simp only [evalBinOp, LVec.pow, LVec.toNat?_ofBoolFn]
        split
        · rename_i hneg
          split
          · rename_i hz
            exfalso
            rcases hc2 with hs | hs
            · simp [hs] at hneg
            · have h0 := (hca hs).2
              rw [toNat_ofBoolFn] at h0
              exact h0 (by simpa using hz)
          · split
            · exact key _
            · split
              · exact key _
              · exact key _
        · exact key _
      · cases hw'
  | shl s =>
      have hw' : some x = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; rw [LVec.shl_ofBoolFn]; exact KV.of_ofBoolFn _ _
  | shr s =>
      have hw' : some x = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; rw [LVec.shr_ofBoolFn]; exact KV.of_ofBoolFn _ _
  | ashl s =>
      have hw' : some x = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.ashl]; rw [LVec.shl_ofBoolFn]; exact KV.of_ofBoolFn _ _
  | ashr s =>
      have hw' : some x = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.ashr, LVec.shiftAmount?, LVec.toNat?_ofBoolFn]
      refine ⟨allKnown_mk_ofFn _ fun i => ?_, by
        simp only [LVec.width, Array.size_ofFn]; exact LVec.width_ofBoolFn x f⟩
      rw [LVec.getElem?_ofBoolFn]
      by_cases hi : i.val + XF.val g y < x
      · rw [if_pos hi]; exact Logic.isKnown_ofBool _
      · rw [if_neg hi]
        cases s
        · rfl
        · show ((LVec.ofBoolFn x f).bits.back?.getD .l0).isKnown = true
          rw [LVec.back?_ofBoolFn]
          by_cases h0 : 0 < x
          · rw [if_pos h0]; exact Logic.isKnown_ofBool _
          · rw [if_neg h0]; rfl
  | and =>
      have hw' : (if x = y then some x else none) = some w := hw
      split at hw'
      · rename_i hxy
        obtain rfl := Option.some.inj hw'
        subst hxy
        simp only [evalBinOp, LVec.and]
        rw [LVec.zipWith_ofBoolFn x Logic.and (· && ·) Logic.and_ofBool]
        exact KV.of_ofBoolFn _ _
      · cases hw'
  | or =>
      have hw' : (if x = y then some x else none) = some w := hw
      split at hw'
      · rename_i hxy
        obtain rfl := Option.some.inj hw'
        subst hxy
        simp only [evalBinOp, LVec.or]
        rw [LVec.zipWith_ofBoolFn x Logic.or (· || ·) Logic.or_ofBool]
        exact KV.of_ofBoolFn _ _
      · cases hw'
  | xor =>
      have hw' : (if x = y then some x else none) = some w := hw
      split at hw'
      · rename_i hxy
        obtain rfl := Option.some.inj hw'
        subst hxy
        simp only [evalBinOp, LVec.xor]
        rw [LVec.zipWith_ofBoolFn x Logic.xor (· ^^ ·) Logic.xor_ofBool]
        exact KV.of_ofBoolFn _ _
      · cases hw'
  | eq =>
      have hw' : (if x = y then some 1 else none) = some w := hw
      split at hw'
      · rename_i hxy
        obtain rfl := Option.some.inj hw'
        subst hxy
        simp only [evalBinOp]; rw [LVec.eqLogical_ofBoolFn]; exact KV.ofLogic_ofBool _
      · cases hw'
  | ne =>
      have hw' : (if x = y then some 1 else none) = some w := hw
      split at hw'
      · rename_i hxy
        obtain rfl := Option.some.inj hw'
        subst hxy
        simp only [evalBinOp, LVec.neLogical]; rw [LVec.eqLogical_ofBoolFn, Logic.not_ofBool]
        exact KV.ofLogic_ofBool _
      · cases hw'
  | caseEq =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.eqCase]; exact KV.ite_l1_l0 _
  | caseNe =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.neCase, LVec.eqCase]
      split
      · exact KV.ofLogic_ofBool false
      · exact KV.ofLogic_ofBool true
  | wildEq =>
      have hw' : (if x = y then some 1 else none) = some w := hw
      split at hw'
      · rename_i hxy
        obtain rfl := Option.some.inj hw'
        subst hxy
        simp only [evalBinOp]
        exact KV.ofLogic (eqWildcard_isKnown (KV.of_ofBoolFn x f) (KV.of_ofBoolFn x g))
      · cases hw'
  | wildNe =>
      have hw' : (if x = y then some 1 else none) = some w := hw
      split at hw'
      · rename_i hxy
        obtain rfl := Option.some.inj hw'
        subst hxy
        simp only [evalBinOp, LVec.neWildcard]
        exact KV.ofLogic (Logic.isKnown_not'
          (eqWildcard_isKnown (KV.of_ofBoolFn x f) (KV.of_ofBoolFn x g)))
      · cases hw'
  | casez =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; exact KV.ite_l1_l0 _
  | casex =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; exact KV.ite_l1_l0 _
  | land =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.land]
      exact KV.ofLogic (Logic.isKnown_and' (truthy_isKnown (KV.of_ofBoolFn x f))
        (truthy_isKnown (KV.of_ofBoolFn y g)))
  | lor =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.lor]
      exact KV.ofLogic (Logic.isKnown_or' (truthy_isKnown (KV.of_ofBoolFn x f))
        (truthy_isKnown (KV.of_ofBoolFn y g)))
  | lt =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; rw [LVec.lt_ofBoolFn]; exact KV.ofLogic_ofBool _
  | le =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; rw [LVec.le_ofBoolFn]; exact KV.ofLogic_ofBool _
  | gt =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; rw [LVec.gt_ofBoolFn]; exact KV.ofLogic_ofBool _
  | ge =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp]; rw [LVec.ge_ofBoolFn]; exact KV.ofLogic_ofBool _
  | slt =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.slt]
      exact KV.ofLogic (signedRelOp_isKnown _ (KV.of_ofBoolFn x f) (KV.of_ofBoolFn y g))
  | sle =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.sle]
      exact KV.ofLogic (signedRelOp_isKnown _ (KV.of_ofBoolFn x f) (KV.of_ofBoolFn y g))
  | sgt =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.sgt]
      exact KV.ofLogic (signedRelOp_isKnown _ (KV.of_ofBoolFn x f) (KV.of_ofBoolFn y g))
  | sge =>
      have hw' : some 1 = some w := hw
      obtain rfl := Option.some.inj hw'
      simp only [evalBinOp, LVec.sge]
      exact KV.ofLogic (signedRelOp_isKnown _ (KV.of_ofBoolFn x f) (KV.of_ofBoolFn y g))

/-! ## Expressions -/

/-- **`xfree_expr`**: on a known state, every expression rule 3 admits evaluates to a known value
of the width rule 3 names, and every list of them to known values of the summed width. -/
theorem xfree_expr {d : Design2} {st : SvState} (hst : KnownState d st) : ∀ fuel : Nat,
    (∀ (e : Expr2) (w : Nat) (v : LVec), xsWidth d e = some w → evalExpr2 fuel st e = .ok v →
      KV w v) ∧
    (∀ (es : List Expr2) (w : Nat) (vs : List LVec), xsWidthList d es = some w →
      evalExprs2 fuel st es = .ok vs → (∀ v ∈ vs, v.allKnown = true) ∧ (vs.map LVec.width).sum = w)
  | 0 => ⟨fun _ _ _ _ h => by simp [evalExpr2] at h, fun _ _ _ _ h => by simp [evalExprs2] at h⟩
  | fuel + 1 => by
    obtain ⟨ihE, ihL⟩ := xfree_expr hst fuel
    refine ⟨fun e w v hw h => ?_, fun es w vs hw h => ?_⟩
    · cases e with
      | lit lv =>
          simp only [evalExpr2, Res.ok.injEq] at h
          subst h
          have hw' : (if lv.allKnown = true then some lv.width else none) = some w := hw
          split at hw'
          · rename_i hk; exact ⟨hk, Option.some.inj hw'⟩
          · cases hw'
      | ident n =>
          simp only [evalExpr2, readSignal] at h
          split at h
          · rename_i u hu
            simp only [Res.ok.injEq] at h
            subst h
            obtain ⟨hk, hwd⟩ := hst n u hu
            have hw' : sigWidth d n = some w := hw
            rw [hw'] at hwd
            exact ⟨hk, (Option.some.inj hwd).symm⟩
          · cases h
      | unary op a =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨va, ha, rfl⟩ := h
          cases op with
          | lnot =>
              have hw' : (xsWidth d a).map (fun _ => 1) = some w := hw
              rw [Option.map_eq_some_iff] at hw'
              obtain ⟨wa, hwa, rfl⟩ := hw'
              exact KV.ofLogic (lnot_isKnown (ihE a wa va hwa ha))
          | bnot =>
              have hw' : xsWidth d a = some w := hw
              obtain ⟨f, rfl⟩ := (ihE a w va hw' ha).ex
              simp only [evalUnaryOp]; rw [LVec.not_ofBoolFn]; exact KV.of_ofBoolFn _ _
          | neg =>
              have hw' : xsWidth d a = some w := hw
              obtain ⟨f, rfl⟩ := (ihE a w va hw' ha).ex
              simp only [evalUnaryOp]; rw [LVec.neg_ofBoolFn]; exact KV.of_ofBoolFn _ _
          | pos =>
              have hw' : xsWidth d a = some w := hw
              obtain ⟨f, rfl⟩ := (ihE a w va hw' ha).ex
              simp only [evalUnaryOp]; rw [LVec.pos_ofBoolFn]; exact KV.of_ofBoolFn _ _
      | resizeSigned w' a =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨va, ha, rfl⟩ := h
          have hw' : (xsWidth d a).map (fun _ => w') = some w := hw
          rw [Option.map_eq_some_iff] at hw'
          obtain ⟨wa, hwa, rfl⟩ := hw'
          obtain ⟨f, rfl⟩ := (ihE a wa va hwa ha).ex
          rw [LVec.resizeSigned_ofBoolFn]; exact KV.of_ofBoolFn _ _
      | squash2 a =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨va, ha, rfl⟩ := h
          have hw' : xsWidth d a = some w := hw
          have k := ihE a w va hw' ha
          have t := KV.toTwoState va
          rw [k.2] at t
          exact t
      | binary op l r =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨a, ha, b, hb, rfl⟩ := h
          have hw' : binW op l r (xsWidth d l) (xsWidth d r) = some w := hw
          exact binW_known hw' (fun x hx => ihE l x a hx ha) (fun x hx => ihE r x b hx hb)
            (fun hc => constNZ_eval hc ha) (fun hc => constNZ_eval hc hb)
      | scmp op l r =>
          simp only [evalExpr2, Res.bind_eq_ok] at h
          obtain ⟨a, ha, b, hb, h⟩ := h
          rcases hl : xsWidth d l with _ | wl
          · have hw' : (if scmpOp op = true then
                (do let _ ← xsWidth d l; let _ ← xsWidth d r; pure 1) else none) = some w := hw
            rw [hl] at hw'; split at hw' <;> first | cases hw' | simp at hw'
          rcases hr : xsWidth d r with _ | wr
          · have hw' : (if scmpOp op = true then
                (do let _ ← xsWidth d l; let _ ← xsWidth d r; pure 1) else none) = some w := hw
            rw [hl, hr] at hw'; split at hw' <;> first | cases hw' | simp at hw'
          have hw' : (if scmpOp op = true then
              (do let _ ← xsWidth d l; let _ ← xsWidth d r; pure 1) else none) = some w := hw
          rw [hl, hr] at hw'
          split at hw'
          · rename_i hop
            obtain rfl := Option.some.inj hw'
            obtain ⟨x, hx⟩ := toInt?_isSome (ihE l wl a hl ha)
            obtain ⟨y, hy⟩ := toInt?_isSome (ihE r wr b hr hb)
            rw [hx, hy] at h
            simp only [Res.pure_eq, Res.ok.injEq] at h
            subst h
            cases op <;> first | exact KV.ite_l1_l0 _ | simp [scmpOp] at hop
          · cases hw'
      | logical isAnd l r =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨a, ha, b, hb, rfl⟩ := h
          have hw0 : (do let _ ← xsWidth d l; let _ ← xsWidth d r; pure 1) = some w := hw
          rcases hl : xsWidth d l with _ | wl
          · rw [hl] at hw0; first | cases hw0 | simp at hw0
          rcases hr : xsWidth d r with _ | wr
          · rw [hl, hr] at hw0; first | cases hw0 | simp at hw0
          rw [hl, hr] at hw0
          have hw' : some 1 = some w := hw0
          obtain rfl := Option.some.inj hw'
          have ka := ihE l wl a hl ha
          have kb := ihE r wr b hr hb
          rw [condTrue_or_isKnownZero ka, condTrue_or_isKnownZero kb]
          generalize a.condTrue = p
          generalize b.condTrue = q
          cases isAnd <;> cases p <;> cases q <;> first
            | exact KV.ofLogic_ofBool false | exact KV.ofLogic_ofBool true
      | ternary c t f =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨cv, hc, tv, ht, fv, hf, rfl⟩ := h
          rcases hcw : xsWidth d c with _ | wc
          · simp [xsWidth, hcw] at hw
          rcases htw : xsWidth d t with _ | wt
          · simp [xsWidth, hcw, htw] at hw
          rcases hfw : xsWidth d f with _ | wf
          · simp [xsWidth, hcw, htw, hfw] at hw
          have hw' : (if wt = wf then some wt else none) = some w := by
            have h0 := hw
            simp only [xsWidth, hcw, htw, hfw] at h0
            exact h0
          split at hw'
          · rename_i heq
            have hw2 : wt = w := Option.some.inj hw'
            rw [← heq] at hfw
            rw [← hw2]
            obtain ⟨g, rfl⟩ := (ihE c wc cv hcw hc).ex
            obtain ⟨g1, rfl⟩ := (ihE t wt tv htw ht).ex
            obtain ⟨g2, rfl⟩ := (ihE f wt fv hfw hf).ex
            rw [XF.ternary_ofBoolFn]; exact KV.of_ofBoolFn _ _
          · cases hw'
      | concat parts =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨vs, hvs, rfl⟩ := h
          have hw' : xsWidthList d parts.toList = some w := hw
          obtain ⟨hk, hsum⟩ := ihL parts.toList w vs hw' hvs
          rw [← hsum]
          exact KV.concat hk
      | slice base lo k =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨vb, hb, rfl⟩ := h
          rcases hbw : xsWidth d base with _ | wb
          · simp [xsWidth, hbw] at hw
          have hw' : (if lo + k ≤ wb then some k else none) = some w := by
            have h0 := hw
            simp only [xsWidth, hbw] at h0
            exact h0
          split at hw'
          · rename_i hin
            have hw2 : k = w := Option.some.inj hw'
            rw [← hw2]
            exact KV.extract (ihE base wb vb hbw hb) hin
          · cases hw'
      | index base idx ew =>
          simp only [evalExpr2, Res.bind_eq_ok] at h
          obtain ⟨vb, hb, vi, hi, h⟩ := h
          rcases hbw : xsWidth d base with _ | wb
          · simp [xsWidth, hbw] at hw
          rcases hiw : xsWidth d idx with _ | wi
          · simp [xsWidth, hbw, hiw] at hw
          have hw' : (if unsignedIdx d idx = true ∧ 2 ^ wi * ew ≤ wb then some ew else none) =
              some w := by
            have h0 := hw
            simp only [xsWidth, hbw, hiw] at h0
            exact h0
          split at hw'
          · rename_i hin
            have hin := hin.2
            have hw2 : ew = w := Option.some.inj hw'
            rw [← hw2]
            have kb := ihE base wb vb hbw hb
            obtain ⟨g, rfl⟩ := (ihE idx wi vi hiw hi).ex
            rw [LVec.toNat?_ofBoolFn] at h
            have hlt := XF.val_lt g wi
            have hrange : (XF.val g wi + 1) * ew ≤ vb.width := by
              rw [kb.2]
              exact Nat.le_trans (Nat.mul_le_mul_right ew hlt) hin
            have h' : (if (XF.val g wi + 1) * ew ≤ vb.width then
                (pure (vb.extract (XF.val g wi * ew) ew) : Res LVec)
              else pure (LVec.xVec ew)) = .ok v := h
            rw [if_pos hrange, Res.pure_eq, Res.ok.injEq] at h'
            subst h'
            refine KV.extract kb ?_
            have e1 : XF.val g wi * ew + ew = (XF.val g wi + 1) * ew := by rw [Nat.succ_mul]
            rw [e1, ← kb.2]
            exact hrange
          · cases hw'
      | repl n a =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨va, ha, rfl⟩ := h
          have hw' : (xsWidth d a).map (· * n) = some w := hw
          rw [Option.map_eq_some_iff] at hw'
          obtain ⟨wa, hwa, rfl⟩ := hw'
          obtain ⟨f, rfl⟩ := (ihE a wa va hwa ha).ex
          rw [LVec.replVec_ofBoolFn]; exact KV.of_ofBoolFn _ _
      | reduce op a =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨va, ha, rfl⟩ := h
          have hw' : (xsWidth d a).map (fun _ => 1) = some w := hw
          rw [Option.map_eq_some_iff] at hw'
          obtain ⟨wa, hwa, rfl⟩ := hw'
          exact KV.ofLogic (redOp_isKnown op (ihE a wa va hwa ha))
      | resize w' a =>
          simp only [evalExpr2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨va, ha, rfl⟩ := h
          have hw' : (xsWidth d a).map (fun _ => w') = some w := hw
          rw [Option.map_eq_some_iff] at hw'
          obtain ⟨wa, hwa, rfl⟩ := hw'
          exact KV.resizeU (ihE a wa va hwa ha) _
      | unsupported _ _ => simp [xsWidth] at hw
    · cases es with
      | nil =>
          simp only [evalExprs2, Res.ok.injEq] at h
          subst h
          have hw' : some 0 = some w := hw
          obtain rfl := Option.some.inj hw'
          exact ⟨fun _ h => by simp at h, rfl⟩
      | cons e es =>
          simp only [evalExprs2, Res.bind_eq_ok, Res.pure_eq, Res.ok.injEq] at h
          obtain ⟨v, hv, vs', hvs', rfl⟩ := h
          have hw0 : (do let a ← xsWidth d e; let b ← xsWidthList d es; pure (a + b)) = some w := hw
          rcases hew : xsWidth d e with _ | we
          · rw [hew] at hw0; first | cases hw0 | simp at hw0
          rcases hesw : xsWidthList d es with _ | wes
          · rw [hew, hesw] at hw0; first | cases hw0 | simp at hw0
          rw [hew, hesw] at hw0
          have hw' : some (we + wes) = some w := hw0
          obtain rfl := Option.some.inj hw'
          have k := ihE e we v hew hv
          obtain ⟨hk, hs⟩ := ihL es wes vs' hesw hvs'
          refine ⟨fun u hu => ?_, ?_⟩
          · rcases List.mem_cons.mp hu with rfl | hu
            · exact k.1
            · exact hk u hu
          · rw [List.map_cons, List.sum_cons, k.2, hs]

/-! ## Statements -/

theorem NbaKnown.append {a b : NbaQueue2} (ha : NbaKnown a) (hb : NbaKnown b) : NbaKnown (a ++ b) := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact ha u hu
  · exact hb u hu

theorem NbaKnown.nil : NbaKnown [] := fun _ h => by simp at h

/-- A known value written into a window of a known signal keeps the state known. -/
theorem KnownState.write {d : Design2} {st : SvState} {n : String} {old p : LVec}
    (hst : KnownState d st) (hold : SvState.lookup st n = some old) (hp : p.allKnown = true)
    (lo : Nat) : KnownState d (SvState.set st n (old.insertAt lo p)) := by
  obtain ⟨hk, hw⟩ := hst n old hold
  have k := KV.insertAt ⟨hk, rfl⟩ hp lo
  exact hst.set k.1 (by rw [k.2]; exact hw)

/-- An invariant of every step of a left fold holds of the fold. -/
theorem foldl_inv {α β : Type} (P : β → Prop) (F : β → α → β) : ∀ (l : List α) (s : β),
    P s → (∀ s u, u ∈ l → P s → P (F s u)) → P (l.foldl F s)
  | [], _, h, _ => h
  | u :: l, s, h, hF => foldl_inv P F l (F s u) (hF s u List.mem_cons_self h)
      (fun s' u' hu' hs' => hF s' u' (List.mem_cons_of_mem _ hu') hs')

/-- A concatenated continuous target: every window of the sampled value is in range, so every
part written is known. -/
theorem writeConcat_go_known {d : Design2} {rep : LVec} (hrep : rep.allKnown = true) :
    ∀ (ws : List (String × Nat × Nat)) (state : SvState) (rw : Nat) (st' : SvState),
      KnownState d state → (ws.map fun x => x.2.2).sum = rw → rw ≤ rep.width →
      writeConcatLhs2.go rep state ws rw = .ok st' → KnownState d st'
  | [], state, rw, st', hs, _, _, h => by
      simp only [writeConcatLhs2.go, Res.ok.injEq] at h
      subst h; exact hs
  | (name, lo, width) :: rest, state, rw, st', hs, hsum, hle, h => by
      simp only [writeConcatLhs2.go] at h
      simp only [List.map_cons, List.sum_cons] at hsum
      split at h
      · cases h
      · rename_i old hold
        refine writeConcat_go_known hrep rest _ (rw - width) st' (hs.write hold ?_ lo)
          (by omega) (by omega) h
        exact (KV.extract ⟨hrep, rfl⟩ (by omega)).1

theorem writeConcat_known {d : Design2} {st : SvState} {v : LVec}
    {ws : List (String × Nat × Nat)} {st' : SvState} (hst : KnownState d st) (hv : v.allKnown = true)
    (h : writeConcatLhs2 st v ws = .ok st') : KnownState d st' := by
  unfold writeConcatLhs2 at h
  refine writeConcat_go_known (KV.resizeU ⟨hv, rfl⟩ _).1 ws st _ st' hst ?_ ?_ h
  · have key : ∀ (l : List (String × Nat × Nat)) (n : Nat),
        l.foldl (fun n (x : String × Nat × Nat) => match x with | (_, _, width) => n + width) n =
          n + (l.map fun x => x.2.2).sum := by
      intro l
      induction l with
      | nil => intro n; simp
      | cons x l ih =>
          intro n
          obtain ⟨a, b, c⟩ := x
          rw [List.foldl_cons, ih]
          simp only [List.map_cons, List.sum_cons]
          omega
    rw [key]; simp
  · simp

/-- **`xfree_stmt`**: on a known state with known pending updates, every statement rule 3 admits
ends in a known state with known pending updates (and so does a case walk, and a block). -/
theorem xfree_stmt {d : Design2} : ∀ fuel : Nat,
    (∀ (s : Stmt2) (st : SvState) (nba : NbaQueue2) (st' : SvState) (nba' : NbaQueue2),
      xsStmt d s = true → KnownState d st → NbaKnown nba →
      execStmt2 fuel st nba s = .ok (st', nba') → KnownState d st' ∧ NbaKnown nba') ∧
    (∀ (items : List CaseItem2) (dflt : Option Stmt2) (mode : CaseMode) (subj : LVec)
      (st : SvState) (nba : NbaQueue2) (st' : SvState) (nba' : NbaQueue2),
      xsItems d mode items = true → xsOpt d dflt = true → KnownState d st → NbaKnown nba →
      execCase2 fuel st nba subj items dflt mode = .ok (st', nba') →
      KnownState d st' ∧ NbaKnown nba') ∧
    (∀ (ss : List Stmt2) (st : SvState) (nba : NbaQueue2) (st' : SvState) (nba' : NbaQueue2),
      xsStmts d ss = true → KnownState d st → NbaKnown nba →
      execStmts2 fuel st nba ss = .ok (st', nba') → KnownState d st' ∧ NbaKnown nba')
  | 0 => ⟨fun _ _ _ _ _ _ _ _ h => by simp [execStmt2] at h,
      fun items _ _ _ _ _ _ _ _ _ _ _ h => by
        cases items with
        | nil => simp [execCase2] at h
        | cons it rest => cases it; simp [execCase2] at h,
      fun _ _ _ _ _ _ _ _ h => by simp [execStmts2] at h⟩
  | f + 1 => by
    obtain ⟨ihS, ihC, ihL⟩ := xfree_stmt f
    refine ⟨fun s st nba st' nba' hx hst hq h => ?_,
      fun items dflt mode subj st nba st' nba' hi hd hst hq h => ?_,
      fun ss st nba st' nba' hx hst hq h => ?_⟩
    · cases s with
      | blockingAssign t e =>
          simp only [xsStmt, Bool.and_eq_true] at hx
          obtain ⟨we, hwe⟩ := Option.isSome_iff_exists.mp hx.2
          cases t with
          | concat ps =>
              simp only [execStmt2, Res.bind_eq_ok] at h
              obtain ⟨v, hv, ws, -, st2, hw, h⟩ := h
              simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨writeConcat_known hst ((xfree_expr hst f).1 e we v hwe hv).1 hw, hq⟩
          | ident m =>
              simp only [execStmt2, Res.bind_eq_ok] at h
              obtain ⟨v, hv, ⟨n, win⟩, -, h⟩ := h
              have kv := (xfree_expr hst f).1 e we v hwe hv
              rcases win with _ | ⟨lo, w⟩
              · simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
              · simp only at h
                split at h
                · rename_i old hold
                  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ⟨hst.write hold (kv.resizeU w).1 lo, hq⟩
                · cases h
          | slice m lo0 w0 =>
              simp only [execStmt2, Res.bind_eq_ok] at h
              obtain ⟨v, hv, ⟨n, win⟩, -, h⟩ := h
              have kv := (xfree_expr hst f).1 e we v hwe hv
              rcases win with _ | ⟨lo, w⟩
              · simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
              · simp only at h
                split at h
                · rename_i old hold
                  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ⟨hst.write hold (kv.resizeU w).1 lo, hq⟩
                · cases h
          | index m i ew =>
              simp only [execStmt2, Res.bind_eq_ok] at h
              obtain ⟨v, hv, ⟨n, win⟩, -, h⟩ := h
              have kv := (xfree_expr hst f).1 e we v hwe hv
              rcases win with _ | ⟨lo, w⟩
              · simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
              · simp only at h
                split at h
                · rename_i old hold
                  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ⟨hst.write hold (kv.resizeU w).1 lo, hq⟩
                · cases h
      | nbaAssign t e =>
          simp only [xsStmt, Bool.and_eq_true] at hx
          obtain ⟨we, hwe⟩ := Option.isSome_iff_exists.mp hx.2
          simp only [execStmt2, Res.bind_eq_ok] at h
          obtain ⟨v, hv, ⟨n, win⟩, -, h⟩ := h
          have kv := (xfree_expr hst f).1 e we v hwe hv
          rcases win with _ | ⟨lo, w⟩
          · simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
          · simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨hst, hq.append fun u hu => ?_⟩
            simp only [List.mem_singleton] at hu
            subst hu
            exact (kv.resizeU w).1
      | ifStmt c th el =>
          simp only [xsStmt, Bool.and_eq_true] at hx
          obtain ⟨⟨-, hth⟩, hel⟩ := hx
          simp only [execStmt2, Res.bind_eq_ok] at h
          obtain ⟨cv, -, h⟩ := h
          split at h
          · exact ihS th st nba st' nba' hth hst hq h
          · cases el with
            | none =>
                simp only [Res.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
            | some s => exact ihS s st nba st' nba' (by simpa [xsOpt] using hel) hst hq h
      | caseStmt subj items dflt mode chk =>
          simp only [xsStmt, Bool.and_eq_true] at hx
          obtain ⟨⟨-, hit⟩, hdf⟩ := hx
          simp only [execStmt2, Res.bind_eq_ok] at h
          obtain ⟨sv, -, h⟩ := h
          exact ihC items.toList dflt mode sv st nba st' nba' hit hdf hst hq h
      | block body =>
          simp only [xsStmt] at hx
          simp only [execStmt2] at h
          exact ihL body.toList st nba st' nba' hx hst hq h
      | unsupported _ _ => simp [xsStmt] at hx
    · cases items with
      | nil =>
          cases dflt with
          | none =>
              simp only [execCase2, Res.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
          | some s =>
              simp only [execCase2] at h
              exact ihS s st nba st' nba' (by simpa [xsOpt] using hd) hst hq h
      | cons it rest =>
          obtain ⟨pats, body⟩ := it
          simp only [xsItems, Bool.and_eq_true] at hi
          obtain ⟨⟨-, hb⟩, hr⟩ := hi
          simp only [execCase2, Res.bind_eq_ok] at h
          obtain ⟨pvs, -, h⟩ := h
          split at h
          · exact ihS body st nba st' nba' hb hst hq h
          · exact ihC rest dflt mode subj st nba st' nba' hr hd hst hq h
    · cases ss with
      | nil =>
          simp only [execStmts2, Res.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
      | cons s rest =>
          simp only [xsStmts, Bool.and_eq_true] at hx
          simp only [execStmts2, Res.bind_eq_ok] at h
          obtain ⟨⟨st1, nba1⟩, h1, h⟩ := h
          obtain ⟨k1, q1⟩ := ihS s st nba st1 nba1 hx.1 hst hq h1
          exact ihL rest st1 nba1 st' nba' hx.2 k1 q1 h

/-! ## Processes, passes, the settle and the cycle -/

theorem xsafe_proc {d : Design2} (hx : XSafe d) {i : Nat} {p : Process2}
    (hp : d.processes[i]? = some p) : xsProc d p = true := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hp
  exact List.all_eq_true.mp hx _ (Array.getElem_mem_toList hi)

theorem xfree_comb {d : Design2} {p : Process2} (hp : xsProc d p = true) {fuel : Nat}
    {st st' : SvState} (hst : KnownState d st) (h : runCombProcess2 fuel st p = .ok st') :
    KnownState d st' := by
  cases p with
  | assign t e =>
      simp only [xsProc, Bool.and_eq_true] at hp
      obtain ⟨we, hwe⟩ := Option.isSome_iff_exists.mp hp.2
      cases t with
      | concat ps =>
          simp only [runCombProcess2, Res.bind_eq_ok] at h
          obtain ⟨v, hv, ws, -, h⟩ := h
          exact writeConcat_known hst ((xfree_expr hst fuel).1 e we v hwe hv).1 h
      | ident m =>
          simp only [runCombProcess2, Res.bind_eq_ok] at h
          obtain ⟨v, hv, ⟨n, win⟩, -, h⟩ := h
          have kv := (xfree_expr hst fuel).1 e we v hwe hv
          rcases win with _ | ⟨lo, w⟩
          · simp only [Res.ok.injEq] at h; subst h; exact hst
          · simp only at h
            split at h
            · rename_i old hold
              simp only [Res.ok.injEq] at h; subst h
              exact hst.write hold (kv.resizeU w).1 lo
            · cases h
      | slice m lo0 w0 =>
          simp only [runCombProcess2, Res.bind_eq_ok] at h
          obtain ⟨v, hv, ⟨n, win⟩, -, h⟩ := h
          have kv := (xfree_expr hst fuel).1 e we v hwe hv
          rcases win with _ | ⟨lo, w⟩
          · simp only [Res.ok.injEq] at h; subst h; exact hst
          · simp only at h
            split at h
            · rename_i old hold
              simp only [Res.ok.injEq] at h; subst h
              exact hst.write hold (kv.resizeU w).1 lo
            · cases h
      | index m i ew =>
          simp only [runCombProcess2, Res.bind_eq_ok] at h
          obtain ⟨v, hv, ⟨n, win⟩, -, h⟩ := h
          have kv := (xfree_expr hst fuel).1 e we v hwe hv
          rcases win with _ | ⟨lo, w⟩
          · simp only [Res.ok.injEq] at h; subst h; exact hst
          · simp only at h
            split at h
            · rename_i old hold
              simp only [Res.ok.injEq] at h; subst h
              exact hst.write hold (kv.resizeU w).1 lo
            · cases h
  | alwaysComb b =>
      simp only [xsProc] at hp
      simp only [runCombProcess2, Res.bind_eq_ok] at h
      obtain ⟨⟨st1, nba⟩, h1, h⟩ := h
      have k := (xfree_stmt fuel).1 b st [] st1 nba hp hst NbaKnown.nil h1
      simp only at h
      split at h
      · simp only [Res.ok.injEq] at h; subst h; exact k.1
      · cases h
  | alwaysFF _ _ => simp only [runCombProcess2, Res.ok.injEq] at h; subst h; exact hst
  | alwaysPlain _ _ => simp only [runCombProcess2, Res.ok.injEq] at h; subst h; exact hst
  | alwaysFFR _ _ _ _ => simp only [runCombProcess2, Res.ok.injEq] at h; subst h; exact hst
  | unsupported _ _ => simp [runCombProcess2] at h

theorem xfree_combPass {d : Design2} (hx : XSafe d) {fuel : Nat} : ∀ (l : List Nat) (st st' : SvState),
    KnownState d st → combPass2 d fuel st l = .ok st' → KnownState d st'
  | [], st, st', hst, h => by simp only [combPass2, Res.ok.injEq] at h; subst h; exact hst
  | i :: rest, st, st', hst, h => by
      rw [combPass2] at h
      split at h
      · rename_i p hp
        obtain ⟨st1, h1, h⟩ := Res.bind_eq_ok.mp h
        exact xfree_combPass hx rest st1 st' (xfree_comb (xsafe_proc hx hp) hst h1) h
      · obtain ⟨st1, h1, h⟩ := Res.bind_eq_ok.mp h
        simp only [Res.pure_eq, Res.ok.injEq] at h1
        subst h1
        exact xfree_combPass hx rest _ st' hst h

/-- **The settle** keeps the state known. -/
theorem xfree_combSettle {d : Design2} (hx : XSafe d) {σ : ScheduleOracle} : ∀ (fuel : Nat)
    (st : SvState) (k : Nat) (st' : SvState) (k' : Nat),
    KnownState d st → combSettle2 d σ fuel st k = .ok (st', k') → KnownState d st'
  | 0, _, _, _, _, _, h => by simp [combSettle2] at h
  | f + 1, st, k, st', k', hst, h => by
      simp only [combSettle2, Res.bind_eq_ok] at h
      obtain ⟨st1, h1, h⟩ := h
      have k1 := xfree_combPass hx _ st st1 hst h1
      split at h
      · simp only [Res.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h; exact k1
      · exact xfree_combSettle hx f st1 (k + 1) st' k' k1 h

theorem xfree_resetProc {d : Design2} {p : Process2} (hp : xsProc d p = true) {fuel : Nat}
    {st : SvState} {nba : NbaQueue2} {st' : SvState} {nba' : NbaQueue2} (hst : KnownState d st)
    (hq : NbaKnown nba) (h : runResetProcess2 fuel st nba p = .ok (st', nba')) :
    KnownState d st' ∧ NbaKnown nba' := by
  cases p with
  | alwaysFFR _ _ b _ =>
      simp only [xsProc] at hp
      simp only [runResetProcess2] at h
      exact (xfree_stmt fuel).1 b st nba st' nba' hp hst hq h
  | _ =>
      simp only [runResetProcess2, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩

theorem xfree_edgeProc {d : Design2} {p : Process2} (hp : xsProc d p = true) {fuel : Nat}
    {st : SvState} {nba : NbaQueue2} {st' : SvState} {nba' : NbaQueue2} (hst : KnownState d st)
    (hq : NbaKnown nba) (h : runEdgeProcess2 fuel st nba p = .ok (st', nba')) :
    KnownState d st' ∧ NbaKnown nba' := by
  cases p with
  | alwaysFF _ b =>
      simp only [xsProc] at hp
      simp only [runEdgeProcess2] at h
      exact (xfree_stmt fuel).1 b st nba st' nba' hp hst hq h
  | alwaysPlain _ b =>
      simp only [xsProc] at hp
      simp only [runEdgeProcess2] at h
      exact (xfree_stmt fuel).1 b st nba st' nba' hp hst hq h
  | alwaysFFR _ _ b _ =>
      simp only [xsProc] at hp
      simp only [runEdgeProcess2] at h
      exact (xfree_stmt fuel).1 b st nba st' nba' hp hst hq h
  | alwaysComb _ =>
      simp only [runEdgeProcess2, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
  | assign _ _ =>
      simp only [runEdgeProcess2, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
  | unsupported _ _ => simp [runEdgeProcess2] at h

theorem xfree_resetPass {d : Design2} (hx : XSafe d) {fuel : Nat} : ∀ (l : List Nat) (st : SvState)
    (nba : NbaQueue2) (st' : SvState) (nba' : NbaQueue2), KnownState d st → NbaKnown nba →
    resetPass2 d fuel st nba l = .ok (st', nba') → KnownState d st' ∧ NbaKnown nba'
  | [], st, nba, st', nba', hst, hq, h => by
      simp only [resetPass2, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
  | i :: rest, st, nba, st', nba', hst, hq, h => by
      rw [resetPass2] at h
      split at h
      · rename_i p hp
        obtain ⟨⟨st1, nba1⟩, h1, h⟩ := Res.bind_eq_ok.mp h
        obtain ⟨k1, q1⟩ := xfree_resetProc (xsafe_proc hx hp) hst hq h1
        exact xfree_resetPass hx rest st1 nba1 st' nba' k1 q1 h
      · obtain ⟨⟨st1, nba1⟩, h1, h⟩ := Res.bind_eq_ok.mp h
        simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact xfree_resetPass hx rest st nba st' nba' hst hq h

theorem xfree_edgePass {d : Design2} (hx : XSafe d) {fuel : Nat} : ∀ (l : List Nat) (st : SvState)
    (nba : NbaQueue2) (st' : SvState) (nba' : NbaQueue2), KnownState d st → NbaKnown nba →
    edgePass2 d fuel st nba l = .ok (st', nba') → KnownState d st' ∧ NbaKnown nba'
  | [], st, nba, st', nba', hst, hq, h => by
      simp only [edgePass2, Res.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨hst, hq⟩
  | i :: rest, st, nba, st', nba', hst, hq, h => by
      rw [edgePass2] at h
      split at h
      · rename_i p hp
        obtain ⟨⟨st1, nba1⟩, h1, h⟩ := Res.bind_eq_ok.mp h
        obtain ⟨k1, q1⟩ := xfree_edgeProc (xsafe_proc hx hp) hst hq h1
        exact xfree_edgePass hx rest st1 nba1 st' nba' k1 q1 h
      · obtain ⟨⟨st1, nba1⟩, h1, h⟩ := Res.bind_eq_ok.mp h
        simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact xfree_edgePass hx rest st nba st' nba' hst hq h

/-- **The NBA commit** of known updates keeps the state known. -/
theorem xfree_commit {d : Design2} {st : SvState} {nba : NbaQueue2} (hst : KnownState d st)
    (hq : NbaKnown nba) : KnownState d (commitNba2 st nba) := by
  unfold commitNba2
  refine foldl_inv (KnownState d) _ nba st hst (fun s u hu hs => ?_)
  try dsimp only
  split
  · rename_i old hold; exact hs.write hold (hq u hu) _
  · exact hs

/-- **Applying a known entry** keeps the state known. -/
theorem xfree_apply {d : Design2} {st e : SvState} (hst : KnownState d st) (he : KnownEntry d e) :
    KnownState d (applyInputs2 d e st) := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  refine foldl_inv (KnownState d) _ d.decls.toList st hst (fun s dc hdc hs => ?_)
  try dsimp only
  split
  · rename_i hin
    split
    · rename_i v hv
      have hn : dc.name ∈ d.inputNames.toList := by
        simp only [Design2.inputNames, Array.toList_filterMap, List.mem_filterMap]
        exact ⟨dc, hdc, by simp [hin]⟩
      have h1 := he dc.name hn
      rw [hv] at h1
      simp only [Option.all_some, Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨hk, hw⟩ := h1
      split
      · have t := KV.toTwoState v
        exact hs.set t.1 (by rw [t.2]; exact hw)
      · exact hs.set hk hw
    · exact hs
  · exact hs

/-- **`xfree_cycle`**: one clock cycle of a rule-3 design, from a known state on a known entry,
ends in a known state (and every state it passes through is known: the settles, the reset
phase, the edge phase and the commits are the lemmas above). -/
theorem xfree_cycle {d : Design2} (hx : XSafe d) {σ : ScheduleOracle} {fuel : Nat}
    {e st : SvState} {k : Nat} {st' : SvState} {k' : Nat} (hst : KnownState d st)
    (he : KnownEntry d e) (h : cycleStep2 d σ fuel e st k = .ok (st', k')) : KnownState d st' := by
  have h0 := xfree_apply hst he
  rw [Observe.cycleStep2_eq_pre_post] at h
  obtain ⟨⟨pre, k2⟩, hpre, hpost⟩ := Res.bind_eq_ok.mp h
  have hpre' : Observe.cyclePre2 d σ fuel e st k = .ok (pre, k2) := hpre
  unfold Observe.cyclePre2 at hpre'
  obtain ⟨⟨st1, k1⟩, h1, hrp⟩ := Res.bind_eq_ok.mp hpre'
  have hrp' : Observe.resetPhase2 d σ fuel st st1 k1 = .ok (pre, k2) := hrp
  have k1' := xfree_combSettle hx _ _ _ _ _ h0 h1
  have kpre : KnownState d pre := by
    dsimp only [Observe.resetPhase2] at hrp'
    split at hrp'
    · simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at hrp'
      obtain ⟨rfl, rfl⟩ := hrp'; exact k1'
    · obtain ⟨⟨str, nbar⟩, hr, hs⟩ := Res.bind_eq_ok.mp hrp'
      have hs' : combSettle2 d σ fuel (commitNba2 str nbar) (k1 + 1) = .ok (pre, k2) := hs
      obtain ⟨kr, qr⟩ := xfree_resetPass hx _ _ _ _ _ k1' NbaKnown.nil hr
      exact xfree_combSettle hx _ _ _ _ _ (xfree_commit kr qr) hs'
  have hpost' : Observe.cyclePost2 d σ fuel pre k2 = .ok (st', k') := hpost
  unfold Observe.cyclePost2 at hpost'
  obtain ⟨⟨st3, nba⟩, h3, h4⟩ := Res.bind_eq_ok.mp hpost'
  have h4' : combSettle2 d σ fuel (commitNba2 st3 nba) (k2 + 1) = .ok (st', k') := h4
  obtain ⟨k3, q3⟩ := xfree_edgePass hx _ _ _ _ _ kpre NbaKnown.nil h3
  exact xfree_combSettle hx _ _ _ _ _ (xfree_commit k3 q3) h4'

/-- **`xfree_run`**: every snapshot of a run of a rule-3 design from a known state on a known
stimulus is known. -/
theorem xfree_run {d : Design2} (hx : XSafe d) {σ : ScheduleOracle} {fuel : Nat} :
    ∀ (stim : List SvState) (st : SvState) (k : Nat) (tr : List SvState),
      KnownState d st → KnownStim d stim → runFrom2 d σ fuel st k stim = .ok tr →
      ∀ s ∈ tr, KnownState d s
  | [], st, k, tr, _, _, h => by
      simp only [runFrom2_nil, Res.ok.injEq] at h
      subst h; simp
  | e :: rest, st, k, tr, hst, hstim, h => by
      obtain ⟨st1, k1, tr1, h1, h2, rfl⟩ := runFrom2_cons_eq_ok.mp h
      have k1' := xfree_cycle hx hst (hstim e List.mem_cons_self) h1
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact k1'
      · exact xfree_run hx rest st1 k1 tr1 k1'
          (fun e' he' => hstim e' (List.mem_cons_of_mem _ he')) h2 s hs

/-! ## Power-up states and `run2At` -/

theorem knownState_of_zip : ∀ (st : SvState) (ds : List Decl), st.map Prod.fst = ds.map Decl.name →
    (∀ b ∈ st.zip ds, b.1.2.width = b.2.width ∧ b.1.2.allKnown = true) →
    ∀ n v, SvState.lookup st n = some v →
      v.allKnown = true ∧ (ds.find? fun dc => dc.name == n).map Decl.width = some v.width
  | [], _, _, _, n, v, h => by simp [SvState.lookup] at h
  | _ :: _, [], hm, _, _, _, _ => by simp at hm
  | (k, x) :: st, dc :: ds, hm, hz, n, v, h => by
      simp only [List.map_cons, List.cons.injEq] at hm
      obtain ⟨hk, hm⟩ := hm
      have hb := hz ((k, x), dc) (by simp)
      simp only [SvState.lookup] at h
      by_cases hkn : k = n
      · subst hkn
        simp only [beq_self_eq_true, if_true, Option.some.injEq] at h
        subst h
        refine ⟨hb.2, ?_⟩
        rw [List.find?_cons_of_pos (by simp [hk])]
        simp [hb.1]
      · rw [if_neg (by simpa using hkn)] at h
        have := knownState_of_zip st ds hm (fun b hb' => hz b (by simp [hb'])) n v h
        refine ⟨this.1, ?_⟩
        rw [List.find?_cons_of_neg (by rw [← hk]; simpa using hkn)]
        exact this.2

/-- A power-up state is known. -/
theorem KnownState.of_powerUp {d : Design2} {st : SvState} (h : PowerUp d st) : KnownState d st :=
  fun n v hv => knownState_of_zip st d.decls.toList h.1 h.2 n v hv

/-- `run2At`'s trace is `runFrom2`'s (the validation only checks it). -/
theorem runFrom2_of_run2At {d : Design2} {σ : ScheduleOracle} {fuel : Nat} {st0 : SvState}
    {stim tr : List SvState} (h : run2At d σ fuel st0 stim = .ok tr) :
    runFrom2 d σ fuel st0 0 stim = .ok tr := by
  simp only [run2At] at h
  obtain ⟨tr', hrun, hv⟩ := Res.bind_eq_ok.mp h
  by_cases hq : d.processes.toList.any Process2.hasQualifiedCase = true
  · simp only [if_pos hq] at hv
    obtain ⟨u, _, hu⟩ := Res.bind_eq_ok.mp hv
    have heq : tr' = tr := Res.ok.inj hu
    simpa [heq] using hrun
  · simp only [if_neg hq] at hv
    have heq : tr' = tr := Res.ok.inj hv
    simpa [heq] using hrun

/-- **`xfree_runsAt`**: every snapshot of every run of a rule-3 design from a power-up state on a
known stimulus is known. So no decision of such a run reads an `x`. -/
theorem xfree_runsAt {d : Design2} (hx : XSafe d) {σ : ScheduleOracle} {st0 : SvState}
    {stim tr : List SvState} (hpu : PowerUp d st0) (hstim : KnownStim d stim)
    (h : RunsAt d σ st0 stim tr) : ∀ s ∈ tr, KnownState d s := by
  obtain ⟨fuel, h⟩ := h
  exact xfree_run hx stim st0 0 tr (KnownState.of_powerUp hpu) hstim (runFrom2_of_run2At h)

#print axioms xfree_expr
#print axioms xfree_stmt
#print axioms xfree_cycle
#print axioms xfree_run
#print axioms xfree_runsAt


end SvGolf

import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombSlotE
import LeanModels.Sv.Known2

/-!
# Two of ibex_alu's refused `always_comb` blocks, over E-core-0 (WS3, X7 acceptance) — *derived from E*

X7 (arch-measure, `X7.md` B.3) found six `always_comb` blocks of `ibex_alu` that today's comb route
refuses. `x7_blocks.py` takes each VERBATIM from WS4's slicer output (`ibex_alu@rv32bnone`,
sha256-checked) and wraps it as its own module; the extractor gives the envelopes (`x7blocks/*.sv.json`).
That code is third-party and lives in scratch only; this file holds no ibex text. It is compiled by
`compile-x7.sh` from the scratch directory.

Each block's single activation over E-core-0 is proved against a plain local spec, through the comb
fragment (`CombFragE.lean`): `activate_single`, then the meaning computed.

* `bwlogic`: `unique case (1'b1)` over two select signals (writes `bwlogic_result`). The `unique` claim
  is the hypothesis `hclaim` (not both selects set), never dropped.
* `adder_flags`: four defaults, then a plain `case (operator_i)` overriding one of them, with three
  `if (1'b0)` arms (writes FOUR signals).

`*_sem` checks the extraction: the instantiated design is the body written here.

**Whole slots** (`CombSlotE.lean`): `adder_flags` passes the written-before-read check on its four
outputs, so the single-process design is a `SingleE` and `adder_flags_slot` holds: every legal
schedule closes the slot at one configuration, with the spec's values. `bwlogic`'s `unique` claim is
about its inputs, which a typed view need not keep, so it is not a `SingleE`: `bwlogic_slot` goes
through `slot_claimed`, which asks the claim of the slot's opening only (LOOP-NOTE §9.11). The negative
fixture `latch.sv` (own code) is in the fragment and the
check refuses it (`latch_refused`).
-/

namespace SvGolf.Design.LoopX7

open LeanModels.Sv LeanModels.Sv.Loop2 LeanModels.Sv.Kernel

load_design_sv2 x7bw from "x7blocks/bwlogic.sv.json"
load_design_sv2 x7af from "x7blocks/adder_flags.sv.json"

/-- A declared signal's width, in a typed view. -/
theorem width_decl {E : Elab} {σ : Store} (hT : E.Typed σ) {n : String} {w : Nat}
    (h : E.toDesign2.declWidth n = some w) :
    ∃ old, SvState.lookup (E.view σ) n = some old ∧ (sig (E.view σ) n).width = w := by
  obtain ⟨old, hold, hw⟩ := Elab.lookup_declared hT h
  exact ⟨old, hold, by simp [sig, hold, hw]⟩

/-! ## `bwlogic`: `unique case (1'b1)` over signals -/

def bwBody : Stmt2 := .block #[.caseStmt (.lit ⟨#[.l1]⟩)
  #[.mk #[.ident "bwlogic_or"] (.blockingAssign (.ident "bwlogic_result") (.ident "bwlogic_or_result")),
    .mk #[.ident "bwlogic_and"] (.blockingAssign (.ident "bwlogic_result") (.ident "bwlogic_and_result"))]
  (some (.blockingAssign (.ident "bwlogic_result") (.ident "bwlogic_xor_result"))) .normal .unique]

def bwDecls : Array Decl :=
  #[{ name := "bwlogic_or", width := 1, isInput := true }, { name := "bwlogic_and", width := 1, isInput := true },
    { name := "bwlogic_or_result", width := 32, isInput := true },
    { name := "bwlogic_and_result", width := 32, isInput := true },
    { name := "bwlogic_xor_result", width := 32, isInput := true },
    { name := "bwlogic_result", width := 32, isOutput := true }]

theorem bw_sem : x7bw.sem = ⟨"x7_bwlogic", bwDecls, #[.alwaysComb bwBody]⟩ := by
  refine sem_single rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rfl
  · simp [instStmt2, instStmts2, instItems2, instPats2, caseWidth2, fitExpr2, rigidExpr, selfWidth2,
      List.lookup, LeanModels.Sv.CombView.DeclT.elemW, LVec.width]
    rfl
  · decide
  · decide

/-- The instantiated `bwlogic` design. -/
abbrev bwD : Design2 := ⟨"x7_bwlogic", bwDecls, #[.alwaysComb bwBody]⟩

theorem bw_ok : bwBody.combOk bwD = true := by decide

theorem bw_all4 : AllFour (Elab.ofDesign2 bwD) := by unfold AllFour; decide

/-- `unique`'s claim, from the plain hypothesis that the two selects are not both set. -/
theorem bw_claims (st : SvState) {o a : Bool}
    (ho : SvState.lookup st "bwlogic_or" = some (.ofBitVec (.ofBool o)))
    (ha : SvState.lookup st "bwlogic_and" = some (.ofBitVec (.ofBool a)))
    (hclaim : ¬ (o = true ∧ a = true)) : bwBody.claims bwD st := by
  have hl1 : (⟨#[.l1]⟩ : LVec) = .ofBitVec 1#1 := by decide
  cases o <;> cases a <;>
    simp_all [bwBody, Stmt2.claims, Stmt2.listClaims, Stmt2.optClaims, CaseItem2.listClaims,
      CaseItem2.armClaims, CaseItem2.pats, armHit, evs, ev, caseClaim, readSignal, caseHit]

/-- The body's meaning on a view (backend-free). -/
theorem bw_mean (st : SvState) {o a : Bool} {ro ra rx : BitVec 32}
    (ho : SvState.lookup st "bwlogic_or" = some (.ofBitVec (.ofBool o)))
    (ha : SvState.lookup st "bwlogic_and" = some (.ofBitVec (.ofBool a)))
    (hro : SvState.lookup st "bwlogic_or_result" = some (.ofBitVec ro))
    (hra : SvState.lookup st "bwlogic_and_result" = some (.ofBitVec ra))
    (hrx : SvState.lookup st "bwlogic_xor_result" = some (.ofBitVec rx))
    (hw : (sig st "bwlogic_result").width = 32) :
    SvState.lookup (bwBody.sem bwD st) "bwlogic_result" =
        some (.ofBitVec (if o then ro else if a then ra else rx)) := by
  have hl1 : (⟨#[.l1]⟩ : LVec) = .ofBitVec 1#1 := by decide
  simp only [bwBody, Stmt2.sem, Stmt2.listSem, Stmt2.optSem, CaseItem2.listSem, CaseItem2.armSem,
    armHit, evs, ev, evalPure2, evalPures2, readSignal, ho, ha, hro, hra, hrx, hl1]
  cases o <;> cases a <;>
    simp [caseHit_ofBitVec, Lhs2.staticWin, Lhs2.window?, Design2.declWidth, bwDecls, LVec.insertAt_zero_of_width_eq, hw]

/-- **The bitwise-logic select, one activation over E-core-0**: the OR result when `bwlogic_or`, else
the AND result when `bwlogic_and`, else the XOR result, under `unique`'s claim. -/
theorem bwlogic_E {σ : Store} (hT : (Elab.ofDesign2 x7bw.sem).Typed σ) {o a : Bool}
    {ro ra rx : BitVec 32}
    (ho : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view σ) "bwlogic_or" = some (.ofBitVec (.ofBool o)))
    (ha : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view σ) "bwlogic_and" = some (.ofBitVec (.ofBool a)))
    (hro : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view σ) "bwlogic_or_result" = some (.ofBitVec ro))
    (hra : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view σ) "bwlogic_and_result" = some (.ofBitVec ra))
    (hrx : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view σ) "bwlogic_xor_result" = some (.ofBitVec rx))
    (hclaim : ¬ (o = true ∧ a = true)) :
    ∃ σ', activate (Elab.ofDesign2 x7bw.sem) 0 σ = .ok (.ok (), σ') ∧
      SvState.lookup ((Elab.ofDesign2 x7bw.sem).view σ') "bwlogic_result" =
        some (.ofBitVec (if o then ro else if a then ra else rx)) := by
  rw [bw_sem] at hT ho ha hro hra hrx ⊢
  obtain ⟨_, -, hw⟩ := width_decl hT (n := "bwlogic_result") (w := 32) (by decide)
  obtain ⟨σ', h1, -, hv⟩ := activate_single rfl bw_all4 bw_ok hT (bw_claims _ ho ha hclaim)
  exact ⟨σ', h1, by rw [hv]; exact bw_mean _ ho ha hro hra hrx hw⟩

/-- **The bitwise-logic select, one whole slot over E-core-0**: from a typed opening with the process
ready (or the store settled), whose select inputs keep `unique`'s claim, every legal schedule closes the
slot at ONE configuration, holding the OR result when `bwlogic_or`, else the AND result when
`bwlogic_and`, else the XOR result (`CombSlotE.slot_claimed`). -/
theorem bwlogic_slot (ch : Choice) {c : Config} (hT : (Elab.ofDesign2 x7bw.sem).Typed c.store)
    (hc : (c.active = [] ∧ bwBody.sem bwD ((Elab.ofDesign2 x7bw.sem).view c.store) =
      (Elab.ofDesign2 x7bw.sem).view c.store) ∨ c.active = [0]) {o a : Bool} {ro ra rx : BitVec 32}
    (ho : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view c.store) "bwlogic_or" = some (.ofBitVec (.ofBool o)))
    (ha : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view c.store) "bwlogic_and" = some (.ofBitVec (.ofBool a)))
    (hro : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view c.store) "bwlogic_or_result" = some (.ofBitVec ro))
    (hra : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view c.store) "bwlogic_and_result" = some (.ofBitVec ra))
    (hrx : SvState.lookup ((Elab.ofDesign2 x7bw.sem).view c.store) "bwlogic_xor_result" = some (.ofBitVec rx))
    (hclaim : ¬ (o = true ∧ a = true)) :
    ∃ c', (∀ c'', SlotCloses (Elab.ofDesign2 x7bw.sem) ch c c'' ↔ c'' = c') ∧ c'.active = [] ∧
      SvState.lookup ((Elab.ofDesign2 x7bw.sem).view c'.store) "bwlogic_result" =
        some (.ofBitVec (if o then ro else if a then ra else rx)) := by
  rw [bw_sem] at hT hc ho ha hro hra hrx ⊢
  obtain ⟨_, -, hw⟩ := width_decl hT (n := "bwlogic_result") (w := 32) (by decide)
  have hW : ∀ X ∈ bwBody.targetWins bwD, X.1 ∈ ["bwlogic_result"] := by decide
  have hfr := fun y (hy : y ∉ ["bwlogic_result"]) => Stmt2.sem_frame hW hy
    ((Elab.ofDesign2 bwD).view c.store)
  obtain ⟨c', hu, ha', -, hv⟩ := slot_claimed rfl bw_all4 (by decide) bw_ok hW (by decide) ch hT hc
    (bw_claims _ ho ha hclaim)
    (bw_claims _ ((hfr _ (by decide)).trans ho) ((hfr _ (by decide)).trans ha) hclaim)
  exact ⟨c', hu, ha', by rw [hv]; exact bw_mean _ ho ha hro hra hrx hw⟩

/-! ## `adder_flags`: defaults, then a plain `case` overriding them (four writes) -/

/-- The operators that negate the adder's second operand (the arm's pattern list, in order). -/
def negOps : List (BitVec 7) :=
  [1#7, 27#7, 28#7, 25#7, 26#7, 23#7, 24#7, 40#7, 41#7, 29#7, 30#7, 31#7, 32#7]

def afBody : Stmt2 := .block #[
  .blockingAssign (.ident "adder_op_a_shift1") (.lit (.ofNat 1 0)),
  .blockingAssign (.ident "adder_op_a_shift2") (.lit (.ofNat 1 0)),
  .blockingAssign (.ident "adder_op_a_shift3") (.lit (.ofNat 1 0)),
  .blockingAssign (.ident "adder_op_b_negate") (.lit (.ofNat 1 0)),
  .caseStmt (.ident "operator_i")
    #[.mk (negOps.map fun k => Expr2.lit (.ofBitVec k)).toArray
        (.blockingAssign (.ident "adder_op_b_negate") (.lit (.ofNat 1 1))),
      .mk #[.lit (.ofNat 7 20)]
        (.ifStmt (.lit (.ofNat 1 0)) (.blockingAssign (.ident "adder_op_a_shift1") (.lit (.ofNat 1 1))) none),
      .mk #[.lit (.ofNat 7 21)]
        (.ifStmt (.lit (.ofNat 1 0)) (.blockingAssign (.ident "adder_op_a_shift2") (.lit (.ofNat 1 1))) none),
      .mk #[.lit (.ofNat 7 22)]
        (.ifStmt (.lit (.ofNat 1 0)) (.blockingAssign (.ident "adder_op_a_shift3") (.lit (.ofNat 1 1))) none)]
    (some (.block #[])) .normal .none]

def afDecls : Array Decl :=
  #[{ name := "operator_i", width := 7, isInput := true },
    { name := "adder_op_a_shift1", width := 1, isOutput := true },
    { name := "adder_op_a_shift2", width := 1, isOutput := true },
    { name := "adder_op_a_shift3", width := 1, isOutput := true },
    { name := "adder_op_b_negate", width := 1, isOutput := true }]

theorem af_sem : x7af.sem = ⟨"x7_adder_flags", afDecls, #[.alwaysComb afBody]⟩ := by
  refine sem_single rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rfl
  · simp [instStmt2, instStmts2, instItems2, instPats2, caseWidth2, fitExpr2, rigidExpr, selfWidth2,
      List.lookup, LeanModels.Sv.CombView.DeclT.elemW, LVec.width]
    rfl
  · decide
  · decide

/-- The instantiated `adder_flags` design. -/
abbrev afD : Design2 := ⟨"x7_adder_flags", afDecls, #[.alwaysComb afBody]⟩

theorem af_ok : afBody.combOk afD = true := by decide

theorem af_all4 : AllFour (Elab.ofDesign2 afD) := by unfold AllFour; decide

/-- A plain `case`: no claim. -/
theorem af_claims (st : SvState) : afBody.claims afD st := by
  simp [afBody, Stmt2.claims, Stmt2.listClaims, Stmt2.optClaims, CaseItem2.listClaims,
    CaseItem2.armClaims, caseClaim]

/-- The body's meaning on a view (backend-free). -/
theorem af_mean (st : SvState) {x : BitVec 7}
    (hx : SvState.lookup st "operator_i" = some (.ofBitVec x))
    (hw1 : (sig st "adder_op_a_shift1").width = 1) (hw2 : (sig st "adder_op_a_shift2").width = 1)
    (hw3 : (sig st "adder_op_a_shift3").width = 1) (hw4 : (sig st "adder_op_b_negate").width = 1) :
    SvState.lookup (afBody.sem afD st) "adder_op_b_negate" =
        some (.ofBitVec (.ofBool (decide (x ∈ negOps)))) ∧
      SvState.lookup (afBody.sem afD st) "adder_op_a_shift1" = some (.ofBitVec 0#1) ∧
      SvState.lookup (afBody.sem afD st) "adder_op_a_shift2" = some (.ofBitVec 0#1) ∧
      SvState.lookup (afBody.sem afD st) "adder_op_a_shift3" = some (.ofBitVec 0#1) := by
  simp (config := { decide := true }) [afBody, Stmt2.sem, Stmt2.listSem, Stmt2.optSem,
    CaseItem2.listSem, CaseItem2.armSem, armHit, evs, ev, readSignal, caseHit_ofBitVec, hx,
    Lhs2.staticWin, Lhs2.window?, Design2.declWidth, afDecls, LVec.insertAt_zero_of_width_eq, hw1, hw2, hw3, hw4, negOps,
    SvState.lookup_set]
  by_cases hn : x ∈ negOps
  · simp only [negOps, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) [SvState.lookup_set]
  by_cases h20 : x = 20#7
  · subst h20; simp (config := { decide := true }) [SvState.lookup_set]
  by_cases h21 : x = 21#7
  · subst h21; simp (config := { decide := true }) [SvState.lookup_set]
  by_cases h22 : x = 22#7
  · subst h22; simp (config := { decide := true }) [SvState.lookup_set]
  simp only [negOps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  simp (config := { decide := true }) [SvState.lookup_set, hn, h20, h21, h22]

/-- **The adder's operand flags, one activation over E-core-0**: `adder_op_b_negate` is set exactly for
the operators `negOps`, and the three shift flags are cleared (their arms are `if (1'b0)`). -/
theorem adder_flags_E {σ : Store} (hT : (Elab.ofDesign2 x7af.sem).Typed σ) {x : BitVec 7}
    (hx : SvState.lookup ((Elab.ofDesign2 x7af.sem).view σ) "operator_i" = some (.ofBitVec x)) :
    ∃ σ', activate (Elab.ofDesign2 x7af.sem) 0 σ = .ok (.ok (), σ') ∧
      SvState.lookup ((Elab.ofDesign2 x7af.sem).view σ') "adder_op_b_negate" =
        some (.ofBitVec (.ofBool (decide (x ∈ negOps)))) ∧
      SvState.lookup ((Elab.ofDesign2 x7af.sem).view σ') "adder_op_a_shift1" = some (.ofBitVec 0#1) ∧
      SvState.lookup ((Elab.ofDesign2 x7af.sem).view σ') "adder_op_a_shift2" = some (.ofBitVec 0#1) ∧
      SvState.lookup ((Elab.ofDesign2 x7af.sem).view σ') "adder_op_a_shift3" = some (.ofBitVec 0#1) := by
  rw [af_sem] at hT hx ⊢
  obtain ⟨_, -, hw1⟩ := width_decl hT (n := "adder_op_a_shift1") (w := 1) (by decide)
  obtain ⟨_, -, hw2⟩ := width_decl hT (n := "adder_op_a_shift2") (w := 1) (by decide)
  obtain ⟨_, -, hw3⟩ := width_decl hT (n := "adder_op_a_shift3") (w := 1) (by decide)
  obtain ⟨_, -, hw4⟩ := width_decl hT (n := "adder_op_b_negate") (w := 1) (by decide)
  obtain ⟨σ', h1, -, hv⟩ := activate_single rfl af_all4 af_ok hT (af_claims _)
  exact ⟨σ', h1, by rw [hv]; exact af_mean _ hx hw1 hw2 hw3 hw4⟩

/-! ## `adder_flags`: every slot (CombSlotE)

Its body passes the written-before-read check on its four outputs, so the single-process design is a
`SingleE` (`singleE_comb`), and `SingleE.slot` gives the whole slot. -/

/-- The signals `adder_flags` writes. -/
def afW : List String := ["adder_op_a_shift1", "adder_op_a_shift2", "adder_op_a_shift3", "adder_op_b_negate"]

theorem af_singleE : SingleE (Elab.ofDesign2 afD) afBody (CombInv afD) (afBody.sem afD) afW :=
  singleE_comb rfl af_all4 (by decide) af_ok (by decide) (by decide) (by decide) fun st _ => af_claims st

/-- **The adder's operand flags, one whole slot over E-core-0**: from a typed opening with the process
ready (or the store settled), every legal schedule closes the slot at ONE configuration, where
`adder_op_b_negate` is set exactly for `negOps` and the shift flags are 0. -/
theorem adder_flags_slot (ch : Choice) {c : Config} (hT : (Elab.ofDesign2 x7af.sem).Typed c.store)
    (hc : (c.active = [] ∧ afBody.sem afD ((Elab.ofDesign2 x7af.sem).view c.store) =
      (Elab.ofDesign2 x7af.sem).view c.store) ∨ c.active = [0]) {x : BitVec 7}
    (hx : SvState.lookup ((Elab.ofDesign2 x7af.sem).view c.store) "operator_i" = some (.ofBitVec x)) :
    ∃ c', (∀ c'', SlotCloses (Elab.ofDesign2 x7af.sem) ch c c'' ↔ c'' = c') ∧ c'.active = [] ∧
      SvState.lookup ((Elab.ofDesign2 x7af.sem).view c'.store) "adder_op_b_negate" =
        some (.ofBitVec (.ofBool (decide (x ∈ negOps)))) ∧
      SvState.lookup ((Elab.ofDesign2 x7af.sem).view c'.store) "adder_op_a_shift1" = some (.ofBitVec 0#1) ∧
      SvState.lookup ((Elab.ofDesign2 x7af.sem).view c'.store) "adder_op_a_shift2" = some (.ofBitVec 0#1) ∧
      SvState.lookup ((Elab.ofDesign2 x7af.sem).view c'.store) "adder_op_a_shift3" = some (.ofBitVec 0#1) := by
  rw [af_sem] at hT hc hx ⊢
  obtain ⟨_, -, hw1⟩ := width_decl hT (n := "adder_op_a_shift1") (w := 1) (by decide)
  obtain ⟨_, -, hw2⟩ := width_decl hT (n := "adder_op_a_shift2") (w := 1) (by decide)
  obtain ⟨_, -, hw3⟩ := width_decl hT (n := "adder_op_a_shift3") (w := 1) (by decide)
  obtain ⟨_, -, hw4⟩ := width_decl hT (n := "adder_op_b_negate") (w := 1) (by decide)
  obtain ⟨c', hu, ha, -, hv⟩ := af_singleE.slot ch hT hc
  refine ⟨c', hu, ha, ?_⟩
  rw [hv]
  exact af_mean _ hx hw1 hw2 hw3 hw4

/-! ## The negative fixture: a latch

`latch.sv` (own code) writes `q` only when `en` is set. It is in the comb fragment, and the check
refuses it: `q` is not written on the `else` path. -/

load_design_sv2 x7latch from "x7blocks/latch.sv.json"

def latchBody : Stmt2 :=
  .block #[.ifStmt (.ident "en") (.blockingAssign (.ident "q") (.ident "d")) none]

def latchDecls : Array Decl :=
  #[{ name := "en", width := 1, isInput := true }, { name := "d", width := 4, isInput := true },
    { name := "q", width := 4, isOutput := true }]

/-- The instantiated `latch` design. -/
abbrev latchD : Design2 := ⟨"x7_latch", latchDecls, #[.alwaysComb latchBody]⟩

theorem latch_sem : x7latch.sem = latchD := by
  refine sem_single rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rfl
  · simp [instStmt2, instStmts2, fitExpr2, rigidExpr, selfWidth2, List.lookup,
      LeanModels.Sv.CombView.DeclT.elemW]
    rfl
  · decide
  · decide

theorem latch_ok : latchBody.combOk latchD = true := by decide

/-- **The check refuses the latch.** -/
theorem latch_refused : combWbr latchD ["q"] latchBody = false := by decide

/-! ## The other four blocks are in the fragment (MEASURED by evaluation, not a proof)

`activate_single` then reduces their activation to `body.sem` too, given the `*_sem` instantiation check and,
for `unique case`, the claim. What each still lacks is a plain spec of `body.sem`: LOOP-NOTE §9.10. -/

load_design_sv2 x7ia from "x7blocks/adder_in_a.sv.json"
load_design_sv2 x7ib from "x7blocks/adder_in_b.sv.json"
load_design_sv2 x7sh from "x7blocks/shifter.sv.json"
load_design_sv2 x7rm from "x7blocks/result_mux.sv.json"

/-- Every process is an `always_comb` whose body is in the comb fragment. -/
def combOkAll (d : Design2) : Bool := d.processes.all fun
  | .alwaysComb b => b.combOk d
  | _ => false

#guard [x7bw.sem, x7af.sem, x7ia.sem, x7ib.sem, x7sh.sem, x7rm.sem].all fun d =>
  d.processes.size == 1 && combOkAll d

#pin_axioms bw_sem bw_claims bw_mean bwlogic_E bwlogic_slot af_sem af_mean adder_flags_E af_singleE adder_flags_slot
  latch_sem latch_ok latch_refused

end SvGolf.Design.LoopX7

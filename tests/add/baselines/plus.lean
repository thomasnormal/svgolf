import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2
import LeanModels.Sv.Comb2

/-!
# The `add` statement for the baseline `tests/add/negative/plus.sv`

The design is Yosys's own adder, one continuous assign with a concatenation target:

    assign {cout, s} = a + b + cin;

This file proves `theorem Submission.solution : Submission.Goal` (the task's
`SvGolf.Tasks.Add.Statement design.sem`) for EVERY `N` in the task's range: `N` stays a
variable, nothing is unrolled and nothing is bit-blasted.

The design uses the run-time `+` that the task bans, so the official check rejects it at
its `banlist` stage, before any Lean stage. This proof is checked by `check.py --lift-banlist`,
which runs every stage with only the task's operator banlist lifted; the statement, the
checker and the library are the task's own. The design stays unrankable: a proved baseline,
not an entry.

The `sv_comb` tactics refuse the design (`sv_structure: outside the supported fragment —
site `plain#0`: concatenation target (outside the v1 fragment)`), so the proof is by hand,
on the route of `tasks/add/reference/add_n_byhand.lean`:

1. **The design at symbolic `N`** (`plus_sem_processes`, `plus_sem_decls`): `instantiate2`
   split into its stages (`PDesign.instantiate2_of_ok`); the one assign instantiates to
   `{cout, s} = resize(a) + resize(b) + resize(cin)` at the target's width `N + 1` (the
   envelope's `17` is the default point's width; the lowering takes the context width at
   every `N`); the one-driver guard passes (`plus_driversOk`, by `rfl`).
2. **The comb profile and acyclicity** (`plus_comb`, `plus_acyclic`): the two windows of the
   target, `cout` and `s`, are disjoint; the one process reads only inputs.
3. **The settled state** (`plus_settled`): the right-hand side evaluates on known inputs to
   the `N + 1`-bit sum (`sv2_known`); `CombEqs.concat_part_ident` reads `s` as its low `N`
   bits and `cout` as its top bit; `sum1_low` and `sum1_carry` are the `BitVec` arithmetic.
   This is the library's `Comb2ConcatExample.cadd_settled` (proved there for a hand-built
   copy of this design), applied to the loaded design.
4. **The statement** (`solution`): `CombTask.satisfiedAt_of_comb`, then the `Nat` bridges
   of `add_n_byhand.lean` (`sum_eq_ofNat`, `carry_eq_ofNat`).
-/

namespace Submission

open LeanModels.Sv SvGolf

/-! ## 1a. The envelope's shape (pinned by `rfl`) -/

/-- The one static process, as the envelope holds it (`17` is the width at the default
`N = 16`; `instExpr2` lowers each marker to the context width of the instance). -/
theorem plus_source :
    design.pdesign.processes =
      [.assignL (.concat [.ident "cout", .ident "s"])
        (.binary (.m0 .add)
          (.binary (.m0 .add) (.resize 17 (.ident "a")) (.resize 17 (.ident "b")))
          (.resize 17 (.ident "cin")))] := rfl

theorem plus_generates : design.pdesign.generates = [] := rfl

theorem plus_others : design.pdesign.others = [] := rfl

/-! ## 1b. The instantiated vocabulary -/

/-- The target `{cout, s}`, MSB-first. -/
def plusTarget : Lhs2 := .concat [.ident "cout", .ident "s"]

/-- `a + b + cin` at the context width `W`, every operand zero-extended to `W` bits. -/
def plusRhs (W : Nat) : Expr2 :=
  .binary .add (.binary .add (.resize W (.ident "a")) (.resize W (.ident "b")))
    (.resize W (.ident "cin"))

/-- The instantiated assign. -/
def plusProc (W : Nat) : Process2 := .assign plusTarget (plusRhs W)

/-- The instantiated declarations, `wv` the width of the `[N-1:0]` ports. -/
def plusDecls (wv : Nat) : List Decl :=
  [{ name := "a", width := wv, isInput := true },
   { name := "b", width := wv, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := wv, isOutput := true },
   { name := "cout", width := 1, isOutput := true }]

/-- The declaration scope: `N` bound, its declared type `int`, 32 bits. -/
def plusScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

/-- The parameter environment (the scope plus its packed-array geometry table). -/
def plusEnv (N : Int) : IEnv :=
  { plusScope N with dims := dimTable (plusScope N) design.pdesign.decls }

/-- Every declaration is 1-D: element width 1. -/
def plusElems : List (String × Nat) := [("a", 1), ("b", 1), ("cin", 1), ("s", 1), ("cout", 1)]

/-! ## 1c. The stages of `instantiate2` at symbolic `N` -/

theorem plus_paramEnv (N : Int) : design.pdesign.paramEnv2 [N] = .ok (plusEnv N) := by
  rfl

theorem plus_decls (N : Int) :
    buildDecls (plusEnv N) design.pdesign.decls = .ok (plusDecls ((N - 1).natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    plusEnv, plusScope, List.lookup, plusDecls, Gen2.except_ok_bind]

theorem plus_elems (N : Int) :
    buildElems (plusEnv N) design.pdesign.decls = .ok plusElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, plusEnv,
    plusScope, List.lookup, plusElems, Gen2.except_ok_bind]

/-- The process environment: the parameter environment with the declared widths. -/
abbrev pEnv (N : Int) (wv : Nat) : IEnv := (plusEnv N).withDecls (plusDecls wv)

theorem pEnv_widths (N : Int) (wv : Nat) :
    (pEnv N wv).widths = [("a", wv), ("b", wv), ("cin", 1), ("s", wv), ("cout", 1)] := rfl

/-- The target `{cout, s}`: two whole signals, context width `1 + wv`. -/
theorem plus_lhs (N : Int) (wv : Nat) :
    instLhs2 (pEnv N wv) plusElems (.concat [.ident "cout", .ident "s"]) =
      .ok (plusTarget, 1 + wv) := by
  simp [instLhs2, instLhsLeaf2, concatLeafExact, plusDecls, List.lookup, plusTarget,
    Gen2.except_ok_bind, Gen2.except_pure]

theorem plus_ctx1 (N : Int) (wv : Nat) :
    ctxOpWidth2 (pEnv N wv) plusElems (.resize 17 (.ident "a")) (.resize 17 (.ident "b")) =
      some (max wv wv) := rfl

theorem plus_ctx2 (N : Int) (wv : Nat) :
    ctxOpWidth2 (pEnv N wv) plusElems
      (.binary (.m0 .add) (.resize 17 (.ident "a")) (.resize 17 (.ident "b")))
      (.resize 17 (.ident "cin")) = some (max (max wv wv) 1) := rfl

/-- A zero-extension marker around a declared signal lowers to `.resize` at the context. -/
theorem plus_res (N : Int) (wv : Nat) (n : String) (w : Nat)
    (hn : (pEnv N wv).widths.lookup n = some w) :
    fitExpr2 (pEnv N wv) plusElems (some (1 + wv)) (.resize 17 (.ident n)) =
      .resize (1 + wv) (.ident n) := by
  rw [fitExpr2_of_not_rigid _ rfl]
  simp [instExpr2, selfWidth2, hn, PExpr.ctxPropagates, PExpr.negGenvarWidened, PExpr.constLeaf]

/-- **The static process at symbolic `N`**: the assign at the context width `1 + wv`. -/
theorem plus_static (N : Int) (wv : Nat) :
    design.pdesign.processes.map (instProcess2 (pEnv N wv) plusElems) = [plusProc (1 + wv)] := by
  rw [plus_source]
  simp only [List.map_cons, List.map_nil, instProcess2, plus_lhs]
  rw [fitExpr2_binary, instExpr2_add _ _ _ (by rw [plus_ctx2]; simp <;> omega), fitExpr2_binary,
    instExpr2_add _ _ _ (by rw [plus_ctx1]; simp <;> omega), plus_res N wv "a" wv rfl,
    plus_res N wv "b" wv rfl, plus_res N wv "cin" 1 rfl]
  rfl

theorem plus_instantiate2 (N : Nat) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (design.pdesign.assemble2 (plusEnv N) (plusDecls (((N : Int) - 1).natAbs + 1))
        plusElems []) :=
  PDesign.instantiate2_of_ok rfl (plus_paramEnv N) (plus_decls N) (plus_elems N)
    (by rw [plus_generates]; exact expandList2_nil)

theorem plus_processes (N : Nat) :
    (design.pdesign.instantiateD2 [(N : Int)]).processes.toList =
      [plusProc (1 + (((N : Int) - 1).natAbs + 1))] := by
  rw [PDesign.instantiateD2_of_ok (plus_instantiate2 N), PDesign.assemble2_processes,
    plus_static, plus_others]
  simp

theorem plus_decls_inst (N : Nat) :
    (design.pdesign.instantiateD2 [(N : Int)]).decls.toList =
      plusDecls (((N : Int) - 1).natAbs + 1) := by
  rw [PDesign.instantiateD2_of_ok (plus_instantiate2 N), PDesign.assemble2_decls]

/-! ## 1d. The one-driver rule -/

/-- The one-driver rule: `cout` and `s` are distinct signals and neither is an input. -/
theorem plus_driversOk (W : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames [plusProc W] = true := by
  rfl

/-- `design.sem N` is the instantiated design (its one-driver guard passes). -/
theorem plus_sem_eq (N : Nat) : design.sem N = design.pdesign.instantiateD2 [(N : Int)] := by
  show design.pdesign.instantiateGD2 [(N : Int)] = _
  apply PDesign.instantiateGD2_of_driversOk
  rw [plus_processes]
  exact plus_driversOk _

/-- **The instantiated process list, for every `N ≥ 1`**: the one assign, at width `N + 1`. -/
theorem plus_sem_processes (N : Nat) (hN : 1 ≤ N) :
    (design.sem N).processes.toList = [plusProc (N + 1)] := by
  rw [plus_sem_eq, plus_processes]
  have h : 1 + (((N : Int) - 1).natAbs + 1) = N + 1 := by omega
  rw [h]

/-- **The instantiated declarations, for every `N ≥ 1`**. -/
theorem plus_sem_decls (N : Nat) (hN : 1 ≤ N) :
    (design.sem N).decls.toList = plusDecls N := by
  rw [plus_sem_eq, plus_decls_inst]
  have h : ((N : Int) - 1).natAbs + 1 = N := by omega
  rw [h]

/-! ## 2a. The process table and the declarations (`1 ≤ N`) -/

section Table

variable {N : Nat} (hN : 1 ≤ N)
include hN

theorem plus_proc {i : Nat} {p : Process2} :
    (design.sem N).processes[i]? = some p ↔ i = 0 ∧ p = plusProc (N + 1) := by
  rw [← Array.getElem?_toList, plus_sem_processes N hN]
  match i with
  | 0 => simp [eq_comm]
  | i + 1 => simp

theorem plus_proc0 : (design.sem N).processes[0]? = some (.assign plusTarget (plusRhs (N + 1))) :=
  (plus_proc hN).mpr ⟨rfl, rfl⟩

theorem plus_declWidth (n : String) :
    (design.sem N).declWidth n = ((plusDecls N).find? fun dc => dc.name == n).map Decl.width := by
  simp only [Design2.declWidth, plus_sem_decls N hN]

theorem plus_declWidth_s : (design.sem N).declWidth "s" = some N := by
  simp [plus_declWidth hN, plusDecls]

theorem plus_declWidth_cout : (design.sem N).declWidth "cout" = some 1 := by
  simp [plus_declWidth hN, plusDecls]

theorem plus_inputNames : (design.sem N).inputNames.toList = ["a", "b", "cin"] := by
  simp [Design2.inputNames, plus_sem_decls N hN, plusDecls]

/-- The target's windows, MSB-first: `cout` (1 bit), then `s` (`N` bits). -/
theorem plus_wins : plusTarget.wins (design.sem N) = [("cout", 0, 1), ("s", 0, N)] := by
  simp [plusTarget, plus_declWidth_s hN, plus_declWidth_cout hN]

theorem plus_writes {i : Nat} {wn : Win} :
    (design.sem N).Writes i wn ↔ i = 0 ∧ (wn = ("cout", 0, 1) ∨ wn = ("s", 0, N)) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    obtain ⟨rfl, h⟩ := (plus_proc hN).mp hp
    simp only [plusProc, Process2.assign.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [plus_wins hN] at hw
    simpa using hw
  · rintro ⟨rfl, h⟩
    exact ⟨_, _, plus_proc0 hN, by rw [plus_wins hN]; simpa using h⟩

theorem plus_driven {n : String} : Driven (design.sem N) n ↔ n = "cout" ∨ n = "s" := by
  constructor
  · rintro ⟨i, lo, w, h⟩
    rcases ((plus_writes hN).mp h).2 with h | h <;> simp only [Prod.mk.injEq] at h <;> simp [h.1]
  · rintro (rfl | rfl)
    · exact ⟨0, 0, 1, (plus_writes hN).mpr ⟨rfl, Or.inl rfl⟩⟩
    · exact ⟨0, 0, N, (plus_writes hN).mpr ⟨rfl, Or.inr rfl⟩⟩

end Table

/-! ## 2b. The comb profile and acyclicity -/

/-- **The comb profile** (every `N ≥ 1`): one assign whose concatenated target has two
disjoint in-range windows on non-input signals. -/
theorem plus_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (design.sem N) where
  nodup := by
    rw [plus_sem_decls N hN]
    simp only [plusDecls, List.map_cons, List.map_nil]
    decide
  assign := by
    intro i p hp
    obtain ⟨rfl, rfl⟩ := (plus_proc hN).mp hp
    exact ⟨_, _, [("cout", 0, 1), ("s", 0, N)], rfl,
      by simp [plusTarget, plus_declWidth_s hN, plus_declWidth_cout hN]⟩
  inWidth := by
    intro i n lo w h
    rcases ((plus_writes hN).mp h).2 with h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h
    · exact ⟨_, plus_declWidth_cout hN, by omega⟩
    · exact ⟨_, plus_declWidth_s hN, by omega⟩
  notInput := by
    intro n hn
    rw [plus_inputNames hN]
    rcases (plus_driven hN).mp hn with rfl | rfl <;> decide
  disjoint := by
    intro i j wi wj hij hi hj
    exact absurd (((plus_writes hN).mp hi).1.trans ((plus_writes hN).mp hj).1.symm) hij
  selfDisjoint := by
    intro i t e hp
    obtain ⟨-, h⟩ := (plus_proc hN).mp hp
    simp only [plusProc, Process2.assign.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rw [plus_wins hN]
    simp [Win.overlaps]
  rhsFree := by
    intro i t e hp
    obtain ⟨-, h⟩ := (plus_proc hN).mp hp
    simp only [plusProc, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  rhsDeclared := by
    intro i t e hp
    obtain ⟨-, h⟩ := (plus_proc hN).mp hp
    simp only [plusProc, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [plus_sem_decls N hN]
    simp [Expr2.idents, plusRhs, plusDecls]
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [plus_sem_decls N hN] at hdc
    simp [plusDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [plus_sem_decls N hN] at hdc
    simp [plusDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The one process reads only the inputs, which nothing writes (any rank works). -/
theorem plus_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (design.sem N) := by
  refine ⟨fun _ => 0, ?_⟩
  intro i j ti ei tj ej wj hi hj hw hex
  exfalso
  obtain ⟨-, h⟩ := (plus_proc hN).mp hi
  simp only [plusProc, Process2.assign.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hWj := ((plus_writes hN).mp ⟨tj, ej, hj, hw⟩).2
  obtain ⟨r, hr, hov⟩ := hex
  simp only [plusRhs, Expr2.reads, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rcases hWj with rfl | rfl <;>
    simp [ReadWin.overlaps] at hov

/-! ## 3a. `BitVec` arithmetic: the `N + 1`-bit sum read as `{carry, sum}`

The same three lemmas as `cadd_toNat`, `cadd_low` and `cadd_carry` of the library file
`LeanModels/Sv/Comb2ConcatExample.lean`, restated here because that module is not among the
built modules a solution can import. -/

/-- The `N + 1`-bit sum of the zero-extended operands does not wrap. -/
theorem sum1_toNat {N : Nat} (x y : BitVec N) (ci : Bool) :
    (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool ci).setWidth (N + 1)).toNat =
      x.toNat + y.toNat + ci.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hc : ci.toNat ≤ 1 := Bool.toNat_le ci
  have h1 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, Nat.pow_succ]
  generalize 2 ^ N = M at *
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + y.toNat) (by omega),
    Nat.mod_eq_of_lt (a := ci.toNat) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The low `N` bits of the `N + 1`-bit sum are the `N`-bit sum. -/
theorem sum1_low {N : Nat} (x y : BitVec N) (ci : Bool) :
    (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool ci).setWidth (N + 1)).extractLsb' 0 N =
      x + y + (BitVec.ofBool ci).setWidth N := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, sum1_toNat, Nat.shiftRight_zero]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  rw [Nat.mod_add_mod, Nat.add_mod_mod]

/-- The top bit of the `N + 1`-bit sum is the carry out `2^N ≤ x + y + ci`. -/
theorem sum1_carry {N : Nat} (x y : BitVec N) (ci : Bool) :
    (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool ci).setWidth (N + 1)).getLsbD N =
      decide (2 ^ N ≤ x.toNat + y.toNat + ci.toNat) := by
  rw [← BitVec.testBit_toNat, sum1_toNat, Nat.testBit_eq_decide_div_mod_eq]
  have hx := x.isLt
  have hy := y.isLt
  have hc : ci.toNat ≤ 1 := Bool.toNat_le ci
  have hpos : 0 < 2 ^ N := Nat.two_pow_pos N
  have hn : x.toNat + y.toNat + ci.toNat < 2 * 2 ^ N := by omega
  generalize x.toNat + y.toNat + ci.toNat = n at *
  have hq : n / 2 ^ N < 2 := (Nat.div_lt_iff_lt_mul hpos).mpr hn
  have hle : 1 ≤ n / 2 ^ N ↔ 1 * 2 ^ N ≤ n := Nat.le_div_iff_mul_le hpos
  rw [Nat.one_mul] at hle
  generalize n / 2 ^ N = q at *
  rw [decide_eq_decide]
  obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
  · exact ⟨fun h => absurd h (by decide), fun h => absurd (hle.mpr h) (by decide)⟩
  · exact ⟨fun _ => hle.mp (Nat.le_refl 1), fun _ => rfl⟩

/-! ## 3b. The settled state -/

/-- **One settled state**: in any state that solves the design's equations and has the comb
shape, known inputs `x y : BitVec N`, `ci : Bool` on `a b cin` give `x + y + ci` (mod `2^N`)
on `s` and the carry out `2^N ≤ x + y + ci` on `cout`. -/
theorem plus_settled {N : Nat} (hN : 1 ≤ N) {st : SvState}
    (heqs : CombEqs (design.sem N) st) (hs : StateShape (design.sem N) st)
    {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
      SvState.lookup st "cout" =
        some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  have hv : evalPure2 st (plusRhs (N + 1)) = .ok (LVec.ofBitVec
      (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool ci).setWidth (N + 1))) := by
    sv2_known [plusRhs, ha, hb, hc]
  have htot : Win.sumWidth (plusTarget.wins (design.sem N)) = N + 1 := by
    rw [plus_wins hN]; simp; omega
  have hS := CombEqs.concat_part_ident (plus_comb N hN) heqs hs (plus_proc0 hN) hv
    (n := "s") (w := N) (off := 0) (by rw [plus_wins hN]; simp) (plus_declWidth_s hN)
  have hCO := CombEqs.concat_part_ident (plus_comb N hN) heqs hs (plus_proc0 hN) hv
    (n := "cout") (w := 1) (off := N) (by rw [plus_wins hN]; simp) (plus_declWidth_cout hN)
  rw [htot, LVec.resizeU_ofBitVec, BitVec.setWidth_eq] at hS hCO
  rw [LVec.extract_ofBitVec _ (by omega), sum1_low] at hS
  rw [LVec.extract_one_ofBitVec _ (by omega), sum1_carry] at hCO
  exact ⟨hS, hCO⟩

/-! ## 4. From the settled state to the task's function -/

/-- A 1-bit vector is the `ofBool` of its only bit. -/
theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-- The sum is the task's `s`: `(x + y + ci) mod 2^N`. -/
theorem sum_eq_ofNat {N : Nat} (hN : 1 ≤ N) (x y : BitVec N) (ci : Bool) :
    x + y + (BitVec.ofBool ci).setWidth N =
      BitVec.ofNat N (x.toNat + y.toNat + (BitVec.ofBool ci).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
  have hc : ci.toNat < 2 ^ N := by have := Bool.toNat_le ci; omega
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hc, Nat.mod_add_mod]

/-- The carry out is the task's `cout`: `t / 2^N`, for any `t < 2 · 2^N`. -/
theorem carry_eq_ofNat {N : Nat} (t : Nat) (ht : t < 2 * 2 ^ N) :
    BitVec.ofBool (decide (2 ^ N ≤ t)) = BitVec.ofNat 1 (t / 2 ^ N) := by
  by_cases h : 2 ^ N ≤ t
  · have hq : t / 2 ^ N = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [h, hq]
  · have hq : t / 2 ^ N = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, hq]

/-- The interface: inputs `a b : N`, `cin : 1`; outputs `s : N`, `cout : 1`. -/
theorem add_interface (N : Nat) (hN : 1 ≤ N) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  simp [CombTask.Interface, inputPorts, outputPorts, plus_sem_decls N hN, plusDecls,
    SvGolf.Tasks.Add.task]

/-- **The `add` statement for `plus.sv`**, for every `N` in the task's range. -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  refine CombTask.satisfiedAt_of_comb (add_interface N hN') (plus_comb N hN')
    (plus_acyclic N hN') ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨ha, hb, hc⟩ := hv
  obtain ⟨hs', hco⟩ := plus_settled hN' heqs hs ha hb hc
  have ht : x.toNat + y.toNat + c0.toNat < 2 * 2 ^ N := by
    have : x.toNat < 2 ^ N := x.isLt
    have : y.toNat < 2 ^ N := y.isLt
    have := Bool.toNat_le c0
    have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN'
    omega
  refine ⟨?_, ?_⟩
  · rw [hs', sum_eq_ofNat hN']
  · rw [hco, carry_eq_ofNat _ ht, BitVec.toNat_ofBool]

/-! ## Axiom pin: standard axioms only (no `sorry`, no `native_decide`, no `bv_decide`). -/

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission

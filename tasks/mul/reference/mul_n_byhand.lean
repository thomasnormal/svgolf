import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.Known2

/-!
# Reference solution for task `mul` (N-bit unsigned multiplier): the proof

A submission file like any player's `Solution.lean`: the checker generates
`Submission.Design` (the envelope of `reference/mul_n.sv` loaded as
`Submission.design`, and `Submission.Goal :=
SvGolf.Tasks.Mul.Statement design.sem`), and this file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N ≥ 1`. Nothing is unrolled at a fixed width, nothing is
bit-blasted, no `decide` runs on input-dependent data: `N`, the inputs and
every index stay symbolic from the envelope to the conclusion. Axioms:
`propext`, `Classical.choice`, `Quot.sound`.

## The design

`reference/mul_n.sv` is an array multiplier: partial products
`pp[i][j] = a[j] & b[i]`; row 0 of the row sums is `s[0] = {1'b0, pp[0]}`;
row `i` (`1 ≤ i < N`) is an `N`-bit ripple-carry adder of full adders,
`s[i] = s[i-1][N:1] + pp[i]` (`t` the propagates, `c` the carries, carry-in
`0`, `s[i][N]` the carry-out); the output takes bit 0 of every row and the
upper `N` bits of the last row.

## The proof, in four parts

0. **Arithmetic** (`MulMath`, pure `Nat`): the row sums
   `R 0 = x·y₀`, `R (i+1) = R i / 2 + x·y_{i+1}`; the row invariant
   `x * (y mod 2^(i+1)) = 2^i * R i + L` with `L < 2^i` (`R_inv`); hence bit
   `k < N` of `x * y` is bit 0 of row `k` (`testBit_mul_row`) and bit `N + j`
   is bit `j + 1` of row `N - 1` (`testBit_mul_top`).
1. **The design at symbolic `N`** (adapted from
   `Examples/system-verilog/mul2d/gen.lean`): the generate loops expand, for
   every `N ≥ 1`, to the flat 1-bit cells of `mulProcs N`
   (`mul_sem_processes`), over the declarations `mulDecls N`
   (`mul_sem_decls`); the one-driver guard of `design.sem` passes
   (`mul_driversOk`).
2. **Comb profile and acyclicity** (`mul_comb`, `mul_acyclic`): every
   process is a 1-bit (or row-wide) slice assign; disjointness of the write
   windows comes from the one-driver rule (`mulProcs_pairwise`); the rank
   certificate is the row-major order of the adder array (`rkWin`), checked
   reader by reader (`mul_reader`) with `omega` over the row-major offsets.
3. **The settled state** (`mul_settled`): in any state solving the design's
   equations, by induction on the row, row `i`'s window of `s` holds
   `R i` bit by bit; inside a row, by induction on the bit, the carries are
   core's `BitVec.carry` of the row's two addends (`BitVec.carry_succ`) and
   the sums are `BitVec.getLsbD_add`. The output bits then follow from
   part 0, and `CombTask.satisfiedAt_of_comb` (`SvGolf/Comb.lean`) turns it
   into the statement (`solution`).
-/

/-! # Part 0. The row-sum arithmetic (pure `Nat`) -/

namespace Submission.MulMath

/-- Row `i`'s addend: `x` when bit `i` of `y` is set, else `0`. -/
def addend (x y i : Nat) : Nat := if y.testBit i then x else 0

/-- The row sums of the array multiplier: row 0 is the first addend; row
`i + 1` adds the upper bits of row `i` (`/ 2`) to addend `i + 1`. -/
def R (x y : Nat) : Nat → Nat
  | 0 => addend x y 0
  | i + 1 => R x y i / 2 + addend x y (i + 1)

theorem addend_le (x y i : Nat) : addend x y i ≤ x := by
  unfold addend; split <;> omega

theorem R_le (x y : Nat) : ∀ i, R x y i ≤ 2 * x
  | 0 => by simp only [R]; have := addend_le x y 0; omega
  | i + 1 => by
      simp only [R]; have := R_le x y i; have := addend_le x y (i + 1); omega

theorem addend_eq (x y i : Nat) : addend x y i = x * (y / 2 ^ i % 2) := by
  unfold addend
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have : y / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : y / 2 ^ i % 2 = 1
  · simp [h]
  · have h0 : y / 2 ^ i % 2 = 0 := by omega
    simp [h0]

/-- **The row invariant**: the rows so far hold `x * (y mod 2^(i+1))`, with
`i` low bits `L` already emitted. -/
theorem R_inv (x y : Nat) : ∀ i, ∃ L, L < 2 ^ i ∧ x * (y % 2 ^ (i + 1)) = 2 ^ i * R x y i + L
  | 0 => ⟨0, by decide, by
      simp only [R, addend_eq, Nat.pow_zero, Nat.div_one, Nat.one_mul, Nat.add_zero, Nat.zero_add,
        Nat.pow_one]⟩
  | i + 1 => by
      obtain ⟨L, hL, h⟩ := R_inv x y i
      refine ⟨2 ^ i * (R x y i % 2) + L, ?_, ?_⟩
      · have : R x y i % 2 ≤ 1 := by omega
        have : 2 ^ i * (R x y i % 2) ≤ 2 ^ i * 1 := Nat.mul_le_mul_left _ this
        rw [Nat.pow_succ]; omega
      · rw [Nat.mod_pow_succ, Nat.mul_add, h, R, addend_eq]
        have hR := Nat.div_add_mod (R x y i) 2
        generalize R x y i / 2 = q at hR ⊢
        generalize R x y i % 2 = r at hR ⊢
        rw [← hR, Nat.pow_succ]
        grind

/-- Bit `k` of the product is bit 0 of row `k`. -/
theorem testBit_mul_row (x y k : Nat) : (x * y).testBit k = (R x y k).testBit 0 := by
  obtain ⟨L, hL, h⟩ := R_inv x y k
  have hsplit : x * y = x * (y % 2 ^ (k + 1)) + 2 ^ (k + 1) * (x * (y / 2 ^ (k + 1))) := by
    rw [Nat.mul_left_comm, ← Nat.mul_add, Nat.mod_add_div]
  have hmod : (x * y) % 2 ^ (k + 1) = (x * (y % 2 ^ (k + 1))) % 2 ^ (k + 1) := by
    rw [hsplit, Nat.add_mul_mod_self_left]
  have h1 : (x * y).testBit k = ((x * y) % 2 ^ (k + 1)).testBit k := by
    rw [Nat.testBit_mod_two_pow]; simp
  rw [h1, hmod, Nat.testBit_mod_two_pow, h, Nat.testBit_two_pow_mul_add _ hL]
  simp

/-- Bit `N + j` of the product of `N`-bit numbers is bit `j + 1` of the last
row `N - 1`. -/
theorem testBit_mul_top (x y N j : Nat) (hN : 1 ≤ N) (hy : y < 2 ^ N) :
    (x * y).testBit (N + j) = (R x y (N - 1)).testBit (j + 1) := by
  obtain ⟨L, hL, h⟩ := R_inv x y (N - 1)
  have hN' : N - 1 + 1 = N := by omega
  rw [hN', Nat.mod_eq_of_lt hy] at h
  rw [h, Nat.testBit_two_pow_mul_add _ hL]
  rw [if_neg (by omega)]
  congr 1
  omega

/-- A number below `2^(N+1)` has bit `N` iff it is at least `2^N`. -/
theorem testBit_top (n N : Nat) (h : n < 2 ^ (N + 1)) : n.testBit N = decide (2 ^ N ≤ n) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hlt : n / 2 ^ N < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos N)]
    rw [Nat.pow_succ] at h; omega
  have hm : n / 2 ^ N % 2 = n / 2 ^ N := Nat.mod_eq_of_lt hlt
  rw [hm]
  by_cases h2 : 2 ^ N ≤ n
  · have : 1 ≤ n / 2 ^ N := (Nat.le_div_iff_mul_le (Nat.two_pow_pos N)).mpr (by omega)
    simp [h2]; omega
  · have : n / 2 ^ N = 0 := Nat.div_eq_of_lt (by omega)
    simp [h2, this]

end Submission.MulMath

namespace Submission

open LeanModels.Sv SvGolf

/-! # Part 1. The design at symbolic `N`

Adapted from `Examples/system-verilog/mul2d/gen.lean` (svGolf does not import
`Examples`): the envelope's templates pinned by `rfl`, and the whole
instantiated process list for every `N ≥ 1`. -/

/-! ## The envelope's shape (pinned by `rfl`) -/

/-- The symbolic bound `N-1`. -/
def nM1 : PExpr := .binary (.m0 .sub) (.paramRef "N" none) (.int 1)

/-- The partial-product template `assign pp[i][j] = a[j] & b[i];` — the
target is ONE select path over `pp` with the genvar labels `[i, j]`. -/
def ppT : PProcess :=
  .assignL (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"])
    (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "j"))
      (.bitSel (.ident "b") (.genvarRef "i")))

/-- The partial-product generate block: `for (i …) for (j …) <ppT>`. -/
def ppGen : GenItem :=
  .genFor (some "g_pp") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 16)
    [.genFor (some "g_pp_j") "j" (.int 0) (.binary .slt (.genvarRef "j") (.paramRef "N" none))
      (.unary .inc (.genvarRef "j")) (some 16) ([ppT].map GenItem.process)]

/-- `pp`'s declared dimensions `[N-1:0][N-1:0]`, symbolic. -/
def ppDims : List PDim := [⟨nM1, .int 0⟩, ⟨nM1, .int 0⟩]

/-- … evaluated at `N`: the geometry-table entry (`(msb, lsb)` labels). -/
def ppGeom (N : Nat) : List (Int × Int) := [((N : Int) - 1, 0), ((N : Int) - 1, 0)]

/-- The first generate item of the envelope is the partial-product block. -/
theorem mul_pp_source : design.pdesign.generates.head? = some ppGen := rfl

/-- The source of the geometry table records `pp` as `[N-1:0][N-1:0]`. -/
theorem mul_pp_dims : design.pdesign.packedDims.lookup "pp" = some ppDims := rfl

/-! ## The instantiated cell -/

/-- Cell `(i, j)`: `pp[i*N + j] = a[j] & b[i]` on the flat `N*N`-bit vector. -/
def ppCell (N i j : Nat) : Process2 :=
  .assign (.slice "pp" (i * N + j) 1)
    (.binary .and (.slice (.ident "a") j 1) (.slice (.ident "b") i 1))

/-- The nested select `pp[i][j]` over `[N-1:0][N-1:0]` with in-range genvar
labels is the 1-bit window at `i*N + j`. -/
theorem pp_window (E : IEnv) (N i j : Nat) (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (hiv : E.vals.lookup "i" = some (i : Int))
    (hjv : E.vals.lookup "j" = some (j : Int)) (hd : E.dims.lookup "pp" = some (ppGeom N)) :
    arrayElemWindow E "pp" [.genvarRef "i", .genvarRef "j"] =
      .ok (((i * N + j : Nat) : Int), 1, true) := by
  have hm0 : (0 : Int) ≤ (N : Int) - 1 := by omega
  have hdims := arrayDims_of hd
  have hwj := walkIndices_desc0_cons (ds := []) hm0 (evalInt_genvarRef_of hjv)
    (by omega) (by omega) (walkIndices_nil (env := E) [])
  have hwi := walkIndices_desc0_cons hm0 (evalInt_genvarRef_of hiv) (by omega) (by omega) hwj
  rw [arrayElemWindow_of hdims hwi]
  have hc : dimsStride [((N : Int) - 1, 0)] = N := by
    simp only [dimsStride, dimCount]
    omega
  simp [hc]

/-- **The partial-product template at in-range genvars** (any environment
binding `N`, `pp`'s dimensions, and 1-bit element widths for `a`, `b`). -/
theorem pp_inst (env : IEnv) (elems : List (String × Nat)) (N i j : Nat) (hN : 1 ≤ N)
    (hi : i < N) (hj : j < N) (hd : env.dims.lookup "pp" = some (ppGeom N))
    (ha : elems.lookup "a" = some 1) (hb : elems.lookup "b" = some 1) :
    instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems ppT = ppCell N i j := by
  have hw := pp_window ((env.bindVal "i" i).bindVal "j" j) N i j hN hi hj
    (by simp [IEnv.bindVal, List.lookup])
    (by simp [IEnv.bindVal]) (by simpa using hd)
  have hiv : evalInt ((env.bindVal "i" i).bindVal "j" j) (.genvarRef "i") = .ok (i : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])
  have hjv : evalInt ((env.bindVal "i" i).bindVal "j" j) (.genvarRef "j") = .ok (j : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal])
  rw [ppT, instProcess2_assignL _ (by rw [instLhs2_arrayElem, arrayElemTarget_of_inRange hw]),
    fitExpr2_binary, instExpr2_and, fitExpr2_bitSel_ident ha hjv (by omega),
    fitExpr2_bitSel_ident hb hiv (by omega)]
  have hidx : ((i : Int) * (N : Int) + (j : Int)).toNat = i * N + j := by
    rw [← Int.natCast_mul, ← Int.natCast_add, Int.toNat_natCast]
  simp [ppCell, hidx]

/-- The loop bound `N` survives genvar bindings (genvars never shadow `N`). -/
private theorem n_bound (env : IEnv) (N : Nat) (h : env.vals.lookup "N" = some (N : Int))
    (g : String) (hg : g ≠ "N") (i : Int) :
    evalInt (env.bindVal g i) (.paramRef "N" none) = .ok (N : Int) := by
  apply evalInt_paramRef_of
  simp [IEnv.bindVal, List.lookup, h, beq_false_of_ne (Ne.symm hg)]

/-- … and `N` stays in the INT class there (`PExpr.isInt`: bound in `vals`). -/
private theorem n_bound_int (env : IEnv) (N : Nat) (h : env.vals.lookup "N" = some (N : Int))
    (g : String) (hg : g ≠ "N") (i : Int) :
    (PExpr.paramRef "N" none).isInt (env.bindVal g i) = true := by
  exact isInt_paramRef_of (v := (N : Int))
    (by simp [IEnv.bindVal, List.lookup, h, beq_false_of_ne (Ne.symm hg)])

/-- **The partial-product generate block, for every `N ≥ 1`**: the
`i`-major family of 1-bit cells `pp[i*N + j] = a[j] & b[i]`. -/
theorem mul_pp_expand (env : IEnv) (elems : List (String × Nat)) (N F : Nat) (hN : 1 ≤ N)
    (hF : N < F) (hNv : env.vals.lookup "N" = some (N : Int))
    (hd : env.dims.lookup "pp" = some (ppGeom N))
    (ha : elems.lookup "a" = some 1) (hb : elems.lookup "b" = some 1) :
    ppGen.expand2 env elems F =
      .ok ((List.range N).flatMap fun i => (List.range N).map fun j => ppCell N i j) := by
  rw [ppGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [ppT].map (instProcess2 ((env.bindVal "i" v).bindVal "j" w) elems))
      (evalInt_int 0) (n_bound_int env N hNv "i" (by decide)) (n_bound env N hNv "i" (by decide)) (by simpa using hF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast, List.map_cons,
      List.map_nil, Gen2.flatMap_singleton_map]
    congr 1
    simp only [List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro i hi
    apply List.map_congr_left
    intro j hj
    exact pp_inst env elems N i j hN (List.mem_range.mp hi) (List.mem_range.mp hj) hd ha hb
  · intro v _ _
    apply expandList2_singleton_ok
    rw [GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (n_bound_int _ N (by simp [IEnv.bindVal, List.lookup, hNv]) "j" (by decide))
      (n_bound _ N (by simp [IEnv.bindVal, List.lookup, hNv]) "j" (by decide)) (by simpa using hF)]
    simp

/-! ## At the environment `instantiate2` builds -/

/-- The declaration scope of `mul_n` at `N`: `N` bound, its declared `int`
type 32 bits. -/
def mulScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

/-- The parameter environment of `mul_n` at `N` (by `rfl`): the declaration
scope plus the geometry table evaluated in it. -/
def mulEnv (N : Int) : IEnv := { mulScope N with dims := dimTable (mulScope N) design.pdesign.decls }

theorem mul_paramEnv (N : Int) : design.pdesign.paramEnv2 [N] = .ok (mulEnv N) := rfl

/-- `N - 1` in the declaration scope, at any declared-width table. -/
theorem mulScope_nM1 (N : Int) (ws : List (String × Nat)) :
    evalInt { mulScope N with widths := ws } nM1 = .ok (N - 1) :=
  evalInt_sub_of (by simp [mulScope]) rfl (evalInt_paramRef_of (by simp [mulScope])) (evalInt_int 1)

/-- The geometry table's `pp` entry: `[N-1:0][N-1:0]` evaluated. -/
theorem mulEnv_pp (N : Nat) : (mulEnv N).dims.lookup "pp" = some (ppGeom N) :=
  PDesign.dimTable_lookup_of mul_pp_dims fun ws =>
    evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0)
      (evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0) evalDims_nil)

/-- **The partial-product block of the instantiated multiplier, for every
`N ≥ 1`** — at the declaration environment of ANY declaration list and any
element-width table giving the 1-D ports `a`, `b` 1-bit elements (what
`buildElems` computes for them), at the surface fuel. -/
theorem mul_pp_instantiated (N : Nat) (hN : 1 ≤ N) (decls : List Decl)
    (elems : List (String × Nat)) (ha : elems.lookup "a" = some 1)
    (hb : elems.lookup "b" = some 1) :
    ppGen.expand2 ((mulEnv N).withDecls decls) elems (PDesign.surfaceFuel [(N : Int)]) =
      .ok ((List.range N).flatMap fun i => (List.range N).map fun j => ppCell N i j) :=
  mul_pp_expand _ elems N _ hN
    (by
      have := Nat.le_mul_self (N + 2)
      simp [PDesign.surfaceFuel]
      omega)
    (by simp [mulEnv, mulScope]) (by simpa using mulEnv_pp N) ha hb

/-! ## The whole instantiated multiplier

The same route over the remaining templates — the four static assigns, the
row block (`c[i][0]`, then `t/s/c` per bit, then `s[i][N]`) and the output
block — gives the complete process list for every `N ≥ 1`
(`mul_processes`). Reads of `s[i-1][j+1]` (the previous row's sum,
shifted one bit) are windows of the `[N-1:0][N:0]` array at
`(i-1)*(N+1) + (j+1)`; the label arithmetic is discharged once per
template by `win_sq`/`win_rect`. -/

/-- `t`, `pp`: `[N-1:0][N-1:0]`; `s`, `c`: `[N-1:0][N:0]`. -/
def rectDims : List PDim := [⟨nM1, .int 0⟩, ⟨.paramRef "N" none, .int 0⟩]

theorem mul_t_dims : design.pdesign.packedDims.lookup "t" = some ppDims := rfl
theorem mul_s_dims : design.pdesign.packedDims.lookup "s" = some rectDims := rfl
theorem mul_c_dims : design.pdesign.packedDims.lookup "c" = some rectDims := rfl

/-- `[N-1:0][N:0]` evaluated at `N`. -/
def rectGeom (N : Nat) : List (Int × Int) := [((N : Int) - 1, 0), ((N : Int), 0)]

/-- The geometry table's `t`/`s`/`c` entries. -/
theorem mulEnv_t (N : Nat) : (mulEnv N).dims.lookup "t" = some (ppGeom N) :=
  PDesign.dimTable_lookup_of mul_t_dims fun ws =>
    evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0)
      (evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0) evalDims_nil)

private theorem rect_eval (N : Nat) (ws : List (String × Nat)) :
    evalDims { mulScope N with widths := ws } rectDims = .ok (rectGeom N) :=
  evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0)
    (evalDims_cons_of (d := ⟨.paramRef "N" none, .int 0⟩)
      (evalInt_paramRef_of (by simp [mulScope])) (evalInt_int 0) evalDims_nil)

theorem mulEnv_s (N : Nat) : (mulEnv N).dims.lookup "s" = some (rectGeom N) :=
  PDesign.dimTable_lookup_of mul_s_dims (rect_eval N)

theorem mulEnv_c (N : Nat) : (mulEnv N).dims.lookup "c" = some (rectGeom N) :=
  PDesign.dimTable_lookup_of mul_c_dims (rect_eval N)

/-- `2*N-1`, the msb label of `p`. -/
def pMsb : PExpr := .binary (.m0 .sub) (.binary .mul (.int 2) (.paramRef "N" none)) (.int 1)

/-- `p`: `[2*N-1:0]`. -/
theorem mul_p_dims : design.pdesign.packedDims.lookup "p" = some [⟨pMsb, .int 0⟩] := rfl

/-- `2*N-1` at `N`, in any environment binding `N`. -/
theorem evalInt_pMsb {E : IEnv} {N : Int} (hN : E.vals.lookup "N" = some N) :
    evalInt E pMsb = .ok (2 * N - 1) :=
  evalInt_sub_of (by simp [PExpr.isInt, SymBinOp.intArith, hN]) rfl
    (evalInt_mul_of rfl (by simp [PExpr.isInt, hN]) (evalInt_int 2) (evalInt_paramRef_of hN))
    (evalInt_int 1)

/-- The geometry table's `p` entry. -/
theorem mulEnv_p (N : Nat) : (mulEnv N).dims.lookup "p" = some [(2 * (N : Int) - 1, 0)] :=
  PDesign.dimTable_lookup_of mul_p_dims fun _ =>
    evalDims_cons_of (d := ⟨pMsb, .int 0⟩) (evalInt_pMsb (by simp [mulScope])) (evalInt_int 0)
      evalDims_nil

/-- The 1-bit literal `1'b0`. -/
def zero1 : LVec := LVec.ofNat 1 0

/-- `s[0] = {1'b0, pp[0]}`. -/
def s0T : PProcess :=
  .assignL (.arrayElem "s" [.int 0]) (.concat [.lit zero1, .arrayElem "pp" [.int 0]])
/-- `c[0] = '0`. -/
def c0T : PProcess := .assignL (.arrayElem "c" [.int 0]) (.fill .l0)
/-- `t[0] = '0`. -/
def t0T : PProcess := .assignL (.arrayElem "t" [.int 0]) (.fill .l0)
/-- `p[2*N-1:N] = s[N-1][N:1]` — a row part-select read. Both selects have
static labels over parameter-dependent ranges, so both are `ArraySel` paths
(labels normalized against the declared range at every point). -/
def pHiT : PProcess :=
  .assignL (.arrayPart "p" [] .range pMsb (.paramRef "N" none))
    (.arrayPart "s" [nM1] .range (.paramRef "N" none) (.int 1))

theorem mul_static_source : design.pdesign.processes = [s0T, c0T, t0T, pHiT] := rfl

/-- `c[i][0] = 1'b0`. -/
def cRowT : PProcess := .assignL (.arrayElem "c" [.genvarRef "i", .int 0]) (.lit zero1)
/-- `t[i][j] = s[i-1][j+1] ^ pp[i][j]`. -/
def tT : PProcess :=
  .assignL (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])
    (.binary (.m0 .xor)
      (.arrayElem "s" [.binary (.m0 .sub) (.genvarRef "i") (.int 1),
        .binary (.m0 .add) (.genvarRef "j") (.int 1)])
      (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]))
/-- `s[i][j] = t[i][j] ^ c[i][j]`. -/
def sT : PProcess :=
  .assignL (.arrayElem "s" [.genvarRef "i", .genvarRef "j"])
    (.binary (.m0 .xor) (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])
      (.arrayElem "c" [.genvarRef "i", .genvarRef "j"]))
/-- `c[i][j+1] = (s[i-1][j+1] & pp[i][j]) | (c[i][j] & t[i][j])`. -/
def cT : PProcess :=
  .assignL (.arrayElem "c" [.genvarRef "i", .binary (.m0 .add) (.genvarRef "j") (.int 1)])
    (.binary (.m0 .or)
      (.binary (.m0 .and)
        (.arrayElem "s" [.binary (.m0 .sub) (.genvarRef "i") (.int 1),
          .binary (.m0 .add) (.genvarRef "j") (.int 1)])
        (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]))
      (.binary (.m0 .and) (.arrayElem "c" [.genvarRef "i", .genvarRef "j"])
        (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])))
/-- `s[i][N] = c[i][N]`. -/
def sTopT : PProcess :=
  .assignL (.arrayElem "s" [.genvarRef "i", .paramRef "N" none])
    (.arrayElem "c" [.genvarRef "i", .paramRef "N" none])

/-- The row block: `for (i = 1; i < N; i++) { c[i][0]; for (j …) {t; s; c}; s[i][N] }`. -/
def rowGen : GenItem :=
  .genFor (some "g_row") "i" (.int 1) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 15)
    [.process cRowT,
     .genFor (some "g_bit") "j" (.int 0) (.binary .slt (.genvarRef "j") (.paramRef "N" none))
       (.unary .inc (.genvarRef "j")) (some 16) ([tT, sT, cT].map GenItem.process),
     .process sTopT]

/-- `p[i] = s[i][0]`. -/
def outT : PProcess := .assignL (.bitSel "p" (.genvarRef "i")) (.arrayElem "s" [.genvarRef "i", .int 0])

/-- The output block `for (i = 0; i < N; i++) p[i] = s[i][0];`. -/
def outGen : GenItem :=
  .genFor (some "g_out") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 16) ([outT].map GenItem.process)

theorem mul_generates : design.pdesign.generates = [ppGen, rowGen, outGen] := rfl

/-! ### The instantiated vocabulary -/

def s0Proc (N : Nat) : Process2 :=
  .assign (.slice "s" 0 (N + 1)) (.concat #[.lit zero1, .slice (.ident "pp") 0 N])
def c0Proc (N : Nat) : Process2 := .assign (.slice "c" 0 (N + 1)) (.lit (LVec.replicate (N + 1) .l0))
def t0Proc (N : Nat) : Process2 := .assign (.slice "t" 0 N) (.lit (LVec.replicate N .l0))
/-- `p[2N-1:N] = s[N-1][N:1]`: the row part-select starts at bit
`(N-1)*(N+1) + 1 = N*N` of the flat `s`. -/
def pHiProc (N : Nat) : Process2 :=
  .assign (.slice "p" N N) (.slice (.ident "s") (N * N) N)

def cRowCell (N i : Nat) : Process2 := .assign (.slice "c" (i * (N + 1)) 1) (.lit zero1)
def tCell (N i j : Nat) : Process2 :=
  .assign (.slice "t" (i * N + j) 1)
    (.binary .xor (.slice (.ident "s") ((i - 1) * (N + 1) + (j + 1)) 1)
      (.slice (.ident "pp") (i * N + j) 1))
def sCell (N i j : Nat) : Process2 :=
  .assign (.slice "s" (i * (N + 1) + j) 1)
    (.binary .xor (.slice (.ident "t") (i * N + j) 1) (.slice (.ident "c") (i * (N + 1) + j) 1))
def cCell (N i j : Nat) : Process2 :=
  .assign (.slice "c" (i * (N + 1) + (j + 1)) 1)
    (.binary .or
      (.binary .and (.slice (.ident "s") ((i - 1) * (N + 1) + (j + 1)) 1)
        (.slice (.ident "pp") (i * N + j) 1))
      (.binary .and (.slice (.ident "c") (i * (N + 1) + j) 1) (.slice (.ident "t") (i * N + j) 1)))
def sTopCell (N i : Nat) : Process2 :=
  .assign (.slice "s" (i * (N + 1) + N) 1) (.slice (.ident "c") (i * (N + 1) + N) 1)
def outCell (N i : Nat) : Process2 := .assign (.slice "p" i 1) (.slice (.ident "s") (i * (N + 1)) 1)

/-- Row `i` (`1 ≤ i < N`): its carry-in, the bit cells, its top sum bit. -/
def rowCells (N i : Nat) : List Process2 :=
  cRowCell N i :: ((List.range N).flatMap fun j => [tCell N i j, sCell N i j, cCell N i j])
    ++ [sTopCell N i]

/-- **The instantiated multiplier**: static assigns, the partial products,
rows `1 … N-1`, the low output bits. -/
def mulProcs (N : Nat) : List Process2 :=
  [s0Proc N, c0Proc N, t0Proc N, pHiProc N]
    ++ ((List.range N).flatMap fun i => (List.range N).map fun j => ppCell N i j)
    ++ ((List.range (N - 1)).flatMap fun k => rowCells N (k + 1))
    ++ (List.range N).map (outCell N)

/-! ### Windows of the 2-D arrays -/

/-- The environment facts every template reads: `N`, and the evaluated
geometry of the four arrays. -/
structure MulEnvOk (E : IEnv) (N : Nat) : Prop where
  n : E.vals.lookup "N" = some (N : Int)
  pp : E.dims.lookup "pp" = some (ppGeom N)
  t : E.dims.lookup "t" = some (ppGeom N)
  s : E.dims.lookup "s" = some (rectGeom N)
  c : E.dims.lookup "c" = some (rectGeom N)

theorem MulEnvOk.bind {E : IEnv} {N : Nat} (h : MulEnvOk E N) (g : String) (hg : g ≠ "N")
    (v : Int) : MulEnvOk (E.bindVal g v) N :=
  ⟨by simp [IEnv.bindVal, List.lookup, h.n, beq_false_of_ne (Ne.symm hg)],
   by simpa using h.pp, by simpa using h.t, by simpa using h.s, by simpa using h.c⟩

theorem MulEnvOk.nM1 {E : IEnv} {N : Nat} (h : MulEnvOk E N) :
    evalInt E nM1 = .ok ((N : Int) - 1) :=
  evalInt_sub_of (by simp [h.n]) rfl (evalInt_paramRef_of h.n) (evalInt_int 1)

/-- A path `x[i][j]` over `[N-1:0][N-1:0]` (`pp`, `t`). -/
theorem win_sq {E : IEnv} {N : Nat} {n : String} (hd : E.dims.lookup n = some (ppGeom N))
    (hN : 1 ≤ N) {ie je : PExpr} {i j : Nat}
    (hi : evalInt E ie = .ok (i : Int)) (hj : evalInt E je = .ok (j : Int)) (hiN : i < N)
    (hjN : j < N) :
    arrayElemWindow E n [ie, je] = .ok (((i * N + j : Nat) : Int), 1, true) := by
  rw [arrayElemWindow_desc0_2 hd
    (by omega) (by omega) hi (by omega) (by omega) hj (by omega) (by omega)]
  have : (i : Int) * ((N : Int) - 1 + 1) + (j : Int) = ((i * N + j : Nat) : Int) := by simp
  rw [this]

/-- A path `x[i][j]` over `[N-1:0][N:0]` (`s`, `c`). -/
theorem win_rect {E : IEnv} {N : Nat} {n : String} (hd : E.dims.lookup n = some (rectGeom N))
    (hN : 1 ≤ N) {ie je : PExpr} {i j : Nat}
    (hi : evalInt E ie = .ok (i : Int)) (hj : evalInt E je = .ok (j : Int)) (hiN : i < N)
    (hjN : j ≤ N) :
    arrayElemWindow E n [ie, je] = .ok (((i * (N + 1) + j : Nat) : Int), 1, true) := by
  rw [arrayElemWindow_desc0_2 hd
    (by omega) (by omega) hi (by omega) (by omega) hj (by omega) (by omega)]
  have : (i : Int) * ((N : Int) + 1) + (j : Int) = ((i * (N + 1) + j : Nat) : Int) := by simp
  rw [this]

/-- An in-range 1-bit path read in a 1-bit context: the flat `slice`. -/
theorem read1 {E : IEnv} {elems : List (String × Nat)} {n : String} {is : List PExpr} {k : Nat}
    (h : arrayElemWindow E n is = .ok ((k : Int), 1, true)) :
    fitExpr2 E elems (some 1) (.arrayElem n is) = .slice (.ident n) k 1 := by
  rw [fitExpr2_arrayElem_of h, arrayElemRead_of_inRange h, Int.toNat_natCast]

/-- An in-range 1-bit path target. -/
theorem target1 {E : IEnv} {elems : List (String × Nat)} {n : String} {is : List PExpr} {k : Nat}
    (h : arrayElemWindow E n is = .ok ((k : Int), 1, true)) :
    instLhs2 E elems (.arrayElem n is) = .ok (.slice n k 1, 1) := by
  rw [instLhs2_arrayElem, arrayElemTarget_of_inRange h, Int.toNat_natCast]

/-! ### The templates at in-range genvars -/

section cells

variable {env : IEnv} {elems : List (String × Nat)} {N : Nat}

private theorem gv_i (env : IEnv) (i j : Int) :
    evalInt ((env.bindVal "i" i).bindVal "j" j) (.genvarRef "i") = .ok i :=
  evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])

private theorem gv_j (env : IEnv) (i j : Int) :
    evalInt ((env.bindVal "i" i).bindVal "j" j) (.genvarRef "j") = .ok j :=
  evalInt_genvarRef_of (by simp [IEnv.bindVal])

private theorem gv_im1 (env : IEnv) (i : Nat) (j : Int) (hi : 1 ≤ i) :
    evalInt ((env.bindVal "i" i).bindVal "j" j) (.binary (.m0 .sub) (.genvarRef "i") (.int 1)) =
      .ok ((i - 1 : Nat) : Int) := by
  rw [evalInt_sub_of rfl rfl (gv_i env i j) (evalInt_int 1)]
  congr 1
  omega

private theorem gv_jp1 (env : IEnv) (i : Int) (j : Nat) :
    evalInt ((env.bindVal "i" i).bindVal "j" j) (.binary (.m0 .add) (.genvarRef "j") (.int 1)) =
      .ok ((j + 1 : Nat) : Int) := by
  rw [evalInt_add_of rfl rfl (gv_j env i j) (evalInt_int 1)]
  simp

theorem cRow_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i : Nat) (hi : i < N) :
    instProcess2 (env.bindVal "i" i) elems cRowT = cRowCell N i := by
  have hi' : evalInt (env.bindVal "i" i) (.genvarRef "i") = .ok (i : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal])
  have hw := win_rect (n := "c") (by simpa using h.c) hN hi'
    (evalInt_int 0) (j := 0) hi (by omega)
  have hz : zero1.width = 1 := LVec.width_ofNat 1 0
  rw [cRowT, instProcess2_assignL _ (target1 hw), fitExpr2_lit, if_pos hz]
  simp [cRowCell]

theorem t_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i j : Nat) (hi1 : 1 ≤ i) (hi : i < N)
    (hj : j < N) :
    instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems tT = tCell N i j := by
  have h' := (h.bind "i" (by decide) i).bind "j" (by decide) j
  have hwT := win_sq (n := "t") h'.t hN (gv_i env i j) (gv_j env i j) hi hj
  have hwS := win_rect (n := "s") h'.s hN (gv_im1 env i j hi1) (gv_jp1 env i j) (by omega)
    (by omega)
  have hwP := win_sq (n := "pp") h'.pp hN (gv_i env i j) (gv_j env i j) hi hj
  rw [tT, instProcess2_assignL _ (target1 hwT), fitExpr2_binary, instExpr2_xor, read1 hwS,
    read1 hwP]
  rfl

theorem s_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i j : Nat) (hi : i < N) (hj : j < N) :
    instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems sT = sCell N i j := by
  have h' := (h.bind "i" (by decide) i).bind "j" (by decide) j
  have hwS := win_rect (n := "s") h'.s hN (gv_i env i j) (gv_j env i j) hi (by omega)
  have hwT := win_sq (n := "t") h'.t hN (gv_i env i j) (gv_j env i j) hi hj
  have hwC := win_rect (n := "c") h'.c hN (gv_i env i j) (gv_j env i j) hi (by omega)
  rw [sT, instProcess2_assignL _ (target1 hwS), fitExpr2_binary, instExpr2_xor, read1 hwT,
    read1 hwC]
  rfl

theorem c_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i j : Nat) (hi1 : 1 ≤ i) (hi : i < N)
    (hj : j < N) :
    instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems cT = cCell N i j := by
  have h' := (h.bind "i" (by decide) i).bind "j" (by decide) j
  have hwC1 := win_rect (n := "c") h'.c hN (gv_i env i j) (gv_jp1 env i j) hi (by omega)
  have hwS := win_rect (n := "s") h'.s hN (gv_im1 env i j hi1) (gv_jp1 env i j) (by omega)
    (by omega)
  have hwP := win_sq (n := "pp") h'.pp hN (gv_i env i j) (gv_j env i j) hi hj
  have hwC := win_rect (n := "c") h'.c hN (gv_i env i j) (gv_j env i j) hi (by omega)
  have hwT := win_sq (n := "t") h'.t hN (gv_i env i j) (gv_j env i j) hi hj
  rw [cT, instProcess2_assignL _ (target1 hwC1), fitExpr2_binary, instExpr2_or, fitExpr2_binary,
    instExpr2_and, fitExpr2_binary, instExpr2_and, read1 hwS, read1 hwP, read1 hwC, read1 hwT]
  rfl

theorem sTop_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i : Nat) (hi : i < N) :
    instProcess2 (env.bindVal "i" i) elems sTopT = sTopCell N i := by
  have h' := h.bind "i" (by decide) i
  have hi' : evalInt (env.bindVal "i" i) (.genvarRef "i") = .ok (i : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal])
  have hwS := win_rect (n := "s") h'.s hN hi' (evalInt_paramRef_of h'.n) hi (Nat.le_refl N)
  have hwC := win_rect (n := "c") h'.c hN hi' (evalInt_paramRef_of h'.n) hi (Nat.le_refl N)
  rw [sTopT, instProcess2_assignL _ (target1 hwS), read1 hwC]
  rfl

theorem out_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (hp : elems.lookup "p" = some 1) (i : Nat)
    (hi : i < N) :
    instProcess2 (env.bindVal "i" i) elems outT = outCell N i := by
  have h' := h.bind "i" (by decide) i
  have hi' : evalInt (env.bindVal "i" i) (.genvarRef "i") = .ok (i : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal])
  have hwS := win_rect (n := "s") h'.s hN hi' (evalInt_int 0) (j := 0) hi (by omega)
  rw [outT, instProcess2_assignL _ (instLhs2_bitSel hp hi' (by omega)), read1 hwS]
  simp [outCell]

end cells

/-! ### The generate blocks -/

theorem mul_row_expand (env : IEnv) (elems : List (String × Nat)) (N F : Nat) (hN : 1 ≤ N)
    (hF : N < F) (h : MulEnvOk env N) :
    rowGen.expand2 env elems F =
      .ok ((List.range (N - 1)).flatMap fun k => rowCells N (k + 1)) := by
  rw [rowGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => rowCells N (v.toNat))
      (evalInt_int 1) (n_bound_int env N h.n "i" (by decide)) (n_bound env N h.n "i" (by decide)) (by omega)]
  · congr 1
    have hcnt : ((N : Int) - 1).toNat = N - 1 := by omega
    rw [hcnt, intRange_eq_map, List.flatMap_map]
    simp only [List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro k _
    show rowCells N (1 + (k : Int)).toNat = rowCells N (k + 1)
    congr 1
    omega
  · intro v hv1 hvN
    obtain ⟨i, rfl⟩ : ∃ i : Nat, v = (i : Int) := ⟨v.toNat, by omega⟩
    have hi1 : 1 ≤ i := by omega
    have hiN : i < N := by omega
    have hb := h.bind "i" (by decide) i
    have hinner : (GenItem.genFor (some "g_bit") "j" (.int 0)
        (.binary .slt (.genvarRef "j") (.paramRef "N" none)) (.unary .inc (.genvarRef "j")) (some 16)
        ([tT, sT, cT].map GenItem.process)).expand2 (env.bindVal "i" i) elems F =
        .ok ((List.range N).flatMap fun j => [tCell N i j, sCell N i j, cCell N i j]) := by
      rw [GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
          (f := fun w => [tCell N i w.toNat, sCell N i w.toNat, cCell N i w.toNat])
          (evalInt_int 0) (n_bound_int _ N hb.n "j" (by decide)) (n_bound _ N hb.n "j" (by decide)) (by omega)]
      · congr 1
        rw [intRange_zero, List.flatMap_map]
        simp
      · intro w hw0 hwN
        obtain ⟨j, rfl⟩ : ∃ j : Nat, w = (j : Int) := ⟨w.toNat, by omega⟩
        have hjN : j < N := by omega
        rw [expandList2_processes]
        simp only [List.map_cons, List.map_nil, Int.toNat_natCast]
        rw [t_inst h hN i j hi1 hiN hjN, s_inst h hN i j hiN hjN, c_inst h hN i j hi1 hiN hjN]
    rw [expandList2_cons_ok (GenItem.expand2_process _)
      (expandList2_cons_ok hinner (expandList2_singleton_ok (GenItem.expand2_process _)))]
    rw [cRow_inst h hN i hiN, sTop_inst h hN i hiN]
    simp [rowCells]

theorem mul_out_expand (env : IEnv) (elems : List (String × Nat)) (N F : Nat) (hN : 1 ≤ N)
    (hF : N < F) (h : MulEnvOk env N) (hp : elems.lookup "p" = some 1) :
    outGen.expand2 env elems F = .ok ((List.range N).map (outCell N)) := by
  rw [outGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => [outCell N v.toNat])
      (evalInt_int 0) (n_bound_int env N h.n "i" (by decide)) (n_bound env N h.n "i" (by decide)) (by simpa using hF)]
  · congr 1
    rw [intRange_zero, List.flatMap_map]
    simp only [Int.sub_zero, Int.toNat_natCast]
    exact Gen2.flatMap_singleton_map (outCell N) (List.range N)
  · intro v hv0 hvN
    obtain ⟨i, rfl⟩ : ∃ i : Nat, v = (i : Int) := ⟨v.toNat, by omega⟩
    rw [expandList2_processes]
    simp only [List.map_cons, List.map_nil, Int.toNat_natCast]
    rw [out_inst h hN hp i (by omega)]

/-! ### Assembling `instantiate2` -/

/-- Element widths (`buildElems`) for `N ≥ 1`. -/
def mulElems (N : Nat) : List (String × Nat) :=
  [("a", 1), ("b", 1), ("p", 1), ("pp", N), ("s", N + 1), ("c", N + 1), ("t", N)]

private theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem mul_elems (N : Nat) (hN : 1 ≤ N) :
    buildElems (mulEnv N) design.pdesign.decls = .ok (mulElems N) := by
  have hv : ((N : Int) - 1).natAbs + 1 = N := by omega
  simp [design.pdesign, buildElems, PType.width_packed_cons, PType.elemWidth, PDim.width,
    evalInt, mulEnv, mulScope, List.lookup, mulElems, Gen2.except_ok_bind, hv, List.foldlM_cons,
    except_pure]

theorem mulEnvOk (N : Nat) (decls : List Decl) : MulEnvOk ((mulEnv N).withDecls decls) N :=
  ⟨by simp [mulEnv, mulScope], by simpa using mulEnv_pp N, by simpa using mulEnv_t N,
   by simpa using mulEnv_s N, by simpa using mulEnv_c N⟩

/-- An unbased-unsized fill in a context of width `w`. -/
private theorem instExpr2_fill_ctx {env : IEnv} {elems : List (String × Nat)} {w : Nat}
    {b : Logic} : instExpr2 env elems (some w) (.fill b) = .lit (LVec.replicate w b) := by
  simp [instExpr2]

theorem mul_static (N : Nat) (hN : 1 ≤ N) (decls : List Decl) :
    design.pdesign.processes.map (instProcess2 ((mulEnv N).withDecls decls) (mulElems N)) =
      [s0Proc N, c0Proc N, t0Proc N, pHiProc N] := by
  have E := mulEnvOk N decls
  rw [mul_static_source]
  -- `p[2*N-1:N]`: the target window (a static-label `ArraySel` path over
  -- `[2*N-1:0]`) and the row part-select read.
  have hm : evalInt ((mulEnv N).withDecls decls) pMsb = .ok (2 * (N : Int) - 1) :=
    evalInt_pMsb E.n
  have hpd : ((mulEnv N).withDecls decls).dims.lookup "p" = some [(2 * (N : Int) - 1, 0)] := by
    simpa using mulEnv_p N
  have hgp := arrayPartGeom_range_of (is := []) (a := pMsb) (b := .paramRef "N" none)
    (arrayDims_of hpd) (walkIndices_nil (env := (mulEnv N).withDecls decls) _) hm
    (evalInt_paramRef_of E.n)
    (by rw [labelOffset_desc0 (m := 2 * (N : Int) - 1) (by omega),
      labelOffset_desc0 (m := 2 * (N : Int) - 1) (by omega)]; omega)
  rw [labelOffset_desc0 (m := 2 * (N : Int) - 1) (by omega) (N : Int),
    labelOffset_desc0 (m := 2 * (N : Int) - 1) (by omega) (2 * (N : Int) - 1)] at hgp
  have hcp := dimCount_desc0 (by omega : (0 : Int) ≤ 2 * (N : Int) - 1)
  have hP := arrayPartTarget_of_inRange hgp (by omega) (by omega)
  have hpw : (2 * (N : Int) - 1 - N + 1).toNat * dimsStride [] = N := by simp; omega
  have hpl : ((0 : Int) + (N : Int) * ((dimsStride [] : Nat) : Int)).toNat = N := by simp
  rw [hpw, hpl] at hP
  have hwalk := walkIndices_desc0_cons (env := (mulEnv N).withDecls decls) (ds := [((N : Int), 0)])
    (by omega : (0 : Int) ≤ (N : Int) - 1) E.nM1 (by omega) (Int.le_refl _)
    (walkIndices_nil (env := (mulEnv N).withDecls decls) [((N : Int), 0)])
  have hgeom := arrayPartGeom_range_of (a := .paramRef "N" none) (b := .int 1)
    (arrayDims_of E.s) hwalk (evalInt_paramRef_of E.n) (evalInt_int 1)
    (by rw [labelOffset_desc0 (m := (N : Int)) (by omega),
      labelOffset_desc0 (m := (N : Int)) (by omega)]; omega)
  rw [labelOffset_desc0 (m := (N : Int)) (by omega) (N : Int),
    labelOffset_desc0 (m := (N : Int)) (by omega) 1] at hgeom
  have hc := dimCount_desc0 (by omega : (0 : Int) ≤ (N : Int))
  have hread := arrayPartRead_of_inRange hgeom (by omega) (by omega)
  have hsw := selfWidth2_arrayPart_of (elems := mulElems N) hgeom
  have hwid : ((N : Int) - 1 + 1).toNat * dimsStride [] = N := by simp
  rw [hwid] at hsw hread
  have hs : dimsStride [((N : Int), 0)] = N + 1 := by
    simp only [dimsStride_cons, dimsStride_nil, Nat.mul_one]
    omega
  have hoff : (((N : Int) - 1) * ((dimsStride [((N : Int), 0)] : Nat) : Int) + 0
      + 1 * ((dimsStride [] : Nat) : Int)).toNat = N * N := by
    rw [hs, dimsStride_nil]
    have hsq : ((N : Int) - 1) * ((N + 1 : Nat) : Int) + 0 + 1 * ((1 : Nat) : Int) =
        ((N * N : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul, Int.sub_mul, Int.mul_add, Int.mul_one,
        Int.one_mul, Int.add_zero, Int.natCast_one]
      omega
    rw [hsq, Int.toNat_natCast]
  rw [hoff] at hread
  -- `s[0]`, `c[0]`, `t[0]`, `pp[0]`: the first row of a `[N-1:0][…]` array.
  have hrow : ∀ {n : String} {m : Int} (hd : ((mulEnv N).withDecls decls).dims.lookup n =
      some [((N : Int) - 1, 0), (m, 0)]),
      arrayElemWindow ((mulEnv N).withDecls decls) n [.int 0] = .ok (0, dimCount m 0, true) := by
    intro n m hd
    rw [arrayElemWindow_of (arrayDims_of hd) (walkIndices_desc0_cons (by omega) (evalInt_int 0)
      (Int.le_refl 0) (by omega) (walkIndices_nil _))]
    simp [dimsStride]
  have hcN : dimCount ((N : Int) - 1) 0 = N := by unfold dimCount; omega
  have hcN1 : dimCount (N : Int) 0 = N + 1 := by unfold dimCount; omega
  have hwS := hrow (n := "s") E.s
  have hwC := hrow (n := "c") E.c
  have hwT := hrow (n := "t") E.t
  have hwP := hrow (n := "pp") E.pp
  rw [hcN1] at hwS hwC
  rw [hcN] at hwT hwP
  simp only [List.map_cons, List.map_nil]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, ?_⟩⟩⟩
  · have hz : zero1.width = 1 := LVec.width_ofNat 1 0
    have h1 : selfWidth2 ((mulEnv N).withDecls decls) (mulElems N) (.lit zero1) = some 1 := by
      rw [selfWidth2_lit, hz]
    have hsum : selfWidthSum2 ((mulEnv N).withDecls decls) (mulElems N)
        [.lit zero1, .arrayElem "pp" [.int 0]] = some (N + 1) := by
      rw [selfWidthSum2_cons_of h1 (selfWidthSum2_cons_of
        (selfWidth2_arrayElem_of hwP) selfWidthSum2_nil), Option.some.injEq]
      omega
    rw [s0T, instProcess2_assignL _ (by rw [instLhs2_arrayElem, arrayElemTarget_of_inRange hwS]),
      fitExpr2_concat hsum, if_pos rfl, instParts2_cons, instParts2_cons, instParts2_nil,
      instExpr2_lit, instExpr2_arrayElem, arrayElemRead_of_inRange hwP]
    simp only [s0Proc, Int.toNat_zero]
  · rw [c0T, instProcess2_assignL _ (by rw [instLhs2_arrayElem, arrayElemTarget_of_inRange hwC]),
      fitExpr2_of_not_rigid (N + 1) rfl, instExpr2_fill_ctx]
    simp only [c0Proc, Int.toNat_zero]
  · rw [t0T, instProcess2_assignL _ (by rw [instLhs2_arrayElem, arrayElemTarget_of_inRange hwT]),
      fitExpr2_of_not_rigid N rfl, instExpr2_fill_ctx]
    simp only [t0Proc, Int.toNat_zero]
  · rw [pHiT, instProcess2_assignL _ (by rw [instLhs2_arrayPart]; exact hP),
      fitExpr2_of_rigid_eq rfl hsw, instExpr2_arrayPart _ (dynPartPlan_of_geom hgeom), hread]
    rfl

theorem mul_gens (N : Nat) (hN : 1 ≤ N) (decls : List Decl) :
    expandList2 ((mulEnv N).withDecls decls) (mulElems N) (PDesign.surfaceFuel [(N : Int)])
      design.pdesign.generates =
      .ok (((List.range N).flatMap fun i => (List.range N).map fun j => ppCell N i j)
        ++ (((List.range (N - 1)).flatMap fun k => rowCells N (k + 1))
        ++ (List.range N).map (outCell N))) := by
  have hF : N < PDesign.surfaceFuel [(N : Int)] := by
    have := Nat.le_mul_self (N + 2)
    simp [PDesign.surfaceFuel]
    omega
  have E := mulEnvOk N decls
  rw [mul_generates]
  exact expandList2_cons_ok (mul_pp_instantiated N hN decls _ (by simp [mulElems])
      (by simp [mulElems, List.lookup]))
    (expandList2_cons_ok (mul_row_expand _ _ N _ hN hF E)
      (expandList2_singleton_ok
        (mul_out_expand _ _ N _ hN hF E (by simp [mulElems, List.lookup]))))

/-! ### The one-driver rule, for every `N`

`design.sem N` is `instantiateGD2`: the instantiated design under the
one-driver rule (`Hier2.lean`, "Drivers" — a flat top is checked at every
parameter point since 2026-10-28). It holds for every `N`, by the
process-list recipe of `Hier2Gen.lean`. Each partial-product row and each
adder row is stated over its BASE offsets (`q = i*N` into `pp`/`t`,
`r = i*(N+1)` into `s`/`c`), so every disjointness inside a row is linear
for `omega`; `rowMajor_le` orders the bases of two rows. -/

theorem mul_declNames : design.pdesign.declNames = ["a", "b", "p", "pp", "s", "c", "t"] := rfl

theorem mul_inputNames : design.pdesign.inputNames = ["a", "b"] := rfl

/-- Partial-product row `i`'s windows over its base `q = i*N`. -/
def ppWins (N q : Nat) : List DrvWin := (List.range N).flatMap fun j => [("pp", some (q + j, 1))]

/-- Adder row `i`'s windows over its bases `r = i*(N+1)` (`s`, `c`) and
`q = i*N` (`t`): the carry-in, the bit cells, the top sum bit. -/
def rowWins (N r q : Nat) : List DrvWin :=
  ("c", some (r, 1)) :: ((List.range N).flatMap fun j =>
    [("t", some (q + j, 1)), ("s", some (r + j, 1)), ("c", some (r + (j + 1), 1))])
    ++ [("s", some (r + N, 1))]

/-- The four static windows: `s[0]`, `c[0]`, `t[0]` (whole rows) and
`p[2N-1:N]`. -/
def staticWins (N : Nat) : List DrvWin :=
  [("s", some (0, N + 1)), ("c", some (0, N + 1)), ("t", some (0, N)), ("p", some (N, N))]

/-- The low output bits `p[i]`. -/
def outWins (N : Nat) : List DrvWin := (List.range N).flatMap fun i => [("p", some (i, 1))]

/-- The continuous-driver windows of the instantiated multiplier. -/
theorem mul_driverWins (N : Nat) :
    driverWins ["a", "b", "p", "pp", "s", "c", "t"] (mulProcs N) =
      staticWins N ++ (List.range N).flatMap (fun i => ppWins N (i * N))
        ++ (List.range (N - 1)).flatMap (fun k => rowWins N ((k + 1) * (N + 1)) ((k + 1) * N))
        ++ outWins N := by
  have hp : ["a", "b", "p", "pp", "s", "c", "t"].contains "p" = true := by decide
  have hpp : ["a", "b", "p", "pp", "s", "c", "t"].contains "pp" = true := by decide
  have hs : ["a", "b", "p", "pp", "s", "c", "t"].contains "s" = true := by decide
  have hc : ["a", "b", "p", "pp", "s", "c", "t"].contains "c" = true := by decide
  have ht : ["a", "b", "p", "pp", "s", "c", "t"].contains "t" = true := by decide
  simp only [mulProcs, rowCells, driverWins_append, driverWins_cons, driverWins_nil,
    driverWins_flatMap, driverWins_map, s0Proc, c0Proc, t0Proc, pHiProc, ppCell, cRowCell, tCell,
    sCell, cCell, sTopCell, outCell, Process2.drvWins, Lhs2.drvWins, List.filter_cons,
    List.filter_nil, hp, hpp, hs, hc, ht, ↓reduceIte, List.cons_append, List.nil_append,
    List.append_nil, staticWins, ppWins, rowWins, outWins]

/-- Two windows of different signals never overlap. -/
private theorem ov_names {n n' : String} {l w l' w' : Nat} (h : n ≠ n') :
    DrvWin.overlaps (n, some (l, w)) (n', some (l', w')) = false :=
  DrvWin.overlaps_some_eq_false.mpr (Or.inl h)

/-- A partial-product row's windows are pairwise disjoint. -/
theorem ppWins_pairwise (N q : Nat) :
    (ppWins N q).Pairwise fun a b => a.overlaps b = false :=
  pairwise_flatMap_range (fun _ _ => List.pairwise_singleton _ _)
    fun j k hjk _ a ha b hb => by
      simp only [List.mem_singleton] at ha hb
      subst ha hb
      exact DrvWin.overlaps_some_eq_false.mpr (Or.inr (Or.inr (by omega)))

/-- Two partial-product rows with bases `q + N ≤ q'` are disjoint. -/
theorem ppWins_cross {N q q' : Nat} (h : q + N ≤ q') :
    ∀ a ∈ ppWins N q, ∀ b ∈ ppWins N q', a.overlaps b = false := by
  intro a ha b hb
  simp only [ppWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at ha hb
  obtain ⟨j, hj, rfl⟩ := ha
  obtain ⟨k, hk, rfl⟩ := hb
  exact DrvWin.overlaps_some_eq_false.mpr (Or.inr (Or.inr (by omega)))

/-- Membership in an adder row. -/
theorem mem_rowWins {N r q : Nat} {a : DrvWin} :
    a ∈ rowWins N r q ↔ a = ("c", some (r, 1)) ∨ a = ("s", some (r + N, 1)) ∨
      ∃ j < N, a = ("t", some (q + j, 1)) ∨ a = ("s", some (r + j, 1)) ∨
        a = ("c", some (r + (j + 1), 1)) := by
  simp only [rowWins, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false]
  constructor
  · rintro ((h | ⟨j, hj, h⟩) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨j, hj, h⟩)
    · exact Or.inr (Or.inl h)
  · rintro (h | h | ⟨j, hj, h⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨j, hj, h⟩)

/-- An adder row's windows are pairwise disjoint. -/
theorem rowWins_pairwise (N r q : Nat) :
    (rowWins N r q).Pairwise fun a b => a.overlaps b = false := by
  rw [rowWins, List.pairwise_append, List.pairwise_cons]
  refine ⟨⟨fun b hb => ?_, pairwise_flatMap_range (fun j _ => ?_)
    fun j k hjk _ a ha b hb => ?_⟩, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    obtain ⟨j, hj, rfl | rfl | rfl⟩ := hb <;> simp [DrvWin.overlaps]
  · simp [DrvWin.overlaps]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp [DrvWin.overlaps] <;> omega
  · simp only [List.mem_singleton] at hb
    subst hb
    simp only [List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
      or_false] at ha
    rcases ha with rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;> simp [DrvWin.overlaps] <;> omega

/-- Two adder rows with bases `r + (N+1) ≤ r'`, `q + N ≤ q'` are disjoint. -/
theorem rowWins_cross {N r q r' q' : Nat} (hr : r + (N + 1) ≤ r') (hq : q + N ≤ q') :
    ∀ a ∈ rowWins N r q, ∀ b ∈ rowWins N r' q', a.overlaps b = false := by
  intro a ha b hb
  rw [mem_rowWins] at ha hb
  rcases ha with rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;>
    rcases hb with rfl | rfl | ⟨k, hk, rfl | rfl | rfl⟩ <;> simp [DrvWin.overlaps] <;> omega

/-- **The one-driver rule holds for every `N`.** -/
theorem mul_driversOk (N : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (mulProcs N) = true := by
  rw [mul_declNames, mul_inputNames]
  apply driversOk_of_continuous
  · rw [List.flatMap_eq_nil_iff]
    intro p hp
    simp only [mulProcs, rowCells, List.mem_append, List.mem_cons, List.mem_flatMap,
      List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hp
    rcases hp with (((rfl | rfl | rfl | rfl) | ⟨i, -, j, -, rfl⟩) |
      ⟨k, -, (rfl | ⟨j, -, rfl | rfl | rfl⟩) | rfl⟩) | ⟨i, -, rfl⟩ <;> rfl
  · rw [mul_driverWins]
    simp only [List.pairwise_append]
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · simp [staticWins, DrvWin.overlaps]
    · exact pairwise_flatMap_range (fun i _ => ppWins_pairwise N (i * N))
        fun i i' hii' _ => ppWins_cross (rowMajor_le hii')
    · intro a ha b hb
      simp only [staticWins, List.mem_cons, List.not_mem_nil, or_false] at ha
      simp only [ppWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at hb
      obtain ⟨i, -, j, -, rfl⟩ := hb
      rcases ha with rfl | rfl | rfl | rfl <;> exact ov_names (by decide)
    · exact pairwise_flatMap_range (fun k _ => rowWins_pairwise N _ _)
        fun k k' hkk' _ => rowWins_cross (rowMajor_le (by omega)) (rowMajor_le (by omega))
    · intro a ha b hb
      simp only [List.mem_append] at ha
      simp only [List.mem_flatMap, List.mem_range] at hb
      obtain ⟨k, -, hb⟩ := hb
      have hr : 0 * (N + 1) + (N + 1) ≤ (k + 1) * (N + 1) := rowMajor_le (by omega)
      have hq : 0 * N + N ≤ (k + 1) * N := rowMajor_le (by omega)
      rw [mem_rowWins] at hb
      rcases ha with ha | ha
      · simp only [staticWins, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;> simp [DrvWin.overlaps] <;> omega
      · simp only [ppWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at ha
        obtain ⟨i, -, j, -, rfl⟩ := ha
        rcases hb with rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;> exact ov_names (by decide)
    · exact pairwise_flatMap_range (fun _ _ => List.pairwise_singleton _ _)
        fun i i' hii' _ a ha b hb => by
          simp only [List.mem_singleton] at ha hb
          subst ha hb
          exact DrvWin.overlaps_some_eq_false.mpr (Or.inr (Or.inr (by omega)))
    · intro a ha b hb
      simp only [outWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · simp only [staticWins, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> simp [DrvWin.overlaps] <;> omega
      · simp only [ppWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at ha
        obtain ⟨i', -, j, -, rfl⟩ := ha
        exact ov_names (by decide)
      · simp only [List.mem_flatMap, List.mem_range] at ha
        obtain ⟨k, -, ha⟩ := ha
        rw [mem_rowWins] at ha
        rcases ha with rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;> exact ov_names (by decide)
  · intro w hw
    rw [mul_driverWins] at hw
    simp only [List.mem_append, staticWins, ppWins, outWins, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap, List.mem_range] at hw
    rcases hw with (((rfl | rfl | rfl | rfl) | ⟨i, -, j, -, rfl⟩) | ⟨k, -, hw⟩) | ⟨i, -, rfl⟩
    all_goals first
      | rfl
      | (rw [mem_rowWins] at hw
         rcases hw with rfl | rfl | ⟨j, -, rfl | rfl | rfl⟩ <;> rfl)

/-- The instantiated declarations for `N ≥ 1`: the ports `a b : N`, `p : 2N`,
the partial products `pp` and propagates `t` (`N*N` bits), the row sums `s`
and carries `c` (`N*(N+1)` bits). -/
def mulDecls (N : Nat) : List Decl :=
  [{ name := "a", width := N, isInput := true },
   { name := "b", width := N, isInput := true },
   { name := "p", width := 2 * N, isOutput := true },
   { name := "pp", width := N * N },
   { name := "s", width := N * (N + 1) },
   { name := "c", width := N * (N + 1) },
   { name := "t", width := N * N }]

theorem mul_buildDecls (N : Nat) (hN : 1 ≤ N) :
    buildDecls (mulEnv N) design.pdesign.decls = .ok (mulDecls N) := by
  have h1 : ((N : Int) - 1).natAbs + 1 = N := by omega
  have h2 : (2 * (N : Int) - 1).natAbs + 1 = 2 * N := by omega
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt, mulEnv,
    mulScope, List.lookup, Gen2.except_ok_bind, h1, h2, mulDecls]

/-! # Part 2. The comb profile and the acyclicity certificate -/

/-! ## The family member `design.sem N` -/

/-- `instantiate2` at symbolic `N ≥ 1`. -/
theorem mul_instantiate2 (N : Nat) (hN : 1 ≤ N) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (design.pdesign.assemble2 (mulEnv N) (mulDecls N) (mulElems N)
        (((List.range N).flatMap fun i => (List.range N).map fun j => ppCell N i j)
          ++ (((List.range (N - 1)).flatMap fun k => rowCells N (k + 1))
          ++ (List.range N).map (outCell N)))) :=
  PDesign.instantiate2_of_ok rfl (mul_paramEnv N) (mul_buildDecls N hN) (mul_elems N hN)
    (mul_gens N hN (mulDecls N))

theorem mul_instD_processes (N : Nat) (hN : 1 ≤ N) :
    (design.pdesign.instantiateD2 [(N : Int)]).processes.toList = mulProcs N := by
  have hothers : design.pdesign.others = [] := rfl
  rw [PDesign.instantiateD2_of_ok (mul_instantiate2 N hN), PDesign.assemble2_processes,
    mul_static N hN (mulDecls N), hothers]
  simp [mulProcs]

/-- `design.sem N` is the instantiated design: its one-driver guard passes. -/
theorem mul_sem_eq (N : Nat) (hN : 1 ≤ N) :
    design.sem N = design.pdesign.instantiateD2 [(N : Int)] := by
  show design.pdesign.instantiateGD2 [(N : Int)] = _
  apply PDesign.instantiateGD2_of_driversOk
  rw [mul_instD_processes N hN]
  exact mul_driversOk N

theorem mul_sem_processes (N : Nat) (hN : 1 ≤ N) :
    (design.sem N).processes.toList = mulProcs N := by
  rw [mul_sem_eq N hN]
  exact mul_instD_processes N hN

theorem mul_sem_decls (N : Nat) (hN : 1 ≤ N) : (design.sem N).decls.toList = mulDecls N := by
  rw [mul_sem_eq N hN, PDesign.instantiateD2_of_ok (mul_instantiate2 N hN),
    PDesign.assemble2_decls]

/-! ## The process table -/

theorem mul_getElem?_of_mem {N : Nat} (hN : 1 ≤ N) {p : Process2} (h : p ∈ mulProcs N) :
    ∃ k : Nat, (design.sem N).processes[k]? = some p := by
  rw [← mul_sem_processes N hN, List.mem_iff_getElem?] at h
  obtain ⟨k, hk⟩ := h
  rw [Array.getElem?_toList] at hk
  exact ⟨k, hk⟩

theorem mul_mem_of_getElem? {N : Nat} (hN : 1 ≤ N) {k : Nat} {p : Process2}
    (h : (design.sem N).processes[k]? = some p) : p ∈ mulProcs N := by
  rw [← mul_sem_processes N hN, List.mem_iff_getElem?]
  exact ⟨k, by rw [Array.getElem?_toList]; exact h⟩

/-- **Every process of the multiplier**, by kind: a property of each of the
eleven cell kinds is a property of every process. -/
theorem mulProcs_forall {N : Nat} {P : Process2 → Prop}
    (h0 : P (s0Proc N)) (h1 : P (c0Proc N)) (h2 : P (t0Proc N)) (h3 : P (pHiProc N))
    (hpp : ∀ i < N, ∀ j < N, P (ppCell N i j))
    (hcr : ∀ k, k + 1 < N → P (cRowCell N (k + 1)))
    (ht : ∀ k, k + 1 < N → ∀ j < N, P (tCell N (k + 1) j))
    (hs : ∀ k, k + 1 < N → ∀ j < N, P (sCell N (k + 1) j))
    (hc : ∀ k, k + 1 < N → ∀ j < N, P (cCell N (k + 1) j))
    (hst : ∀ k, k + 1 < N → P (sTopCell N (k + 1)))
    (hout : ∀ i < N, P (outCell N i)) :
    ∀ p ∈ mulProcs N, P p := by
  intro p hp
  simp only [mulProcs, rowCells, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hp
  rcases hp with (((rfl | rfl | rfl | rfl) | ⟨i, hi, j, hj, rfl⟩) |
      ⟨k, hk, (rfl | ⟨j, hj, rfl | rfl | rfl⟩) | rfl⟩) | ⟨i, hi, rfl⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact hpp i hi j hj
  · exact hcr k (by omega)
  · exact ht k (by omega) j hj
  · exact hs k (by omega) j hj
  · exact hc k (by omega) j hj
  · exact hst k (by omega)
  · exact hout i hi

/-- Membership of each cell kind. -/
theorem mem_ppCell {N i j : Nat} (hi : i < N) (hj : j < N) : ppCell N i j ∈ mulProcs N := by
  simp only [mulProcs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨i, hi, j, hj, rfl⟩))

theorem mem_rowCell {N k : Nat} (hk : k + 1 < N) {p : Process2} (h : p ∈ rowCells N (k + 1)) :
    p ∈ mulProcs N := by
  simp only [mulProcs, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inr ⟨k, by omega, h⟩)

theorem mem_cRowCell {N k : Nat} (hk : k + 1 < N) : cRowCell N (k + 1) ∈ mulProcs N :=
  mem_rowCell hk (by simp [rowCells])

theorem mem_tCell {N k j : Nat} (hk : k + 1 < N) (hj : j < N) : tCell N (k + 1) j ∈ mulProcs N :=
  mem_rowCell hk (by simp only [rowCells, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_range]; exact Or.inl (Or.inr ⟨j, hj, by simp⟩))

theorem mem_sCell {N k j : Nat} (hk : k + 1 < N) (hj : j < N) : sCell N (k + 1) j ∈ mulProcs N :=
  mem_rowCell hk (by simp only [rowCells, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_range]; exact Or.inl (Or.inr ⟨j, hj, by simp⟩))

theorem mem_cCell {N k j : Nat} (hk : k + 1 < N) (hj : j < N) : cCell N (k + 1) j ∈ mulProcs N :=
  mem_rowCell hk (by simp only [rowCells, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_range]; exact Or.inl (Or.inr ⟨j, hj, by simp⟩))

theorem mem_sTopCell {N k : Nat} (hk : k + 1 < N) : sTopCell N (k + 1) ∈ mulProcs N :=
  mem_rowCell hk (by simp [rowCells])

theorem mem_outCell {N i : Nat} (hi : i < N) : outCell N i ∈ mulProcs N := by
  simp only [mulProcs, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr ⟨i, hi, rfl⟩

theorem mem_s0Proc {N : Nat} : s0Proc N ∈ mulProcs N := by simp [mulProcs]
theorem mem_pHiProc {N : Nat} : pHiProc N ∈ mulProcs N := by simp [mulProcs]

/-! ## Declarations (`1 ≤ N`) -/

section Decls

variable {N : Nat} (hN : 1 ≤ N)
include hN

theorem mul_declWidth (n : String) :
    (design.sem N).declWidth n = ((mulDecls N).find? fun dc => dc.name == n).map Decl.width := by
  simp only [Design2.declWidth, mul_sem_decls N hN]

theorem mul_declWidth_p : (design.sem N).declWidth "p" = some (2 * N) := by
  simp [mul_declWidth hN, mulDecls]
theorem mul_declWidth_pp : (design.sem N).declWidth "pp" = some (N * N) := by
  simp [mul_declWidth hN, mulDecls]
theorem mul_declWidth_s : (design.sem N).declWidth "s" = some (N * (N + 1)) := by
  simp [mul_declWidth hN, mulDecls]
theorem mul_declWidth_c : (design.sem N).declWidth "c" = some (N * (N + 1)) := by
  simp [mul_declWidth hN, mulDecls]
theorem mul_declWidth_t : (design.sem N).declWidth "t" = some (N * N) := by
  simp [mul_declWidth hN, mulDecls]

theorem mul_sem_inputNames : (design.sem N).inputNames.toList = ["a", "b"] := by
  simp [Design2.inputNames, mul_sem_decls N hN, mulDecls]

end Decls

/-! ## Every process is a slice assign on a module signal -/

/-- The driver window of a slice assign (`("", none)` for anything else). -/
def sliceDrv : Process2 → DrvWin
  | .assign (.slice n lo w) _ => (n, some (lo, w))
  | _ => ("", none)

/-- The signals the multiplier drives. -/
def mulDriven : List String := ["p", "pp", "s", "c", "t"]

theorem mulProcs_slice {N : Nat} :
    ∀ p ∈ mulProcs N, ∃ n lo w e, p = .assign (.slice n lo w) e ∧ n ∈ mulDriven := by
  refine mulProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> exact ⟨_, _, _, _, rfl, by simp [mulDriven]⟩

/-- `driverWins` of a list of slice assigns on the given names is their
windows, one per process. -/
theorem driverWins_eq_map {names : List String} :
    ∀ {ps : List Process2}, (∀ p ∈ ps, ∃ n lo w e, p = .assign (.slice n lo w) e ∧ n ∈ names) →
      driverWins names ps = ps.map sliceDrv
  | [], _ => rfl
  | p :: ps, h => by
      obtain ⟨n, lo, w, e, rfl, hn⟩ := h p (List.mem_cons_self ..)
      rw [driverWins_cons, driverWins_eq_map (fun q hq => h q (List.mem_cons_of_mem _ hq))]
      simp [Process2.drvWins, Lhs2.drvWins, sliceDrv, hn]

/-- The process list's windows are pairwise disjoint (from the one-driver
rule, `mul_driversOk`). -/
theorem mulProcs_pairwise (N : Nat) :
    (mulProcs N).Pairwise fun p q => (sliceDrv p).overlaps (sliceDrv q) = false := by
  have h := (driversOk_iff.mp (mul_driversOk N)).1
  rw [mul_declNames, driverWins_eq_map (fun p hp => by
    obtain ⟨n, lo, w, e, hp, hn⟩ := mulProcs_slice p hp
    exact ⟨n, lo, w, e, hp, by simp [mulDriven] at hn; rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      simp⟩), List.pairwise_map] at h
  exact h

/-! ## The comb profile -/

/-- Process-wise facts, pulled back from an index. -/
theorem mul_proc_slice {N : Nat} (hN : 1 ≤ N) {k : Nat} {t : Lhs2} {e : Expr2}
    (h : (design.sem N).processes[k]? = some (.assign t e)) :
    ∃ n lo w, t = .slice n lo w ∧ n ∈ mulDriven := by
  obtain ⟨n, lo, w, e', hp, hn⟩ := mulProcs_slice _ (mul_mem_of_getElem? hN h)
  simp only [Process2.assign.injEq] at hp
  exact ⟨n, lo, w, hp.1, hn⟩

/-- Row-major bound: a cell of row `i < M` at offset `c < K` lies below `M * K`. -/
theorem rowMajor_lt {K M i c : Nat} (hi : i < M) (hc : c < K) : i * K + c < M * K := by
  have := rowMajor_le (K := K) hi
  omega

theorem mul_disjoint {N : Nat} (hN : 1 ≤ N) :
    ∀ i j wi wj, i ≠ j → (design.sem N).Writes i wi → (design.sem N).Writes j wj →
      Win.overlaps wi wj = false := by
  intro i j wi wj hij ⟨ti, ei, hi, hwi⟩ ⟨tj, ej, hj, hwj⟩
  obtain ⟨n, lo, w, rfl, -⟩ := mul_proc_slice hN hi
  obtain ⟨n', lo', w', rfl, -⟩ := mul_proc_slice hN hj
  simp only [Lhs2.wins_slice, List.mem_singleton] at hwi hwj
  subst hwi hwj
  have hpw := mulProcs_pairwise N
  rw [← mul_sem_processes N hN, List.pairwise_iff_getElem] at hpw
  rw [← Array.getElem?_toList, List.getElem?_eq_some_iff] at hi hj
  obtain ⟨hil, hi⟩ := hi
  obtain ⟨hjl, hj⟩ := hj
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have := hpw i j hil hjl h
    rw [hi, hj] at this
    simp only [sliceDrv] at this
    rw [DrvWin.overlaps_some_eq_false] at this
    rw [Win.overlaps_eq_false]
    exact this
  · have := hpw j i hjl hil h
    rw [hi, hj] at this
    simp only [sliceDrv] at this
    rw [DrvWin.overlaps_some_eq_false] at this
    rw [Win.overlaps_eq_false]
    rcases this with h | h | h
    · exact Or.inl (Ne.symm h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- Every write window lies inside its signal (row-major index bounds). -/
theorem mul_inWidth {N : Nat} (hN : 1 ≤ N) :
    ∀ p ∈ mulProcs N, ∀ t e, p = .assign t e → ∀ n lo w, (n, lo, w) ∈ t.wins (design.sem N) →
      ∃ dw, (design.sem N).declWidth n = some dw ∧ lo + w ≤ dw := by
  refine mulProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t e h n lo w hw
    simp only [s0Proc, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_s hN, by have := Nat.le_mul_of_pos_left (N + 1) hN; omega⟩
  · intro t e h n lo w hw
    simp only [c0Proc, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_c hN, by have := Nat.le_mul_of_pos_left (N + 1) hN; omega⟩
  · intro t e h n lo w hw
    simp only [t0Proc, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, hw⟩ := hw
    refine ⟨_, mul_declWidth_t hN, ?_⟩
    rw [hw]
    have := Nat.le_mul_of_pos_left N hN
    omega
  · intro t e h n lo w hw
    simp only [pHiProc, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_p hN, by omega⟩
  · intro i hi j hj t e h n lo w hw
    simp only [ppCell, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_pp hN, by have := rowMajor_lt hi hj; omega⟩
  · intro k hk t e h n lo w hw
    simp only [cRowCell, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_c hN, by
      have := rowMajor_lt (K := N + 1) (c := 0) hk (by omega); omega⟩
  · intro k hk j hj t e h n lo w hw
    simp only [tCell, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_t hN, by have := rowMajor_lt hk hj; omega⟩
  · intro k hk j hj t e h n lo w hw
    simp only [sCell, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_s hN, by
      have := rowMajor_lt (K := N + 1) (c := j) hk (by omega); omega⟩
  · intro k hk j hj t e h n lo w hw
    simp only [cCell, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_c hN, by
      have := rowMajor_lt (K := N + 1) (c := j + 1) hk (by omega); omega⟩
  · intro k hk t e h n lo w hw
    simp only [sTopCell, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_s hN, by
      have := rowMajor_lt (K := N + 1) (c := N) hk (by omega); omega⟩
  · intro i hi t e h n lo w hw
    simp only [outCell, Process2.assign.injEq] at h; obtain ⟨rfl, -⟩ := h
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    exact ⟨_, mul_declWidth_p hN, by omega⟩

/-- The right-hand side of an assign. -/
def rhsOf : Process2 → Expr2
  | .assign _ e => e
  | _ => .lit ⟨#[]⟩

theorem mulProcs_rhsFree {N : Nat} : ∀ p ∈ mulProcs N, (rhsOf p).unsupportedFree = true := by
  refine mulProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

/-- Every declared name. -/
def mulNames : List String := ["a", "b", "p", "pp", "s", "c", "t"]

theorem mulProcs_rhsDeclared {N : Nat} :
    ∀ p ∈ mulProcs N, ((rhsOf p).idents.all fun x => x ∈ mulNames) = true := by
  refine mulProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

theorem mul_comb {N : Nat} (hN : 1 ≤ N) : CombDesign (design.sem N) where
  nodup := by
    rw [mul_sem_decls N hN]
    simp only [mulDecls, List.map_cons, List.map_nil]
    decide
  assign := by
    intro j p hp
    obtain ⟨n, lo, w, e, rfl, -⟩ := mulProcs_slice p (mul_mem_of_getElem? hN hp)
    exact ⟨_, _, _, rfl, rfl⟩
  inWidth := by
    intro j n lo w ⟨t, e, hp, hw⟩
    exact mul_inWidth hN _ (mul_mem_of_getElem? hN hp) t e rfl n lo w hw
  notInput := by
    rintro n ⟨j, lo, w, t, e, hp, hw⟩
    obtain ⟨n', lo', w', rfl, hn⟩ := mul_proc_slice hN hp
    simp only [Lhs2.wins_slice, List.mem_singleton, Prod.mk.injEq] at hw
    obtain ⟨rfl, -, -⟩ := hw
    rw [mul_sem_inputNames hN]
    simp only [mulDriven, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  disjoint := mul_disjoint hN
  selfDisjoint := by
    intro j t e hp
    obtain ⟨n, lo, w, rfl, -⟩ := mul_proc_slice hN hp
    exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro j t e hp
    exact mulProcs_rhsFree _ (mul_mem_of_getElem? hN hp)
  rhsDeclared := by
    intro j t e hp x hx
    have h := List.all_eq_true.mp (mulProcs_rhsDeclared _ (mul_mem_of_getElem? hN hp)) x hx
    rw [mul_sem_decls N hN]
    simpa [mulNames, mulDecls] using h
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [mul_sem_decls N hN] at hdc
    simp [mulDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [mul_sem_decls N hN] at hdc
    simp [mulDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## Acyclicity -/

/-- The rank of a process, by its write window: row-major over the adder
array (`s`/`c` at their flat offset, `t` at the offset its row would have in
`s`), propagate before carry before sum; the partial products first, the
output last. -/
def rkWin (N : Nat) (n : String) (lo : Nat) : Nat :=
  if n = "s" then 3 * lo + 2 else if n = "c" then 3 * lo + 1
  else if n = "t" then 3 * (lo + lo / N) else if n = "p" then 3 * (N * N + N) + 3 else 0

/-- The rank certificate: the rank of the process's write window. -/
def mulRank (N : Nat) (k : Nat) : Nat :=
  match (design.sem N).processes[k]? with
  | some (.assign (.slice n lo _) _) => rkWin N n lo
  | _ => 0

theorem rowdiv {N i j : Nat} (hj : j < N) : (i * N + j) / N = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < N), Nat.div_eq_of_lt hj,
    Nat.zero_add]

theorem mul_expand (k N : Nat) :
    (k + 1) * (N + 1) = k * N + k + N + 1 ∧ (k + 1) * N = k * N + N ∧ k * (N + 1) = k * N + k ∧
      N * (N + 1) = N * N + N := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] <;>
    omega

/-- Readers of the multiplier, kind by kind: every window a process reads is
written by a process of strictly lower rank. -/
theorem mul_reader {N : Nat} (hN : 1 ≤ N) {n' : String} {lo' w' : Nat} (hn' : n' ∈ mulDriven) :
    ∀ p ∈ mulProcs N, ∀ m lo w e, p = .assign (.slice m lo w) e →
      ∀ r ∈ e.reads, r.overlaps (n', lo', w') = true → rkWin N n' lo' < rkWin N m lo := by
  refine mulProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `s[0 +: N+1] = {1'b0, pp[0 +: N]}`
    intro m lo w e h r hr hov
    simp only [s0Proc, Process2.assign.injEq, Lhs2.slice.injEq] at h
    obtain ⟨⟨rfl, hlo, -⟩, rfl⟩ := h
    subst lo
    simp [Expr2.reads, Expr2.listReads, Expr2.sliceReads] at hr
    subst hr
    simp only [ReadWin.overlaps, Win.overlaps_eq_true] at hov
    obtain ⟨rfl, -, -⟩ := hov
    simp [rkWin]
  · -- `c[0 +: N+1] = '0`
    intro m lo w e h r hr hov
    simp only [c0Proc, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Expr2.reads] at hr
  · -- `t[0 +: N] = '0`
    intro m lo w e h r hr hov
    simp only [t0Proc, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Expr2.reads] at hr
  · -- `p[N +: N] = s[N*N +: N]`
    intro m lo w e h r hr hov
    simp only [pHiProc, Process2.assign.injEq, Lhs2.slice.injEq] at h
    obtain ⟨⟨rfl, hlo, -⟩, rfl⟩ := h
    subst lo
    simp [Expr2.reads, Expr2.sliceReads] at hr
    subst hr
    simp only [ReadWin.overlaps, Win.overlaps_eq_true] at hov
    obtain ⟨rfl, -, h2⟩ := hov
    simp [rkWin]
    omega
  · -- `pp[i*N + j] = a[j] & b[i]`: reads inputs only
    intro i hi j hj m lo w e h r hr hov
    simp only [ppCell, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;> rw [ReadWin.overlaps_win_one] at hov <;>
      obtain ⟨rfl, -, -⟩ := hov <;> simp [mulDriven] at hn'
  · -- `c[(k+1)*(N+1)] = 1'b0`
    intro k hk m lo w e h r hr hov
    simp only [cRowCell, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Expr2.reads] at hr
  · -- `t[(k+1)*N + j] = s[k*(N+1) + j+1] ^ pp[(k+1)*N + j]`
    intro k hk j hj m lo w e h r hr hov
    simp only [tCell, Process2.assign.injEq, Lhs2.slice.injEq] at h
    obtain ⟨⟨rfl, hlo, -⟩, rfl⟩ := h
    subst lo
    obtain ⟨e1, e2, e3, -⟩ := mul_expand k N
    have hdiv : ((k + 1) * N + j) / N = k + 1 := rowdiv hj
    simp [Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;> rw [ReadWin.overlaps_win_one] at hov <;>
      obtain ⟨rfl, h1, -⟩ := hov <;> simp [rkWin, hdiv] <;> omega
  · -- `s[(k+1)*(N+1) + j] = t[(k+1)*N + j] ^ c[(k+1)*(N+1) + j]`
    intro k hk j hj m lo w e h r hr hov
    simp only [sCell, Process2.assign.injEq, Lhs2.slice.injEq] at h
    obtain ⟨⟨rfl, hlo, -⟩, rfl⟩ := h
    subst lo
    obtain ⟨e1, e2, e3, -⟩ := mul_expand k N
    simp [Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;> rw [ReadWin.overlaps_win_one] at hov <;>
      obtain ⟨rfl, h1, -⟩ := hov
    · have hd := Nat.div_le_div_right (c := N) h1
      rw [rowdiv hj] at hd
      simp [rkWin]
      omega
    · simp [rkWin]
      omega
  · -- `c[(k+1)*(N+1) + j+1] = (s[k*(N+1) + j+1] & pp[..]) | (c[..+j] & t[..])`
    intro k hk j hj m lo w e h r hr hov
    simp only [cCell, Process2.assign.injEq, Lhs2.slice.injEq] at h
    obtain ⟨⟨rfl, hlo, -⟩, rfl⟩ := h
    subst lo
    obtain ⟨e1, e2, e3, -⟩ := mul_expand k N
    simp [Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rw [ReadWin.overlaps_win_one] at hov <;>
      obtain ⟨rfl, h1, -⟩ := hov
    · simp [rkWin]; omega
    · simp [rkWin]
    · simp [rkWin]; omega
    · have hd := Nat.div_le_div_right (c := N) h1
      rw [rowdiv hj] at hd
      simp [rkWin]
      omega
  · -- `s[(k+1)*(N+1) + N] = c[(k+1)*(N+1) + N]`
    intro k hk m lo w e h r hr hov
    simp only [sTopCell, Process2.assign.injEq, Lhs2.slice.injEq] at h
    obtain ⟨⟨rfl, hlo, -⟩, rfl⟩ := h
    subst lo
    simp [Expr2.reads, Expr2.sliceReads] at hr
    subst hr
    rw [ReadWin.overlaps_win_one] at hov
    obtain ⟨rfl, h1, -⟩ := hov
    simp [rkWin]
    omega
  · -- `p[i] = s[i*(N+1)]`
    intro i hi m lo w e h r hr hov
    simp only [outCell, Process2.assign.injEq, Lhs2.slice.injEq] at h
    obtain ⟨⟨rfl, hlo, -⟩, rfl⟩ := h
    subst lo
    obtain ⟨-, -, -, e4⟩ := mul_expand 0 N
    have hb := rowMajor_lt (K := N + 1) (c := 0) hi (by omega)
    simp [Expr2.reads, Expr2.sliceReads] at hr
    subst hr
    rw [ReadWin.overlaps_win_one] at hov
    obtain ⟨rfl, h1, -⟩ := hov
    simp [rkWin]
    omega

/-- **The multiplier is acyclic** (every `N ≥ 1`), with rank `mulRank`. -/
theorem mul_acyclic {N : Nat} (hN : 1 ≤ N) : Acyclic (design.sem N) := by
  refine ⟨mulRank N, ?_⟩
  intro i j ti ei tj ej wj hi hj hw ⟨r, hr, hov⟩
  obtain ⟨n', lo', w', rfl, hn'⟩ := mul_proc_slice hN hj
  obtain ⟨m, lo, w, rfl, -⟩ := mul_proc_slice hN hi
  simp only [Lhs2.wins_slice, List.mem_singleton] at hw
  subst hw
  have hrj : mulRank N j = rkWin N n' lo' := by simp only [mulRank, hj]
  have hri : mulRank N i = rkWin N m lo := by simp only [mulRank, hi]
  rw [hrj, hri]
  exact mul_reader hN hn' _ (mul_mem_of_getElem? hN hi) m lo w ei rfl r hr hov

/-! # Part 3. The settled state and the statement -/

/-! ## Reading windows of a settled state -/

section Gates

variable {st : SvState}

/-- An in-range part-select of a signal whose window is known (the rest of
the signal may be unknown). -/
theorem eval_sliceK {n : String} {u : LVec} {lo w : Nat} {x : BitVec w}
    (h : SvState.lookup st n = some u) (hk : u.extract lo w = LVec.ofBitVec x) :
    evalPure2 st (.slice (.ident n) lo w) = .ok (LVec.ofBitVec x) := by
  simp only [evalPure2_slice, evalPure2_ident_of_lookup h, Pure2.res_ok_bind, Pure2.res_pure_eq,
    hk]

/-- A bit-select of a known signal. -/
theorem eval_bitK {n : String} {w : Nat} {x : BitVec w} {i : Nat}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) (hi : i < w) :
    evalPure2 st (.slice (.ident n) i 1) = .ok (LVec.ofBitVec (BitVec.ofBool (x.getLsbD i))) :=
  evalPure2_bit_ofBitVec (evalPure2_ident_ofBitVec h) hi

/-- `1'b0`. -/
theorem eval_zero1 : evalPure2 st (.lit zero1) = .ok (LVec.ofBitVec (BitVec.ofBool false)) := by
  simp only [evalPure2_lit, zero1, LVec.ofNat_eq_ofBitVec]
  rfl

end Gates

/-- A window of a window. -/
theorem LVec_extract_extract (v : LVec) {lo w j k : Nat} (h : j + k ≤ w) :
    (v.extract lo w).extract j k = v.extract (lo + j) k := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  have hji : j + i < w := by omega
  simp only [LVec.getD_extract, hi, hji, if_true, Nat.add_assoc]

/-- A window all of whose bits are known is known. -/
theorem LVec_extract_eq_ofBitVec {v : LVec} {lo k : Nat} {x : BitVec k}
    (h : ∀ j, j < k → v.extract (lo + j) 1 = LVec.ofBitVec (BitVec.ofBool (x.getLsbD j))) :
    v.extract lo k = LVec.ofBitVec x :=
  LVec.eq_ofBitVec_of_extract_one (LVec.width_extract _ _ _) fun j hj => by
    rw [LVec_extract_extract _ (by omega)]
    exact h j hj

/-- A slice assign, read back on a state solving the equations. -/
theorem readback {d : Design2} {st : SvState} (heqs : CombEqs d st) {k : Nat} {n : String}
    {lo w : Nat} {e : Expr2} (hk : d.processes[k]? = some (.assign (.slice n lo w) e))
    {u : LVec} (hu : SvState.lookup st n = some u) {wv : Nat} {x : BitVec wv}
    (he : evalPure2 st e = .ok (LVec.ofBitVec x)) :
    u.extract lo w = LVec.ofBitVec (x.setWidth w) := by
  obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs hk he
  rw [hu, Option.some.injEq] at hold
  subst hold
  rw [hext, LVec.resizeU_ofBitVec]

/-- … for a 1-bit cell. -/
theorem readback1 {d : Design2} {st : SvState} (heqs : CombEqs d st) {k : Nat} {n : String}
    {lo : Nat} {e : Expr2} (hk : d.processes[k]? = some (.assign (.slice n lo 1) e))
    {u : LVec} (hu : SvState.lookup st n = some u) {b : Bool}
    (he : evalPure2 st e = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    u.extract lo 1 = LVec.ofBitVec (BitVec.ofBool b) := by
  rw [readback heqs hk hu he, BitVec.setWidth_eq]

/-- The carry cell `(x & y) | (c & (x ^ y))` is the majority. -/
theorem carry_gate (p q c : Bool) : ((p && q) || (c && (p ^^ q))) = Bool.atLeastTwo p q c := by
  cases p <;> cases q <;> cases c <;> rfl

/-- `y`'s bit `i` selects `x` or `0`. -/
theorem getLsbD_sel {N : Nat} (x : BitVec N) (b : Bool) (k : Nat) :
    (if b then x else 0#N).getLsbD k = (x.getLsbD k && b) := by
  cases b <;> simp

theorem toNat_sel {N : Nat} (x y : BitVec N) (i : Nat) :
    (if y.getLsbD i then x else 0#N).toNat = MulMath.addend x.toNat y.toNat i := by
  unfold MulMath.addend
  rw [BitVec.testBit_toNat]
  cases y.getLsbD i <;> simp

/-! ## The settled state -/

/-- **The multiplier, one settled state** (every `N ≥ 1`): in a state that
solves the design's equations and has the comb shape, known `x y : BitVec N`
on `a b` give the `2N`-bit product on `p`. Row by row: row `i`'s window of
`s` holds the row sum `R i` (`MulMath.R`), its carries are core's
`BitVec.carry` of the row's two addends; the low output bits are bit 0 of
each row, the high ones the upper bits of the last row (`MulMath`). -/
theorem mul_settled {N : Nat} (hN : 1 ≤ N) {st : SvState} (heqs : CombEqs (design.sem N) st)
    (hs : StateShape (design.sem N) st) {x y : BitVec N}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    SvState.lookup st "p" = some (LVec.ofBitVec (BitVec.ofNat (2 * N) (x.toNat * y.toNat))) := by
  have driven_of : ∀ {p : Process2} {n : String} {lo w : Nat} {e : Expr2}, p ∈ mulProcs N →
      p = .assign (.slice n lo w) e → Driven (design.sem N) n := by
    intro p n lo w e hp he
    obtain ⟨k, hk⟩ := mul_getElem?_of_mem hN hp
    subst he
    exact ⟨k, lo, w, _, _, hk, by simp⟩
  have hN0 : 0 < N := by omega
  obtain ⟨uPP, hPP, -⟩ := hs.driven "pp" (driven_of (mem_ppCell hN0 hN0) rfl)
  obtain ⟨uS, hS, -⟩ := hs.driven "s" (driven_of mem_s0Proc rfl)
  obtain ⟨uP, hP, hPw⟩ := hs.driven "p" (driven_of mem_pHiProc rfl)
  -- the partial products
  have hpp : ∀ i, i < N → ∀ j, j < N →
      uPP.extract (i * N + j) 1 = LVec.ofBitVec (BitVec.ofBool (x.getLsbD j && y.getLsbD i)) := by
    intro i hi j hj
    obtain ⟨k, hk⟩ := mul_getElem?_of_mem hN (mem_ppCell hi hj)
    have he := evalPure2_and_ofBitVec (eval_bitK ha hj) (eval_bitK hb hi)
    rw [BitVec.ofBool_and_ofBool] at he
    exact readback1 heqs hk hPP he
  -- the rows
  have hR := MulMath.R_le x.toNat y.toNat
  have hxlt := x.isLt
  have hrow : ∀ i, i < N → ∀ k, k ≤ N → uS.extract (i * (N + 1) + k) 1 =
      LVec.ofBitVec (BitVec.ofBool ((MulMath.R x.toNat y.toNat i).testBit k)) := by
    intro i
    induction i with
    | zero =>
      intro _ k hk
      -- row 0 is `{1'b0, pp[0]}`
      have hP0 : uPP.extract 0 N = LVec.ofBitVec (if y.getLsbD 0 then x else 0#N) :=
        LVec_extract_eq_ofBitVec fun j hj => by
          rw [getLsbD_sel, Nat.zero_add]
          have := hpp 0 hN0 j hj
          rwa [Nat.zero_mul, Nat.zero_add] at this
      obtain ⟨k0, hk0⟩ := mul_getElem?_of_mem hN (mem_s0Proc (N := N))
      have he := evalPure2_concat_ofBitVec (st := st) eval_zero1 (eval_sliceK hPP hP0)
      have h0 := readback heqs hk0 hS he
      rw [Nat.zero_mul, Nat.zero_add, ← Nat.zero_add k,
        ← LVec_extract_extract uS (lo := 0) (w := N + 1) (by omega), h0,
        LVec.extract_one_ofBitVec _ (by omega)]
      congr 3
      rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, MulMath.R, MulMath.addend,
        BitVec.testBit_toNat]
      by_cases hkN : k < N
      · rw [if_pos hkN, getLsbD_sel]
        cases y.getLsbD 0 <;> simp [hkN, BitVec.testBit_toNat, show k < N + 1 by omega]
      · have hkN' : k = N := by omega
        subst hkN'
        rw [if_neg hkN]
        cases y.getLsbD 0 <;> simp [Nat.testBit_lt_two_pow hxlt]
    | succ i ih =>
      intro hi k hk
      -- the two addends of row `i + 1`
      have hi' : i < N := by omega
      let Xr : BitVec N := BitVec.ofNat N (MulMath.R x.toNat y.toNat i / 2)
      let Yr : BitVec N := if y.getLsbD (i + 1) then x else 0#N
      have hXr : ∀ j, j < N → Xr.getLsbD j = (MulMath.R x.toNat y.toNat i).testBit (j + 1) := by
        intro j hj
        simp only [Xr, BitVec.getLsbD_ofNat, Nat.testBit_div_two, hj, decide_true, Bool.true_and]
      have hXrN : Xr.toNat = MulMath.R x.toNat y.toNat i / 2 := by
        simp only [Xr, BitVec.toNat_ofNat]
        apply Nat.mod_eq_of_lt
        have := hR i
        omega
      have hYrN : Yr.toNat = MulMath.addend x.toNat y.toNat (i + 1) := toNat_sel x y (i + 1)
      -- reads of row `i` (the IH) and of the partial products of row `i + 1`
      have hsr : ∀ j, j < N → uS.extract ((i + 1 - 1) * (N + 1) + (j + 1)) 1 =
          LVec.ofBitVec (BitVec.ofBool (Xr.getLsbD j)) := by
        intro j hj
        rw [Nat.add_sub_cancel, ih hi' (j + 1) (by omega), hXr j hj]
      have hppr : ∀ j, j < N → uPP.extract ((i + 1) * N + j) 1 =
          LVec.ofBitVec (BitVec.ofBool (Yr.getLsbD j)) := by
        intro j hj
        rw [hpp (i + 1) hi j hj, getLsbD_sel]
      obtain ⟨uT, hT, -⟩ := hs.driven "t" (driven_of (mem_tCell (k := i) hi hN0) rfl)
      obtain ⟨uC, hC, -⟩ := hs.driven "c" (driven_of (mem_cRowCell (k := i) hi) rfl)
      -- the propagates
      have ht : ∀ j, j < N → uT.extract ((i + 1) * N + j) 1 =
          LVec.ofBitVec (BitVec.ofBool (Xr.getLsbD j ^^ Yr.getLsbD j)) := by
        intro j hj
        obtain ⟨q, hq⟩ := mul_getElem?_of_mem hN (mem_tCell hi hj)
        have he := evalPure2_xor_ofBitVec (eval_sliceK hS (hsr j hj)) (eval_sliceK hPP (hppr j hj))
        rw [BitVec.ofBool_xor_ofBool] at he
        exact readback1 heqs hq hT he
      -- the carries, by induction on the bit
      have hc : ∀ j, j ≤ N → uC.extract ((i + 1) * (N + 1) + j) 1 =
          LVec.ofBitVec (BitVec.ofBool (BitVec.carry j Xr Yr false)) := by
        intro j
        induction j with
        | zero =>
          intro _
          obtain ⟨q, hq⟩ := mul_getElem?_of_mem hN (mem_cRowCell (k := i) hi)
          rw [Nat.add_zero, BitVec.carry_zero]
          exact readback1 heqs hq hC eval_zero1
        | succ j ihj =>
          intro hj
          obtain ⟨q, hq⟩ := mul_getElem?_of_mem hN (mem_cCell hi (j := j) (by omega))
          have he := evalPure2_or_ofBitVec
            (evalPure2_and_ofBitVec (eval_sliceK hS (hsr j (by omega)))
              (eval_sliceK hPP (hppr j (by omega))))
            (evalPure2_and_ofBitVec (eval_sliceK hC (ihj (by omega)))
              (eval_sliceK hT (ht j (by omega))))
          rw [BitVec.ofBool_and_ofBool, BitVec.ofBool_and_ofBool, BitVec.ofBool_or_ofBool,
            carry_gate, ← BitVec.carry_succ] at he
          exact readback1 heqs hq hC he
      -- the row sum
      have hsum : MulMath.R x.toNat y.toNat (i + 1) = Xr.toNat + Yr.toNat := by
        rw [hXrN, hYrN]
        rfl
      have hsumlt : Xr.toNat + Yr.toNat < 2 ^ (N + 1) := by
        rw [← hsum, Nat.pow_succ]
        have := hR (i + 1)
        omega
      by_cases hkN : k < N
      · obtain ⟨q, hq⟩ := mul_getElem?_of_mem hN (mem_sCell hi hkN)
        have he := evalPure2_xor_ofBitVec (eval_sliceK hT (ht k hkN)) (eval_sliceK hC (hc k hk))
        rw [BitVec.ofBool_xor_ofBool, Bool.xor_assoc, ← BitVec.getLsbD_add hkN] at he
        rw [readback1 heqs hq hS he, hsum, ← BitVec.testBit_toNat, BitVec.toNat_add,
          Nat.testBit_mod_two_pow]
        simp [hkN]
      · have hkN' : k = N := by omega
        subst hkN'
        obtain ⟨q, hq⟩ := mul_getElem?_of_mem hN (mem_sTopCell hi)
        have he := eval_sliceK hC (hc k hk)
        rw [readback1 heqs hq hS he, hsum, MulMath.testBit_top _ _ hsumlt, BitVec.carry_width]
        simp
  -- the outputs: the low half, bit 0 of each row
  have hlo : ∀ i, i < N → uP.extract i 1 =
      LVec.ofBitVec (BitVec.ofBool ((MulMath.R x.toNat y.toNat i).testBit 0)) := by
    intro i hi
    obtain ⟨q, hq⟩ := mul_getElem?_of_mem hN (mem_outCell hi)
    have := hrow i hi 0 (Nat.zero_le _)
    rw [Nat.add_zero] at this
    exact readback1 heqs hq hP (eval_sliceK hS this)
  -- the high half, the upper bits of the last row
  have hZ : uS.extract (N * N) N =
      LVec.ofBitVec (BitVec.ofNat N (MulMath.R x.toNat y.toNat (N - 1) / 2)) :=
    LVec_extract_eq_ofBitVec fun j hj => by
      have hidx : N * N + j = (N - 1) * (N + 1) + (j + 1) := by
        obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        grind
      rw [hidx, hrow (N - 1) (by omega) (j + 1) (by omega), BitVec.getLsbD_ofNat,
        Nat.testBit_div_two]
      simp [hj]
  have hhi : uP.extract N N =
      LVec.ofBitVec (BitVec.ofNat N (MulMath.R x.toNat y.toNat (N - 1) / 2)) := by
    obtain ⟨q, hq⟩ := mul_getElem?_of_mem hN (mem_pHiProc (N := N))
    rw [readback heqs hq hP (eval_sliceK hS hZ), BitVec.setWidth_eq]
  -- assemble `p`
  rw [mul_declWidth_p hN, Option.some.injEq] at hPw
  rw [hP]
  congr 1
  apply LVec.eq_ofBitVec_of_extract_one hPw.symm
  intro k hk
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and]
  by_cases hkN : k < N
  · rw [hlo k hkN, MulMath.testBit_mul_row]
  · obtain ⟨j, rfl⟩ : ∃ j, k = N + j := ⟨k - N, by omega⟩
    rw [MulMath.testBit_mul_top _ _ N j hN y.isLt,
      ← LVec_extract_extract uP (lo := N) (w := N) (j := j) (k := 1) (by omega), hhi,
      LVec.extract_one_ofBitVec _ (by omega), BitVec.getLsbD_ofNat, Nat.testBit_div_two]
    simp only [show j < N by omega, decide_true, Bool.true_and]

/-! ## The statement -/

theorem mul_interface (N : Nat) (hN : 1 ≤ N) :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by
  simp [CombTask.Interface, inputPorts, outputPorts, mul_sem_decls N hN, mulDecls,
    SvGolf.Tasks.Mul.task]

/-- **The reference solution**: the `mul` statement, for every `N ≥ 1`. -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  refine CombTask.satisfiedAt_of_comb (mul_interface N hN') (mul_comb hN') (mul_acyclic hN') ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  exact mul_settled hN' heqs hs hv.1 hv.2

end Submission

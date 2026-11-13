import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2

/-!
# Task `clmul`: the level-generate Karatsuba design `kara_lv.sv`, proved by hand

The design: operands zero-padded to `P = 4 * 2^L` bits, `L = $clog2((N + 3) / 4)` levels; level `l` holds
`3^l` nodes of width `W l = P >> l = 4 * 2^(L - l)` in one row of `av`, `bv` (operands) and `rv`
(products); children `3t`, `3t + 1`, `3t + 2` of node `t` take the low half, the high half and their
XOR; the base level `L` multiplies 4 x 4 bits by schoolbook; level `l < L` combines its children's
products column by column (`p = L + x^m (M + L + H) + x^2m H`).

The `sv_comb` tactics refuse the design (measured: `**` in the localparam `P`), so this file follows the
by-hand route of `tasks/add/reference/add_n_byhand.lean`, for every `N` with `1 ≤ N < 2^30`:

1. **The design at symbolic `N`** (`kara_instantiate2`, `kM_processes`): the envelope's templates pinned
   by `rfl`, every template instantiated at a symbolic node `(l, t)` (`>>`, `**` and 2-D indexed part
   selects at genvar arithmetic), the three generate items expanded (the node loop's bound `3 ** l`).
2. **The comb profile and acyclicity** (`kM_comb`, `kM_acyclic`, `kara_sem_eq`): every window lies in one
   row and one node slot; the rank is the operand row, then the base product row, then the product rows
   bottom up, then the output.
3. **The settled state** (`opd_inv`, `base_inv`, `prod_inv`, `kara_settled`): operand row `l` holds the
   operands `opd` of its nodes; product slot `t` of row `l` holds the carry-less product `cl` of node
   `(l, t)`'s operands (base level: seven column identities; every other level: one Karatsuba step,
   `colF_spec` from `comb_spec`); the output is the product of the padded operands, truncated
   (`cl_trunc`), which is the Spec's `coeff`.

The arithmetic of Part 3 is copied from `design/tasks-week2/clmul/karatsuba/Karatsuba.lean`.
No `sorry`, `native_decide` or `bv_decide`; the axioms are pinned at the end.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-! ## 1a. The envelope's shape (pinned by `rfl`) -/

abbrev gvl : PExpr := .genvarRef "l"
abbrev gvt : PExpr := .genvarRef "t"
abbrev prP : PExpr := .paramRef "P" none
abbrev prL : PExpr := .paramRef "L" none
abbrev prT : PExpr := .paramRef "T" none
abbrev eAdd (a b : PExpr) : PExpr := .binary (.m0 .add) a b
abbrev eSub (a b : PExpr) : PExpr := .binary (.m0 .sub) a b
abbrev eMul (a b : PExpr) : PExpr := .binary .mul a b
abbrev eShr (a b : PExpr) : PExpr := .binary .shr a b
abbrev eXor (a b : PExpr) : PExpr := .binary (.m0 .xor) a b
abbrev eAnd (a b : PExpr) : PExpr := .binary (.m0 .and) a b
/-- `l + 1` -/
abbrev l1T : PExpr := eAdd gvl (.int 1)
/-- `P >> (l+1)`, the half width `m` of a node of level `l` -/
abbrev hMT : PExpr := eShr prP l1T
/-- `P >> l`, the width `W` of a node of level `l` -/
abbrev hWT : PExpr := eShr prP gvl
abbrev t30 : PExpr := eMul (.int 3) gvt
abbrev t31 : PExpr := eAdd t30 (.int 1)
abbrev t32 : PExpr := eAdd t30 (.int 2)
/-- `t < 3 ** l` -/
abbrev nodeBound : PExpr := .binary .slt gvt (.binary .pow (.int 3) gvl)

/-- `v[l+1][(3t)*m +: m] = v[l][t*W +: m]` -/
def spLo (v : String) : PProcess :=
  .assignL (.arrayPart v [l1T] .up (eMul t30 hMT) hMT) (.arrayPart v [gvl] .up (eMul gvt hWT) hMT)
/-- `v[l+1][(3t+1)*m +: m] = v[l][t*W + m +: m]` -/
def spHi (v : String) : PProcess :=
  .assignL (.arrayPart v [l1T] .up (eMul t31 hMT) hMT)
    (.arrayPart v [gvl] .up (eAdd (eMul gvt hWT) hMT) hMT)
/-- `v[l+1][(3t+2)*m +: m] = v[l][t*W +: m] ^ v[l][t*W + m +: m]` -/
def spMid (v : String) : PProcess :=
  .assignL (.arrayPart v [l1T] .up (eMul t32 hMT) hMT)
    (eXor (.arrayPart v [gvl] .up (eMul gvt hWT) hMT)
      (.arrayPart v [gvl] .up (eAdd (eMul gvt hWT) hMT) hMT))

def splitNode : GenItem :=
  .genFor (some "g_node") "t" (.int 0) nodeBound (.unary .inc gvt) (some 1)
    ([spLo "av", spLo "bv", spHi "av", spHi "bv", spMid "av", spMid "bv"].map GenItem.process)

def splitGen : GenItem :=
  .genFor (some "g_split") "l" (.int 0) (.binary .slt gvl prL) (.unary .inc gvl) (some 2) [splitNode]

/-- `4*t + k` (`4*t` at `k = 0`) -/
def f4 : Nat → PExpr
  | 0 => eMul (.int 4) gvt
  | k + 1 => eAdd (eMul (.int 4) gvt) (.int ((k + 1 : Nat) : Int))
/-- `8*t + k` -/
def f8 : Nat → PExpr
  | 0 => eMul (.int 8) gvt
  | k + 1 => eAdd (eMul (.int 8) gvt) (.int ((k + 1 : Nat) : Int))
abbrev aE (k : Nat) : PExpr := .arrayElem "av" [prL, f4 k]
abbrev bE (k : Nat) : PExpr := .arrayElem "bv" [prL, f4 k]
abbrev pp (i j : Nat) : PExpr := eAnd (aE i) (bE j)
abbrev rT (k : Nat) : PLhs := .arrayElem "rv" [prL, f8 k]

def bs0 : PProcess := .assignL (rT 0) (pp 0 0)
def bs1 : PProcess := .assignL (rT 1) (eXor (pp 0 1) (pp 1 0))
def bs2 : PProcess := .assignL (rT 2) (eXor (eXor (pp 0 2) (pp 1 1)) (pp 2 0))
def bs3 : PProcess := .assignL (rT 3) (eXor (eXor (pp 0 3) (pp 1 2)) (eXor (pp 2 1) (pp 3 0)))
def bs4 : PProcess := .assignL (rT 4) (eXor (eXor (pp 1 3) (pp 2 2)) (pp 3 1))
def bs5 : PProcess := .assignL (rT 5) (eXor (pp 2 3) (pp 3 2))
def bs6 : PProcess := .assignL (rT 6) (pp 3 3)

def baseGen : GenItem :=
  .genFor (some "g_base") "t" (.int 0) (.binary .slt gvt prT) (.unary .inc gvt) (some 9)
    ([bs0, bs1, bs2, bs3, bs4, bs5, bs6].map GenItem.process)

/-- `t*2*W` -/
abbrev s2T : PExpr := eMul (eMul gvt (.int 2)) hWT
abbrev c0T : PExpr := eMul t30 hWT
abbrev c1T : PExpr := eMul t31 hWT
abbrev c2T : PExpr := eMul t32 hWT
abbrev mm1T : PExpr := eSub hMT (.int 1)
abbrev rP (lo w : PExpr) : PExpr := .arrayPart "rv" [l1T] .up lo w
abbrev rEl (idx : PExpr) : PExpr := .arrayElem "rv" [l1T, idx]

def cb0 : PProcess := .assignL (.arrayPart "rv" [gvl] .up s2T hMT) (rP c0T hMT)
def cb1 : PProcess := .assignL (.arrayPart "rv" [gvl] .up (eAdd s2T hMT) mm1T)
    (eXor (eXor (rP c0T mm1T) (rP (eAdd c0T hMT) mm1T)) (eXor (rP c1T mm1T) (rP c2T mm1T)))
def cb2 : PProcess := .assignL (.arrayElem "rv" [gvl, eSub (eAdd s2T hWT) (.int 1)])
    (eXor (eXor (rEl (eSub (eAdd c0T hMT) (.int 1))) (rEl (eSub (eAdd c1T hMT) (.int 1))))
      (rEl (eSub (eAdd c2T hMT) (.int 1))))
def cb3 : PProcess := .assignL (.arrayPart "rv" [gvl] .up (eAdd s2T hWT) mm1T)
    (eXor (eXor (rP (eAdd c0T hMT) mm1T) (rP c1T mm1T))
      (eXor (rP (eAdd c1T hMT) mm1T) (rP (eAdd c2T hMT) mm1T)))
def cb4 : PProcess := .assignL (.arrayPart "rv" [gvl] .up (eSub (eAdd (eAdd s2T hWT) hMT) (.int 1)) hMT)
    (rP (eSub (eAdd c1T hMT) (.int 1)) hMT)

def combNode : GenItem :=
  .genFor (some "g_node") "t" (.int 0) nodeBound (.unary .inc gvt) (some 1)
    ([cb0, cb1, cb2, cb3, cb4].map GenItem.process)

def combGen : GenItem :=
  .genFor (some "g_comb") "l" (.int 0) (.binary .slt gvl prL) (.unary .inc gvl) (some 2) [combNode]

theorem kara_generates : design.pdesign.generates = [splitGen, baseGen, combGen] := rfl

def st0 : PProcess := .assignL (.arrayElem "av" [.int 0]) (.resize 36 (.ident "a"))
def st1 : PProcess := .assignL (.arrayElem "bv" [.int 0]) (.resize 36 (.ident "b"))
def st2 : PProcess :=
  .assign "p" (.arrayPart "rv" [.int 0] .range (eSub (eMul (.int 2) (.paramRef "N" none)) (.int 2)) (.int 0))

theorem kara_static_source : design.pdesign.processes = [st0, st1, st2] := rfl

theorem kara_others : design.pdesign.others = [] := rfl

/-! ## 1b. The constants and the arithmetic of the geometry -/

/-- The number of levels, `L = $clog2((N + 3) / 4)`. -/
def KL (N : Nat) : Nat := clog2 ((N + 3) / 4)
/-- The width of a node of level `l`: `P >> l = 4 * 2^(L - l)`. -/
def KW (L l : Nat) : Nat := 4 * 2 ^ (L - l)
/-- The width of an operand row: `4 * T = 4 * 3^L`. -/
def KR (L : Nat) : Nat := 4 * 3 ^ L
/-- The width of a product row: `8 * T = 8 * 3^L`. -/
def KS (L : Nat) : Nat := 8 * 3 ^ L

theorem KW_pos (L l : Nat) : 4 ≤ KW L l := by
  unfold KW
  have := Nat.two_pow_pos (L - l)
  omega

theorem KW_succ {L l : Nat} (hl : l < L) : KW L l = 2 * KW L (l + 1) := by
  unfold KW
  have h : L - l = (L - (l + 1)) + 1 := by omega
  rw [h, Nat.pow_succ]
  omega

theorem pow_le_three {L l : Nat} (hl : l ≤ L) : 3 ^ l * 2 ^ (L - l) ≤ 3 ^ L := by
  have h1 : 2 ^ (L - l) ≤ 3 ^ (L - l) := Nat.pow_le_pow_left (by decide) _
  have h2 : 3 ^ L = 3 ^ l * 3 ^ (L - l) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hl]
  rw [h2]
  exact Nat.mul_le_mul_left _ h1

/-- Node `t` of level `l` lies inside an operand row: `(t + 1) * W ≤ 4 * 3^L`. -/
theorem node_fits {L l t : Nat} (hl : l ≤ L) (ht : t < 3 ^ l) : (t + 1) * KW L l ≤ KR L := by
  unfold KW KR
  have h := pow_le_three hl
  have h3 : (t + 1) * (4 * 2 ^ (L - l)) ≤ 3 ^ l * (4 * 2 ^ (L - l)) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : 3 ^ l * (4 * 2 ^ (L - l)) = 4 * (3 ^ l * 2 ^ (L - l)) := by rw [Nat.mul_left_comm]
  omega

/-! ## 1c. What the templates read from an environment -/

structure KEnv (E : IEnv) (N L : Nat) : Prop where
  hN : E.vals.lookup "N" = some (N : Int)
  hL : E.vals.lookup "L" = some (L : Int)
  hP : E.vals.lookup "P" = some ((4 * 2 ^ L : Nat) : Int)
  hT : E.vals.lookup "T" = some ((3 ^ L : Nat) : Int)
  hav : E.dims.lookup "av" = some [((L : Int), 0), ((KR L : Int) - 1, 0)]
  hbv : E.dims.lookup "bv" = some [((L : Int), 0), ((KR L : Int) - 1, 0)]
  hrv : E.dims.lookup "rv" = some [((L : Int), 0), ((KS L : Int) - 1, 0)]

theorem KEnv.bind {E : IEnv} {N L : Nat} (h : KEnv E N L) (g : String) (h1 : g ≠ "N")
    (h2 : g ≠ "L") (h3 : g ≠ "P") (h4 : g ≠ "T") (v : Int) : KEnv (E.bindVal g v) N L where
  hN := by rw [vals_lookup_bindVal_ne v (Ne.symm h1)]; exact h.hN
  hL := by rw [vals_lookup_bindVal_ne v (Ne.symm h2)]; exact h.hL
  hP := by rw [vals_lookup_bindVal_ne v (Ne.symm h3)]; exact h.hP
  hT := by rw [vals_lookup_bindVal_ne v (Ne.symm h4)]; exact h.hT
  hav := by simpa using h.hav
  hbv := by simpa using h.hbv
  hrv := by simpa using h.hrv

theorem KEnv.withDecls {E : IEnv} {N L : Nat} (h : KEnv E N L) (decls : List Decl) :
    KEnv (E.withDecls decls) N L where
  hN := by simpa using h.hN
  hL := by simpa using h.hL
  hP := by simpa using h.hP
  hT := by simpa using h.hT
  hav := by simpa using h.hav
  hbv := by simpa using h.hbv
  hrv := by simpa using h.hrv

/-! ## 1d. Constant evaluation: `>>` and `**` (the library has `+ - *`) -/

theorem evalInt_shr_of {env : IEnv} {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    evalInt env (.binary .shr l r) = .ok (a.tdiv (2 ^ b.toNat)) := by
  have ha' : ¬ a < 0 := Int.not_lt.mpr ha
  have hb' : ¬ b < 0 := Int.not_lt.mpr hb
  simp [evalInt, hil, hir, hl, hr, ha', hb', Gen2.except_ok_bind]

theorem evalInt_pow_of {env : IEnv} {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) (hb : 0 ≤ b) :
    evalInt env (.binary .pow l r) = .ok (a ^ b.toNat) := by
  have hb' : ¬ b < 0 := Int.not_lt.mpr hb
  simp [evalInt, hil, hir, hl, hr, hb', Gen2.except_ok_bind]

/-- `(4 * 2^L) >> l = W l` for `l ≤ L` (on naturals, `Int.tdiv` is `/`). -/
theorem tdiv_KW {L l : Nat} (hl : l ≤ L) :
    ((4 * 2 ^ L : Nat) : Int).tdiv (2 ^ ((l : Int).toNat)) = ((KW L l : Nat) : Int) := by
  rw [Int.toNat_natCast]
  have h : 4 * 2 ^ L = KW L l * 2 ^ l := by
    unfold KW
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hl]
  rw [h, show ((2 : Int) ^ l) = ((2 ^ l : Nat) : Int) by norm_cast]
  show (((KW L l * 2 ^ l / 2 ^ l : Nat)) : Int) = _
  rw [Nat.mul_div_cancel _ (Nat.two_pow_pos l)]

/-! ## 1e. The environment of one node `(l, t)` -/

abbrev nodeEnv (E : IEnv) (l t : Nat) : IEnv := (E.bindVal "l" (l : Int)).bindVal "t" (t : Int)

theorem nd_t (E : IEnv) (l t : Nat) : evalInt (nodeEnv E l t) gvt = .ok (t : Int) :=
  evalInt_genvarRef_of (by simp)

theorem nd_l (E : IEnv) (l t : Nat) : evalInt (nodeEnv E l t) gvl = .ok (l : Int) :=
  evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])

theorem nd_l1 (E : IEnv) (l t : Nat) : evalInt (nodeEnv E l t) l1T = .ok ((l + 1 : Nat) : Int) := by
  rw [l1T, eAdd, evalInt_add_of rfl rfl (nd_l E l t) (evalInt_int 1)]
  push_cast
  rfl

section node

variable {E : IEnv} {N L : Nat} (hE : KEnv E N L)
include hE

theorem nd_env (l t : Nat) : KEnv (nodeEnv E l t) N L :=
  (hE.bind "l" (by decide) (by decide) (by decide) (by decide) _).bind "t" (by decide) (by decide)
    (by decide) (by decide) _

theorem nd_int_P (l t : Nat) : prP.isInt (nodeEnv E l t) = true := isInt_paramRef_of (nd_env hE l t).hP

theorem nd_W {l t : Nat} (hl : l ≤ L) : evalInt (nodeEnv E l t) hWT = .ok ((KW L l : Nat) : Int) := by
  rw [hWT, eShr, evalInt_shr_of (nd_int_P hE l t) rfl (evalInt_paramRef_of (nd_env hE l t).hP)
    (nd_l E l t) (by omega) (by omega), tdiv_KW hl]

theorem nd_M {l t : Nat} (hl : l < L) :
    evalInt (nodeEnv E l t) hMT = .ok ((KW L (l + 1) : Nat) : Int) := by
  rw [hMT, eShr, evalInt_shr_of (nd_int_P hE l t) rfl (evalInt_paramRef_of (nd_env hE l t).hP)
    (nd_l1 E l t) (by omega) (by omega), tdiv_KW (by omega)]

theorem nd_int_W (l t : Nat) : hWT.isInt (nodeEnv E l t) = true :=
  isInt_binary_of rfl (nd_int_P hE l t) rfl

theorem nd_int_M (l t : Nat) : hMT.isInt (nodeEnv E l t) = true :=
  isInt_binary_of rfl (nd_int_P hE l t) rfl

theorem nd_t30 (l t : Nat) : evalInt (nodeEnv E l t) t30 = .ok ((3 * t + 0 : Nat) : Int) := by
  rw [t30, eMul, evalInt_mul_of rfl rfl (evalInt_int 3) (nd_t E l t)]
  push_cast
  rfl

theorem nd_t31 (l t : Nat) : evalInt (nodeEnv E l t) t31 = .ok ((3 * t + 1 : Nat) : Int) := by
  rw [t31, eAdd, t30, eMul, evalInt_add_of rfl rfl
    (evalInt_mul_of rfl rfl (evalInt_int 3) (nd_t E l t)) (evalInt_int 1)]
  push_cast
  rfl

theorem nd_t32 (l t : Nat) : evalInt (nodeEnv E l t) t32 = .ok ((3 * t + 2 : Nat) : Int) := by
  rw [t32, eAdd, t30, eMul, evalInt_add_of rfl rfl
    (evalInt_mul_of rfl rfl (evalInt_int 3) (nd_t E l t)) (evalInt_int 2)]
  push_cast
  rfl

/-- `(3t + c) * m` -/
theorem nd_cM {l t : Nat} (hl : l < L) {e : PExpr} {c : Nat} (hei : e.isInt (nodeEnv E l t) = true)
    (he : evalInt (nodeEnv E l t) e = .ok ((3 * t + c : Nat) : Int)) :
    evalInt (nodeEnv E l t) (eMul e hMT) = .ok (((3 * t + c) * KW L (l + 1) : Nat) : Int) := by
  rw [eMul, evalInt_mul_of hei (nd_int_M hE l t) he (nd_M hE hl)]
  push_cast
  rfl

/-- `t * W` -/
theorem nd_tW {l t : Nat} (hl : l ≤ L) :
    evalInt (nodeEnv E l t) (eMul gvt hWT) = .ok ((t * KW L l : Nat) : Int) := by
  rw [eMul, evalInt_mul_of rfl (nd_int_W hE l t) (nd_t E l t) (nd_W hE hl)]
  push_cast
  rfl

/-- `t * W + m` -/
theorem nd_tWM {l t : Nat} (hl : l < L) :
    evalInt (nodeEnv E l t) (eAdd (eMul gvt hWT) hMT) = .ok ((t * KW L l + KW L (l + 1) : Nat) : Int) := by
  rw [eAdd, evalInt_add_of (isInt_binary_of rfl rfl (nd_int_W hE l t)) (nd_int_M hE l t) (nd_tW hE (by omega))
    (nd_M hE hl)]
  push_cast
  rfl

end node

/-! ## 1f. Selects of a 2-D `[A:0][B-1:0]` array at symbolic labels -/

section sel

variable {env : IEnv} {elems : List (String × Nat)}

theorem dimCount_B {B : Nat} (hB : 1 ≤ B) : dimCount ((B : Int) - 1) 0 = B := by
  have h := dimCount_desc0 (show (0 : Int) ≤ (B : Int) - 1 by omega)
  omega

theorem part2_geom {n : String} {ie a b : PExpr} {A B i k w : Nat}
    (hd : env.dims.lookup n = some [((A : Int), 0), ((B : Int) - 1, 0)]) (hB : 1 ≤ B)
    (hi : evalInt env ie = .ok (i : Int)) (hiA : i ≤ A)
    (ha : evalInt env a = .ok (k : Int)) (hb : evalInt env b = .ok (w : Int)) (hw : 0 < w) :
    arrayPartGeom env n [ie] .up a b =
      .ok ((i : Int) * (B : Int), true, 1, B, (k : Int), (k : Int) + w - 1) := by
  have hbm : (0 : Int) ≤ (B : Int) - 1 := by omega
  have hwk := walkIndices_desc0_cons (env := env) (ds := [((B : Int) - 1, 0)]) (m := (A : Int))
    (by omega) hi (by omega) (by omega) (walkIndices_nil (env := env) [((B : Int) - 1, 0)])
  have hmin : min ((k : Int) + w - 1) (k : Int) = k := Int.min_eq_right (by omega)
  have hmax : max ((k : Int) + w - 1) (k : Int) = (k : Int) + w - 1 := Int.max_eq_left (by omega)
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hw' : (0 : Int) < (w : Int) := by omega
  have hc := dimCount_B hB
  simp [arrayPartGeom, arrayDims_of hd, hwk, partLabels, ha, hb, hw, hw', labelOffset_desc0 hbm,
    hmin, hmax, hmode, Gen2.except_ok_bind, dimsStride_cons, hc]

theorem part2_read {n : String} {ie a b : PExpr} {A B i k w : Nat}
    (hd : env.dims.lookup n = some [((A : Int), 0), ((B : Int) - 1, 0)]) (hB : 1 ≤ B)
    (hi : evalInt env ie = .ok (i : Int)) (hiA : i ≤ A)
    (ha : evalInt env a = .ok (k : Int)) (hb : evalInt env b = .ok (w : Int)) (hw : 0 < w)
    (hkw : k + w ≤ B) :
    fitExpr2 env elems (some w) (.arrayPart n [ie] .up a b) = .slice (.ident n) (i * B + k) w := by
  have hg := part2_geom hd hB hi hiA ha hb hw
  have hs := selfWidth2_arrayPart_of (elems := elems) hg
  have hw1 : ((k : Int) + w - 1 - k + 1).toNat * 1 = w := by omega
  rw [hw1] at hs
  rw [fitExpr2_of_rigid_eq rfl hs, instExpr2_arrayPart _ (dynPartPlan_of_geom hg),
    arrayPartRead_of_inRange hg (by omega) (by omega), hw1]
  congr 1
  rw [show (i : Int) * (B : Int) + (k : Int) * ((1 : Nat) : Int) = ((i * B + k : Nat) : Int) by
    push_cast; omega, Int.toNat_natCast]

theorem part2_tgt {n : String} {ie a b : PExpr} {A B i k w : Nat}
    (hd : env.dims.lookup n = some [((A : Int), 0), ((B : Int) - 1, 0)]) (hB : 1 ≤ B)
    (hi : evalInt env ie = .ok (i : Int)) (hiA : i ≤ A)
    (ha : evalInt env a = .ok (k : Int)) (hb : evalInt env b = .ok (w : Int)) (hw : 0 < w)
    (hkw : k + w ≤ B) :
    instLhs2 env elems (.arrayPart n [ie] .up a b) = .ok (.slice n (i * B + k) w, w) := by
  have hg := part2_geom hd hB hi hiA ha hb hw
  have hw1 : ((k : Int) + w - 1 - k + 1).toNat * 1 = w := by omega
  rw [instLhs2_arrayPart, arrayPartTarget_of_inRange hg (by omega) (by omega), hw1]
  rw [show (i : Int) * (B : Int) + (k : Int) * ((1 : Nat) : Int) = ((i * B + k : Nat) : Int) by
    push_cast; omega, Int.toNat_natCast]

theorem elem2_win {n : String} {ie je : PExpr} {A B i j : Nat}
    (hd : env.dims.lookup n = some [((A : Int), 0), ((B : Int) - 1, 0)]) (hB : 1 ≤ B)
    (hi : evalInt env ie = .ok (i : Int)) (hiA : i ≤ A)
    (hj : evalInt env je = .ok (j : Int)) (hjB : j < B) :
    arrayElemWindow env n [ie, je] = .ok (((i * B + j : Nat) : Int), 1, true) := by
  rw [arrayElemWindow_desc0_2 hd (by omega) (by omega) hi (by omega) (by omega) hj (by omega) (by omega)]
  congr 2
  rw [Int.sub_add_cancel]
  push_cast
  rfl

theorem elem2_read {n : String} {ie je : PExpr} {A B i j : Nat}
    (hd : env.dims.lookup n = some [((A : Int), 0), ((B : Int) - 1, 0)]) (hB : 1 ≤ B)
    (hi : evalInt env ie = .ok (i : Int)) (hiA : i ≤ A)
    (hj : evalInt env je = .ok (j : Int)) (hjB : j < B) :
    fitExpr2 env elems (some 1) (.arrayElem n [ie, je]) = .slice (.ident n) (i * B + j) 1 := by
  have hw := elem2_win hd hB hi hiA hj hjB
  rw [fitExpr2_arrayElem_of hw, arrayElemRead_of_inRange hw, Int.toNat_natCast]

theorem elem2_tgt {n : String} {ie je : PExpr} {A B i j : Nat}
    (hd : env.dims.lookup n = some [((A : Int), 0), ((B : Int) - 1, 0)]) (hB : 1 ≤ B)
    (hi : evalInt env ie = .ok (i : Int)) (hiA : i ≤ A)
    (hj : evalInt env je = .ok (j : Int)) (hjB : j < B) :
    instLhs2 env elems (.arrayElem n [ie, je]) = .ok (.slice n (i * B + j) 1, 1) := by
  rw [instLhs2_arrayElem, arrayElemTarget_of_inRange (elem2_win hd hB hi hiA hj hjB), Int.toNat_natCast]

end sel

/-! ## 1g. The split family: the operands of the three children of node `(l, t)` -/

def spLoP (v : String) (L l t : Nat) : Process2 :=
  .assign (.slice v ((l + 1) * KR L + (3 * t + 0) * KW L (l + 1)) (KW L (l + 1)))
    (.slice (.ident v) (l * KR L + t * KW L l) (KW L (l + 1)))
def spHiP (v : String) (L l t : Nat) : Process2 :=
  .assign (.slice v ((l + 1) * KR L + (3 * t + 1) * KW L (l + 1)) (KW L (l + 1)))
    (.slice (.ident v) (l * KR L + (t * KW L l + KW L (l + 1))) (KW L (l + 1)))
def spMidP (v : String) (L l t : Nat) : Process2 :=
  .assign (.slice v ((l + 1) * KR L + (3 * t + 2) * KW L (l + 1)) (KW L (l + 1)))
    (.binary .xor (.slice (.ident v) (l * KR L + t * KW L l) (KW L (l + 1)))
      (.slice (.ident v) (l * KR L + (t * KW L l + KW L (l + 1))) (KW L (l + 1))))

def splitP (L l t : Nat) : List Process2 :=
  [spLoP "av" L l t, spLoP "bv" L l t, spHiP "av" L l t, spHiP "bv" L l t, spMidP "av" L l t,
    spMidP "bv" L l t]

theorem KR_pos (L : Nat) : 1 ≤ KR L := by
  unfold KR
  have : 3 ^ L ≠ 0 := by simp
  omega

/-- The in-range facts of node `(l, t)` of a split level `l < L`. -/
theorem split_fits {L l t : Nat} (hl : l < L) (ht : t < 3 ^ l) (c : Nat) (hc : c ≤ 2) :
    (3 * t + c) * KW L (l + 1) + KW L (l + 1) ≤ KR L ∧ t * KW L l + KW L (l + 1) + KW L (l + 1) ≤ KR L := by
  have h1 := node_fits (L := L) (l := l + 1) (t := 3 * t + 2) (by omega)
    (by rw [Nat.pow_succ]; omega)
  have h2 := node_fits (L := L) (l := l) (t := t) (by omega) ht
  have hw := KW_succ hl
  constructor
  · have : (3 * t + c) * KW L (l + 1) + KW L (l + 1) = (3 * t + c + 1) * KW L (l + 1) :=
      (Nat.succ_mul _ _).symm
    rw [this]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) h1
  · have : (t + 1) * KW L l = t * KW L l + KW L l := Nat.succ_mul _ _
    omega

section split

variable {E : IEnv} {elems : List (String × Nat)} {N L : Nat} (hE : KEnv E N L)
include hE

theorem spLo_inst (v : String) (hv : E.dims.lookup v = some [((L : Int), 0), ((KR L : Int) - 1, 0)])
    {l t : Nat} (hl : l < L) (ht : t < 3 ^ l) :
    instProcess2 (nodeEnv E l t) elems (spLo v) = spLoP v L l t := by
  have hv' : (nodeEnv E l t).dims.lookup v = some [((L : Int), 0), ((KR L : Int) - 1, 0)] := by
    simpa using hv
  obtain ⟨hf1, hf2⟩ := split_fits hl ht 0 (by omega)
  have hm := KW_pos L (l + 1)
  rw [spLo, instProcess2_assignL _ (part2_tgt hv' (KR_pos L) (nd_l1 E l t) (by omega)
      (nd_cM hE hl rfl (nd_t30 hE l t)) (nd_M hE hl) (by omega) hf1),
    part2_read hv' (KR_pos L) (nd_l E l t) (by omega) (nd_tW hE (by omega)) (nd_M hE hl) (by omega)
      (by omega)]
  rfl

theorem spHi_inst (v : String) (hv : E.dims.lookup v = some [((L : Int), 0), ((KR L : Int) - 1, 0)])
    {l t : Nat} (hl : l < L) (ht : t < 3 ^ l) :
    instProcess2 (nodeEnv E l t) elems (spHi v) = spHiP v L l t := by
  have hv' : (nodeEnv E l t).dims.lookup v = some [((L : Int), 0), ((KR L : Int) - 1, 0)] := by
    simpa using hv
  obtain ⟨hf1, hf2⟩ := split_fits hl ht 1 (by omega)
  have hm := KW_pos L (l + 1)
  rw [spHi, instProcess2_assignL _ (part2_tgt hv' (KR_pos L) (nd_l1 E l t) (by omega)
      (nd_cM hE hl rfl (nd_t31 hE l t)) (nd_M hE hl) (by omega) hf1),
    part2_read hv' (KR_pos L) (nd_l E l t) (by omega) (nd_tWM hE hl) (nd_M hE hl) (by omega)
      (by omega)]
  rfl

theorem spMid_inst (v : String) (hv : E.dims.lookup v = some [((L : Int), 0), ((KR L : Int) - 1, 0)])
    {l t : Nat} (hl : l < L) (ht : t < 3 ^ l) :
    instProcess2 (nodeEnv E l t) elems (spMid v) = spMidP v L l t := by
  have hv' : (nodeEnv E l t).dims.lookup v = some [((L : Int), 0), ((KR L : Int) - 1, 0)] := by
    simpa using hv
  obtain ⟨hf1, hf2⟩ := split_fits hl ht 2 (by omega)
  have hm := KW_pos L (l + 1)
  rw [spMid, instProcess2_assignL _ (part2_tgt hv' (KR_pos L) (nd_l1 E l t) (by omega)
      (nd_cM hE hl rfl (nd_t32 hE l t)) (nd_M hE hl) (by omega) hf1), eXor, fitExpr2_binary, instExpr2_xor,
    part2_read hv' (KR_pos L) (nd_l E l t) (by omega) (nd_tW hE (by omega)) (nd_M hE hl) (by omega)
      (by omega),
    part2_read hv' (KR_pos L) (nd_l E l t) (by omega) (nd_tWM hE hl) (nd_M hE hl) (by omega)
      (by omega)]
  rfl

end split

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **The split item expanded at symbolic `N`**: for every level `l < L` and node `t < 3^l`, the six
operand assigns of the node's children. -/
theorem split_expand {E : IEnv} {elems : List (String × Nat)} {N L F : Nat} (hE : KEnv E N L)
    (hF : 3 ^ L < F) (hLF : L < F) :
    splitGen.expand2 E elems F =
      .ok ((List.range L).flatMap fun l => (List.range (3 ^ l)).flatMap fun t => splitP L l t) := by
  have hb : ∀ v : Int, KEnv (E.bindVal "l" v) N L :=
    fun v => hE.bind "l" (by decide) (by decide) (by decide) (by decide) v
  simp only [splitGen, gvl, prL]
  rw [GenItem.expand2_genFor_ascending_flatMap (N := (L : Int))
    (f := fun v => (List.range (3 ^ v.toNat)).flatMap fun t => splitP L v.toNat t) (evalInt_int 0)
    (fun v => isInt_paramRef_of (hb v).hL) (fun v => evalInt_paramRef_of (hb v).hL) (by simpa using hLF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast]
  · intro v hv0 hvL
    obtain ⟨l, rfl⟩ : ∃ l : Nat, v = (l : Int) := ⟨v.toNat, by omega⟩
    have hl : l < L := by omega
    simp only [Int.toNat_natCast]
    apply expandList2_singleton_ok
    have hpow : ∀ w : Int, evalInt ((E.bindVal "l" (l : Int)).bindVal "t" w)
        (.binary .pow (.int 3) gvl) = .ok ((3 ^ l : Nat) : Int) := by
      intro w
      rw [evalInt_pow_of rfl rfl (evalInt_int 3)
        (evalInt_genvarRef_of (v := (l : Int)) (by simp [IEnv.bindVal, List.lookup])) (by omega),
        Int.toNat_natCast]
      push_cast
      rfl
    have h3 : 3 ^ l ≤ 3 ^ L := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hl)
    simp only [splitNode, nodeBound, gvt, gvl]
    rw [GenItem.expand2_genFor_ascending_processes (N := ((3 ^ l : Nat) : Int))
      (evalInt_int 0) (fun w => rfl) hpow
      (by rw [Int.sub_zero, Int.toNat_natCast]; omega)]
    simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast]
    congr 1
    apply flatMap_congr'
    intro t ht
    have ht' := List.mem_range.mp ht
    simp only [List.map_cons, List.map_nil]
    rw [spLo_inst hE "av" hE.hav hl ht', spLo_inst hE "bv" hE.hbv hl ht', spHi_inst hE "av" hE.hav hl ht',
      spHi_inst hE "bv" hE.hbv hl ht', spMid_inst hE "av" hE.hav hl ht', spMid_inst hE "bv" hE.hbv hl ht']
    rfl

/-! ## 1h. A small toolkit: INT-class expressions with a natural value -/

/-- `e` is in the INT class at `env` and evaluates to the natural number `n`. -/
structure EvN (env : IEnv) (e : PExpr) (n : Nat) : Prop where
  isInt : e.isInt env = true
  ev : evalInt env e = .ok (n : Int)

theorem EvN.add {env : IEnv} {e₁ e₂ : PExpr} {a b : Nat} (h₁ : EvN env e₁ a) (h₂ : EvN env e₂ b) :
    EvN env (eAdd e₁ e₂) (a + b) :=
  ⟨isInt_binary_of rfl h₁.isInt h₂.isInt, by
    rw [eAdd, evalInt_add_of h₁.isInt h₂.isInt h₁.ev h₂.ev]
    push_cast
    rfl⟩

theorem EvN.mul {env : IEnv} {e₁ e₂ : PExpr} {a b : Nat} (h₁ : EvN env e₁ a) (h₂ : EvN env e₂ b) :
    EvN env (eMul e₁ e₂) (a * b) :=
  ⟨isInt_binary_of rfl h₁.isInt h₂.isInt, by
    rw [eMul, evalInt_mul_of h₁.isInt h₂.isInt h₁.ev h₂.ev]
    push_cast
    rfl⟩

theorem EvN.sub1 {env : IEnv} {e : PExpr} {a : Nat} (h : EvN env e a) (ha : 1 ≤ a) :
    EvN env (eSub e (.int 1)) (a - 1) :=
  ⟨isInt_binary_of rfl h.isInt rfl, by
    rw [eSub, evalInt_sub_of h.isInt rfl h.ev (evalInt_int 1)]
    congr 1
    omega⟩

theorem EvN.int (env : IEnv) (k : Nat) : EvN env (.int (k : Int)) k := ⟨rfl, rfl⟩

theorem EvN.gv {env : IEnv} {g : String} {v : Nat} (h : env.vals.lookup g = some (v : Int)) :
    EvN env (.genvarRef g) v := ⟨rfl, evalInt_genvarRef_of h⟩

theorem EvN.par {env : IEnv} {n : String} {v : Nat} (h : env.vals.lookup n = some (v : Int)) :
    EvN env (.paramRef n none) v := ⟨isInt_paramRef_of h, evalInt_paramRef_of h⟩

/-! ## 1i. The base family: a 4 x 4 schoolbook product per node `t` of level `L` -/

theorem bs_f4 (E : IEnv) (t k : Nat) :
    EvN (E.bindVal "t" (t : Int)) (f4 k) (4 * t + k) := by
  have ht : EvN (E.bindVal "t" (t : Int)) gvt t := EvN.gv (by simp)
  cases k with
  | zero =>
    have h := (EvN.int (E.bindVal "t" (t : Int)) 4).mul ht
    exact ⟨h.isInt, by rw [f4]; exact h.ev⟩
  | succ k =>
    have h := ((EvN.int (E.bindVal "t" (t : Int)) 4).mul ht).add (EvN.int _ (k + 1))
    exact ⟨h.isInt, by rw [f4]; exact h.ev⟩

theorem bs_f8 (E : IEnv) (t k : Nat) :
    EvN (E.bindVal "t" (t : Int)) (f8 k) (8 * t + k) := by
  have ht : EvN (E.bindVal "t" (t : Int)) gvt t := EvN.gv (by simp)
  cases k with
  | zero =>
    have h := (EvN.int (E.bindVal "t" (t : Int)) 8).mul ht
    exact ⟨h.isInt, by rw [f8]; exact h.ev⟩
  | succ k =>
    have h := ((EvN.int (E.bindVal "t" (t : Int)) 8).mul ht).add (EvN.int _ (k + 1))
    exact ⟨h.isInt, by rw [f8]; exact h.ev⟩

abbrev aSl (L t k : Nat) : Expr2 := .slice (.ident "av") (L * KR L + (4 * t + k)) 1
abbrev bSl (L t k : Nat) : Expr2 := .slice (.ident "bv") (L * KR L + (4 * t + k)) 1
abbrev ppP (L t i j : Nat) : Expr2 := .binary .and (aSl L t i) (bSl L t j)
abbrev xorP (a b : Expr2) : Expr2 := .binary .xor a b
def bsP (L t k : Nat) (e : Expr2) : Process2 := .assign (.slice "rv" (L * KS L + (8 * t + k)) 1) e

/-- The seven column assigns of base node `t`, the generator's XOR trees. -/
def baseP (L t : Nat) : List Process2 :=
  [bsP L t 0 (ppP L t 0 0),
   bsP L t 1 (xorP (ppP L t 0 1) (ppP L t 1 0)),
   bsP L t 2 (xorP (xorP (ppP L t 0 2) (ppP L t 1 1)) (ppP L t 2 0)),
   bsP L t 3 (xorP (xorP (ppP L t 0 3) (ppP L t 1 2)) (xorP (ppP L t 2 1) (ppP L t 3 0))),
   bsP L t 4 (xorP (xorP (ppP L t 1 3) (ppP L t 2 2)) (ppP L t 3 1)),
   bsP L t 5 (xorP (ppP L t 2 3) (ppP L t 3 2)),
   bsP L t 6 (ppP L t 3 3)]

theorem KS_eq (L : Nat) : KS L = 2 * KR L := by unfold KS KR; omega

theorem base_inst {E : IEnv} {elems : List (String × Nat)} {N L : Nat} (hE : KEnv E N L) {t : Nat}
    (ht : t < 3 ^ L) :
    [bs0, bs1, bs2, bs3, bs4, bs5, bs6].map (instProcess2 (E.bindVal "t" (t : Int)) elems) = baseP L t := by
  have hE' := hE.bind "t" (by decide) (by decide) (by decide) (by decide) (t : Int)
  have hR := KR_pos L
  have hS : 1 ≤ KS L := by rw [KS_eq]; omega
  have h4 : 4 * t + 4 ≤ KR L := by
    have := node_fits (L := L) (l := L) (t := t) (Nat.le_refl L) ht
    unfold KW at this
    simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at this
    omega
  have hL : evalInt (E.bindVal "t" (t : Int)) prL = .ok (L : Int) := evalInt_paramRef_of hE'.hL
  have ra : ∀ k, k ≤ 3 → fitExpr2 (E.bindVal "t" (t : Int)) elems (some 1) (aE k) = aSl L t k :=
    fun k hk => elem2_read hE'.hav hR hL (Nat.le_refl L) (bs_f4 E t k).ev (by omega)
  have rb : ∀ k, k ≤ 3 → fitExpr2 (E.bindVal "t" (t : Int)) elems (some 1) (bE k) = bSl L t k :=
    fun k hk => elem2_read hE'.hbv hR hL (Nat.le_refl L) (bs_f4 E t k).ev (by omega)
  have tg : ∀ k, k ≤ 6 → instLhs2 (E.bindVal "t" (t : Int)) elems (rT k) =
      .ok (.slice "rv" (L * KS L + (8 * t + k)) 1, 1) :=
    fun k hk => elem2_tgt hE'.hrv hS hL (Nat.le_refl L) (bs_f8 E t k).ev (by rw [KS_eq]; omega)
  simp only [List.map_cons, List.map_nil, bs0, bs1, bs2, bs3, bs4, bs5, bs6,
    instProcess2_assignL _ (tg 0 (by decide)), instProcess2_assignL _ (tg 1 (by decide)),
    instProcess2_assignL _ (tg 2 (by decide)), instProcess2_assignL _ (tg 3 (by decide)),
    instProcess2_assignL _ (tg 4 (by decide)), instProcess2_assignL _ (tg 5 (by decide)),
    instProcess2_assignL _ (tg 6 (by decide)), fitExpr2_binary, instExpr2_xor, instExpr2_and,
    ra 0 (by decide), ra 1 (by decide), ra 2 (by decide), ra 3 (by decide),
    rb 0 (by decide), rb 1 (by decide), rb 2 (by decide), rb 3 (by decide)]
  rfl

theorem base_expand {E : IEnv} {elems : List (String × Nat)} {N L F : Nat} (hE : KEnv E N L)
    (hF : 3 ^ L < F) :
    baseGen.expand2 E elems F = .ok ((List.range (3 ^ L)).flatMap (baseP L)) := by
  have hb : ∀ v : Int, KEnv (E.bindVal "t" v) N L :=
    fun v => hE.bind "t" (by decide) (by decide) (by decide) (by decide) v
  simp only [baseGen, gvt, prT]
  rw [GenItem.expand2_genFor_ascending_processes (N := ((3 ^ L : Nat) : Int)) (evalInt_int 0)
    (fun v => isInt_paramRef_of (hb v).hT) (fun v => evalInt_paramRef_of (hb v).hT)
    (by rw [Int.sub_zero, Int.toNat_natCast]; omega)]
  simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast]
  congr 1
  apply flatMap_congr'
  intro t ht
  exact base_inst hE (List.mem_range.mp ht)

/-! ## 1j. The combination family: node `(l, t)` of level `l < L` from its children's products -/

abbrev rS (L l o w : Nat) : Expr2 := .slice (.ident "rv") ((l + 1) * KS L + o) w
abbrev rSl (L l o w : Nat) : Lhs2 := .slice "rv" (l * KS L + o) w

/-- The five column ranges of node `(l, t)`, with `W = KW L l`, `m = KW L (l + 1)`. -/
def combP (L l t : Nat) : List Process2 :=
  let W := KW L l
  let m := KW L (l + 1)
  [.assign (rSl L l (t * 2 * W) m) (rS L l ((3 * t + 0) * W) m),
   .assign (rSl L l (t * 2 * W + m) (m - 1))
     (xorP (xorP (rS L l ((3 * t + 0) * W) (m - 1)) (rS L l ((3 * t + 0) * W + m) (m - 1)))
       (xorP (rS L l ((3 * t + 1) * W) (m - 1)) (rS L l ((3 * t + 2) * W) (m - 1)))),
   .assign (rSl L l (t * 2 * W + W - 1) 1)
     (xorP (xorP (rS L l ((3 * t + 0) * W + m - 1) 1) (rS L l ((3 * t + 1) * W + m - 1) 1))
       (rS L l ((3 * t + 2) * W + m - 1) 1)),
   .assign (rSl L l (t * 2 * W + W) (m - 1))
     (xorP (xorP (rS L l ((3 * t + 0) * W + m) (m - 1)) (rS L l ((3 * t + 1) * W) (m - 1)))
       (xorP (rS L l ((3 * t + 1) * W + m) (m - 1)) (rS L l ((3 * t + 2) * W + m) (m - 1)))),
   .assign (rSl L l (t * 2 * W + W + m - 1) m) (rS L l ((3 * t + 1) * W + m - 1) m)]

theorem comb_inst {E : IEnv} {elems : List (String × Nat)} {N L : Nat} (hE : KEnv E N L) {l t : Nat}
    (hl : l < L) (ht : t < 3 ^ l) :
    [cb0, cb1, cb2, cb3, cb4].map (instProcess2 (nodeEnv E l t) elems) = combP L l t := by
  have hE' := nd_env hE l t
  have hS : 1 ≤ KS L := by rw [KS_eq]; have := KR_pos L; omega
  have hm4 := KW_pos L (l + 1)
  have hWm := KW_succ hl
  -- the values of the index expressions
  have eT : EvN (nodeEnv E l t) gvt t := EvN.gv (by simp)
  have eW : EvN (nodeEnv E l t) hWT (KW L l) := ⟨nd_int_W hE l t, nd_W hE (by omega)⟩
  have eM : EvN (nodeEnv E l t) hMT (KW L (l + 1)) := ⟨nd_int_M hE l t, nd_M hE hl⟩
  have eL : EvN (nodeEnv E l t) gvl l := ⟨rfl, nd_l E l t⟩
  have eL1 : EvN (nodeEnv E l t) l1T (l + 1) := ⟨rfl, nd_l1 E l t⟩
  have e30 : EvN (nodeEnv E l t) t30 (3 * t + 0) := ⟨rfl, nd_t30 hE l t⟩
  have e31 : EvN (nodeEnv E l t) t31 (3 * t + 1) := ⟨rfl, nd_t31 hE l t⟩
  have e32 : EvN (nodeEnv E l t) t32 (3 * t + 2) := ⟨rfl, nd_t32 hE l t⟩
  have es2 : EvN (nodeEnv E l t) s2T (t * 2 * KW L l) := (eT.mul (EvN.int _ 2)).mul eW
  have ec0 : EvN (nodeEnv E l t) c0T ((3 * t + 0) * KW L l) := e30.mul eW
  have ec1 : EvN (nodeEnv E l t) c1T ((3 * t + 1) * KW L l) := e31.mul eW
  have ec2 : EvN (nodeEnv E l t) c2T ((3 * t + 2) * KW L l) := e32.mul eW
  have emm : EvN (nodeEnv E l t) mm1T (KW L (l + 1) - 1) := eM.sub1 (by omega)
  -- the geometry: the parent slot in row l, the three child slots in row l + 1
  have hpar : t * 2 * KW L l + 2 * KW L l ≤ KS L := by
    have := node_fits (L := L) (l := l) (t := t) (by omega) ht
    have h2 : (t + 1) * KW L l = t * KW L l + KW L l := Nat.succ_mul _ _
    have h3 : t * 2 * KW L l = 2 * (t * KW L l) := by rw [Nat.mul_comm t 2, Nat.mul_assoc]
    rw [KS_eq]
    omega
  have hch : ∀ c, c ≤ 2 → (3 * t + c) * KW L l + KW L l ≤ KS L := by
    intro c hc
    have := node_fits (L := L) (l := l + 1) (t := 3 * t + c) (by omega) (by rw [Nat.pow_succ]; omega)
    have h2 : (3 * t + c + 1) * KW L (l + 1) = (3 * t + c) * KW L (l + 1) + KW L (l + 1) :=
      Nat.succ_mul _ _
    have h3 : (3 * t + c) * KW L l = 2 * ((3 * t + c) * KW L (l + 1)) := by
      rw [hWm, Nat.mul_left_comm]
    rw [KS_eq]
    omega
  have h0 := hch 0 (by omega)
  have h1 := hch 1 (by omega)
  have h2 := hch 2 (by omega)
  have hrv' : (nodeEnv E l t).dims.lookup "rv" = some [((L : Int), 0), ((KS L : Int) - 1, 0)] := hE'.hrv
  simp only [List.map_cons, List.map_nil, cb0, cb1, cb2, cb3, cb4, rP, rEl,
    instProcess2_assignL _ (part2_tgt hrv' hS eL.ev (by omega) es2.ev eM.ev (by omega) (by omega)),
    instProcess2_assignL _ (part2_tgt hrv' hS eL.ev (by omega) (es2.add eM).ev emm.ev (by omega) (by omega)),
    instProcess2_assignL _ (elem2_tgt hrv' hS eL.ev (by omega) ((es2.add eW).sub1 (by omega)).ev (by omega)),
    instProcess2_assignL _ (part2_tgt hrv' hS eL.ev (by omega) (es2.add eW).ev emm.ev (by omega) (by omega)),
    instProcess2_assignL _ (part2_tgt hrv' hS eL.ev (by omega) (((es2.add eW).add eM).sub1 (by omega)).ev
      eM.ev (by omega) (by omega)),
    fitExpr2_binary, instExpr2_xor,
    part2_read hrv' hS eL1.ev (by omega) ec0.ev eM.ev (by omega) (by omega),
    part2_read hrv' hS eL1.ev (by omega) ec0.ev emm.ev (by omega) (by omega),
    part2_read hrv' hS eL1.ev (by omega) (ec0.add eM).ev emm.ev (by omega) (by omega),
    part2_read hrv' hS eL1.ev (by omega) ec1.ev emm.ev (by omega) (by omega),
    part2_read hrv' hS eL1.ev (by omega) ec2.ev emm.ev (by omega) (by omega),
    elem2_read hrv' hS eL1.ev (by omega) ((ec0.add eM).sub1 (by omega)).ev (by omega),
    elem2_read hrv' hS eL1.ev (by omega) ((ec1.add eM).sub1 (by omega)).ev (by omega),
    elem2_read hrv' hS eL1.ev (by omega) ((ec2.add eM).sub1 (by omega)).ev (by omega),
    part2_read hrv' hS eL1.ev (by omega) (ec1.add eM).ev emm.ev (by omega) (by omega),
    part2_read hrv' hS eL1.ev (by omega) (ec2.add eM).ev emm.ev (by omega) (by omega),
    part2_read hrv' hS eL1.ev (by omega) ((ec1.add eM).sub1 (by omega)).ev eM.ev (by omega) (by omega)]
  rfl

theorem comb_expand {E : IEnv} {elems : List (String × Nat)} {N L F : Nat} (hE : KEnv E N L)
    (hF : 3 ^ L < F) (hLF : L < F) :
    combGen.expand2 E elems F =
      .ok ((List.range L).flatMap fun l => (List.range (3 ^ l)).flatMap fun t => combP L l t) := by
  have hb : ∀ v : Int, KEnv (E.bindVal "l" v) N L :=
    fun v => hE.bind "l" (by decide) (by decide) (by decide) (by decide) v
  simp only [combGen, gvl, prL]
  rw [GenItem.expand2_genFor_ascending_flatMap (N := (L : Int))
    (f := fun v => (List.range (3 ^ v.toNat)).flatMap fun t => combP L v.toNat t) (evalInt_int 0)
    (fun v => isInt_paramRef_of (hb v).hL) (fun v => evalInt_paramRef_of (hb v).hL) (by simpa using hLF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast]
  · intro v hv0 hvL
    obtain ⟨l, rfl⟩ : ∃ l : Nat, v = (l : Int) := ⟨v.toNat, by omega⟩
    have hl : l < L := by omega
    simp only [Int.toNat_natCast]
    apply expandList2_singleton_ok
    have hpow : ∀ w : Int, evalInt ((E.bindVal "l" (l : Int)).bindVal "t" w)
        (.binary .pow (.int 3) gvl) = .ok ((3 ^ l : Nat) : Int) := by
      intro w
      rw [evalInt_pow_of rfl rfl (evalInt_int 3)
        (evalInt_genvarRef_of (v := (l : Int)) (by simp [IEnv.bindVal, List.lookup])) (by omega),
        Int.toNat_natCast]
      push_cast
      rfl
    have h3 : 3 ^ l ≤ 3 ^ L := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hl)
    simp only [combNode, nodeBound, gvt, gvl]
    rw [GenItem.expand2_genFor_ascending_processes (N := ((3 ^ l : Nat) : Int))
      (evalInt_int 0) (fun w => rfl) hpow (by rw [Int.sub_zero, Int.toNat_natCast]; omega)]
    simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast]
    congr 1
    apply flatMap_congr'
    intro t ht
    exact comb_inst hE hl (List.mem_range.mp ht)

/-! ## 1k. The three static assigns -/

section statics

variable {E : IEnv} {elems : List (String × Nat)} {N L : Nat} (hE : KEnv E N L)
include hE

theorem row0_win (v : String) (hv : E.dims.lookup v = some [((L : Int), 0), ((KR L : Int) - 1, 0)]) :
    arrayElemWindow E v [.int 0] = .ok (0, KR L, true) := by
  rw [arrayElemWindow_of (arrayDims_of hv) (walkIndices_desc0_cons (by omega) (evalInt_int 0)
    (Int.le_refl 0) (by omega) (walkIndices_nil (env := E) [((KR L : Int) - 1, 0)]))]
  simp [dimsStride_cons, dimCount_B (KR_pos L)]

/-- `av[0] = a` (zero-extended to the row). -/
theorem st_in (v x : String) (hst : PProcess) (hdef : hst = .assignL (.arrayElem v [.int 0]) (.resize 36 (.ident x)))
    (hv : E.dims.lookup v = some [((L : Int), 0), ((KR L : Int) - 1, 0)])
    (hwx : E.widths.lookup x = some N) (hNR : N ≤ KR L) :
    instProcess2 E elems hst = .assign (.slice v 0 (KR L)) (.resize (KR L) (.ident x)) := by
  subst hdef
  rw [instProcess2_assignL _ (by rw [instLhs2_arrayElem, arrayElemTarget_of_inRange (row0_win hE v hv)]),
    fitExpr2_of_not_rigid _ rfl]
  by_cases h : N < KR L
  · simp [instExpr2, selfWidth2, hwx, h, PExpr.ctxPropagates, PExpr.negGenvarWidened]
  · have h' : N = KR L := by omega
    simp [instExpr2, selfWidth2, hwx, h', PExpr.constLeaf]

/-- `p = rv[0][2N-2:0]`. -/
theorem st_out (hN1 : 1 ≤ N) (hwp : E.widths.lookup "p" = some (2 * N - 1)) (hNS : 2 * N - 1 ≤ KS L) :
    instProcess2 E elems st2 = .assign (.ident "p") (.slice (.ident "rv") 0 (2 * N - 1)) := by
  have hS : 1 ≤ KS L := by rw [KS_eq]; have := KR_pos L; omega
  have hbm : (0 : Int) ≤ (KS L : Int) - 1 := by omega
  have hwk := walkIndices_desc0_cons (env := E) (ds := [((KS L : Int) - 1, 0)]) (m := (L : Int))
    (by omega) (evalInt_int 0) (Int.le_refl 0) (by omega) (walkIndices_nil (env := E) [((KS L : Int) - 1, 0)])
  have e2N : evalInt E (eSub (eMul (.int 2) (.paramRef "N" none)) (.int 2)) = .ok ((2 * N - 2 : Nat) : Int) := by
    have h : EvN E (eMul (.int 2) (.paramRef "N" none)) (2 * N) := (EvN.int E 2).mul (EvN.par hE.hN)
    rw [eSub, evalInt_sub_of h.isInt rfl h.ev (evalInt_int 2)]
    congr 1
    omega
  have hg := arrayPartGeom_range_of (env := E) (n := "rv") (is := [.int 0]) (arrayDims_of hE.hrv) hwk e2N
    (evalInt_int 0) (by rw [labelOffset_desc0 hbm, labelOffset_desc0 hbm]; omega)
  rw [labelOffset_desc0 hbm, labelOffset_desc0 hbm, dimCount_B hS] at hg
  have hw1 : (((2 * N - 2 : Nat) : Int) - 0 + 1).toNat * dimsStride [] = 2 * N - 1 := by
    simp only [dimsStride_nil, Nat.mul_one]
    omega
  rw [st2, instProcess2_assign _ hwp, ← hw1, fitExpr2_arrayPart_of hg,
    arrayPartRead_of_inRange hg (by omega) (by omega), hw1]
  simp

end statics

/-! ## 1l. The parameter stage, the declarations, the element widths -/

def kScope (N : Nat) : IEnv :=
  { vals := [("T", (3 : Int) ^ KL N), ("P", 4 * (2 : Int) ^ KL N), ("L", (KL N : Int)), ("N", (N : Int))],
    pwidths := [("N", 32), ("L", 32), ("P", 32), ("T", 32)] }

def kEnv (N : Nat) : IEnv := { kScope N with dims := dimTable (kScope N) design.pdesign.decls }

theorem kara_paramEnv (N : Nat) : design.pdesign.paramEnv2 [(N : Int)] = .ok (kEnv N) := rfl

theorem le_two_pow_clog2' (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · simp only [Nat.pow_zero]; omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-- `N ≤ P = 4 * 2^L`: the padded width holds the operands. -/
theorem N_le_P (N : Nat) : N ≤ 4 * 2 ^ KL N := by
  have h := le_two_pow_clog2' ((N + 3) / 4)
  unfold KL
  omega

/-- `2^L ≤ N + 2`: the levels are logarithmic. -/
theorem pow_KL_le {N : Nat} (hN : 1 ≤ N) : 2 ^ KL N ≤ N + 2 := by
  unfold KL clog2
  split
  · simp only [Nat.pow_zero]; omega
  · have hn : (N + 3) / 4 - 1 ≠ 0 := by omega
    have h := Nat.log2_lt (n := (N + 3) / 4 - 1) (k := ((N + 3) / 4 - 1).log2) hn
    have : ¬ ((N + 3) / 4 - 1 < 2 ^ ((N + 3) / 4 - 1).log2) := fun h' => Nat.lt_irrefl _ (h.mpr h')
    rw [Nat.pow_succ]
    omega

theorem N_le_KR (N : Nat) : N ≤ KR (KL N) := by
  have h1 := N_le_P N
  have h2 : 2 ^ KL N ≤ 3 ^ KL N := Nat.pow_le_pow_left (by decide) _
  unfold KR
  omega

/-- The node count `3^L` is within the generate fuel `(N + 2)^2 + 64`. -/
theorem fuel_ok {N : Nat} (hN : 1 ≤ N) :
    3 ^ KL N < PDesign.surfaceFuel [(N : Int)] ∧ KL N < PDesign.surfaceFuel [(N : Int)] := by
  have h1 : 3 ^ KL N ≤ 4 ^ KL N := Nat.pow_le_pow_left (by decide) _
  have h2 : 4 ^ KL N = 2 ^ KL N * 2 ^ KL N := by
    rw [show (4 : Nat) = 2 * 2 from rfl, Nat.mul_pow]
  have h3 := pow_KL_le hN
  have h4 : 2 ^ KL N * 2 ^ KL N ≤ (N + 2) * (N + 2) := Nat.mul_le_mul h3 h3
  have h5 : KL N < 2 ^ KL N := Nat.lt_two_pow_self
  have h6 : N + 2 ≤ (N + 2) * (N + 2) := Nat.le_mul_self _
  simp only [PDesign.surfaceFuel, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.natAbs_natCast, Nat.add_zero]
  generalize 2 ^ KL N = X at *
  generalize (N + 2) * (N + 2) = Y at *
  constructor <;> omega

def kDecls (N : Nat) : List Decl :=
  [{ name := "a", width := N, isInput := true },
   { name := "b", width := N, isInput := true },
   { name := "p", width := 2 * N - 1, isOutput := true },
   { name := "av", width := (KL N + 1) * KR (KL N) },
   { name := "bv", width := (KL N + 1) * KR (KL N) },
   { name := "rv", width := (KL N + 1) * KS (KL N) }]

theorem kara_decls {N : Nat} (hN : 1 ≤ N) :
    buildDecls (kEnv N) design.pdesign.decls = .ok (kDecls N) := by
  have hv : ((N : Int) - 1).natAbs + 1 = N := by omega
  have hp : (2 * (N : Int) - 2).natAbs + 1 = 2 * N - 1 := by omega
  have hR : (4 * (3 : Int) ^ KL N - 1).natAbs + 1 = KR (KL N) := by
    have := KR_pos (KL N)
    unfold KR at *
    have e : (4 : Int) * 3 ^ KL N = ((4 * 3 ^ KL N : Nat) : Int) := by push_cast; rfl
    rw [e]
    omega
  have hS : (8 * (3 : Int) ^ KL N - 1).natAbs + 1 = KS (KL N) := by
    have := KR_pos (KL N)
    unfold KS KR at *
    have e : (8 : Int) * 3 ^ KL N = ((8 * 3 ^ KL N : Nat) : Int) := by push_cast; rfl
    rw [e]
    omega
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt, kEnv,
    kScope, List.lookup, Gen2.except_ok_bind, kDecls, hv, hp, hR, hS]

def kElemsL (N : Nat) : List (String × Nat) :=
  [("a", 1), ("b", 1), ("p", 1), ("av", KR (KL N)), ("bv", KR (KL N)), ("rv", KS (KL N))]

theorem kara_elems (N : Nat) : buildElems (kEnv N) design.pdesign.decls = .ok (kElemsL N) := by
  have hR : (4 * (3 : Int) ^ KL N - 1).natAbs + 1 = KR (KL N) := by
    have := KR_pos (KL N)
    unfold KR at *
    have e : (4 : Int) * 3 ^ KL N = ((4 * 3 ^ KL N : Nat) : Int) := by push_cast; rfl
    rw [e]
    omega
  have hS : (8 * (3 : Int) ^ KL N - 1).natAbs + 1 = KS (KL N) := by
    have := KR_pos (KL N)
    unfold KS KR at *
    have e : (8 : Int) * 3 ^ KL N = ((8 * 3 ^ KL N : Nat) : Int) := by push_cast; rfl
    rw [e]
    omega
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, kEnv, kScope,
    List.lookup, kElemsL, Gen2.except_ok_bind, Gen2.except_pure, PType.elemWidth, hR, hS]

theorem dim_ev (N : Nat) (ws : List (String × Nat)) (c : Nat) :
    evalInt { kScope N with widths := ws } (eSub (eMul (.int (c : Int)) prT) (.int 1)) =
      .ok (((c * 3 ^ KL N : Nat) : Int) - 1) := by
  have hT : ({ kScope N with widths := ws } : IEnv).vals.lookup "T" = some ((3 ^ KL N : Nat) : Int) := by
    simp [kScope, List.lookup]
  rw [eSub, evalInt_sub_of (isInt_binary_of rfl rfl (isInt_paramRef_of hT)) rfl
    ((EvN.int _ c).mul (EvN.par hT)).ev (evalInt_int 1)]

theorem kEnvOk (N : Nat) : KEnv (kEnv N) N (KL N) where
  hN := by simp [kEnv, kScope, List.lookup]
  hL := by simp [kEnv, kScope, List.lookup]
  hP := by simp [kEnv, kScope, List.lookup]
  hT := by simp [kEnv, kScope, List.lookup]
  hav := PDesign.dimTable_lookup_of (env := kScope N)
    (rfl : design.pdesign.packedDims.lookup "av" =
      some [{ msb := prL, lsb := .int 0 }, { msb := eSub (eMul (.int 4) prT) (.int 1), lsb := .int 0 }])
    (fun ws => evalDims_cons_of (evalInt_paramRef_of (by simp [kScope, List.lookup])) (evalInt_int 0)
      (evalDims_cons_of (dim_ev N ws 4) (evalInt_int 0) evalDims_nil))
  hbv := PDesign.dimTable_lookup_of (env := kScope N)
    (rfl : design.pdesign.packedDims.lookup "bv" =
      some [{ msb := prL, lsb := .int 0 }, { msb := eSub (eMul (.int 4) prT) (.int 1), lsb := .int 0 }])
    (fun ws => evalDims_cons_of (evalInt_paramRef_of (by simp [kScope, List.lookup])) (evalInt_int 0)
      (evalDims_cons_of (dim_ev N ws 4) (evalInt_int 0) evalDims_nil))
  hrv := PDesign.dimTable_lookup_of (env := kScope N)
    (rfl : design.pdesign.packedDims.lookup "rv" =
      some [{ msb := prL, lsb := .int 0 }, { msb := eSub (eMul (.int 8) prT) (.int 1), lsb := .int 0 }])
    (fun ws => evalDims_cons_of (evalInt_paramRef_of (by simp [kScope, List.lookup])) (evalInt_int 0)
      (evalDims_cons_of (dim_ev N ws 8) (evalInt_int 0) evalDims_nil))

/-! ## 1m. `instantiate2` at symbolic `N` -/

/-- The generate expansion: the split family, the base family, the combination family. -/
def kGens (L : Nat) : List Process2 :=
  ((List.range L).flatMap fun l => (List.range (3 ^ l)).flatMap fun t => splitP L l t) ++
    (((List.range (3 ^ L)).flatMap (baseP L)) ++
      ((List.range L).flatMap fun l => (List.range (3 ^ l)).flatMap fun t => combP L l t))

def kM (N : Nat) : Design2 := design.pdesign.assemble2 (kEnv N) (kDecls N) (kElemsL N) (kGens (KL N))

theorem kara_instantiate2 {N : Nat} (hN : 1 ≤ N) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) = .ok (kM N) := by
  obtain ⟨hF1, hF2⟩ := fuel_ok hN
  have hE := (kEnvOk N).withDecls (kDecls N)
  exact PDesign.instantiate2_of_ok rfl (kara_paramEnv N) (kara_decls hN) (kara_elems N)
    (by
      rw [kara_generates]
      exact expandList2_cons_ok (split_expand hE hF1 hF2)
        (expandList2_cons_ok (base_expand hE hF1) (expandList2_singleton_ok (comb_expand hE hF1 hF2))))

/-- The static processes, instantiated. -/
def kStatics (N : Nat) : List Process2 :=
  [.assign (.slice "av" 0 (KR (KL N))) (.resize (KR (KL N)) (.ident "a")),
   .assign (.slice "bv" 0 (KR (KL N))) (.resize (KR (KL N)) (.ident "b")),
   .assign (.ident "p") (.slice (.ident "rv") 0 (2 * N - 1))]

/-- **The instantiated process list, for every `N ≥ 1`.** -/
theorem kM_processes {N : Nat} (hN : 1 ≤ N) : (kM N).processes.toList = kStatics N ++ kGens (KL N) := by
  have hE := (kEnvOk N).withDecls (kDecls N)
  have hNS : 2 * N - 1 ≤ KS (KL N) := by have := N_le_KR N; rw [KS_eq]; omega
  rw [kM, PDesign.assemble2_processes, kara_static_source, kara_others]
  simp only [List.map_cons, List.map_nil, List.append_nil]
  rw [st_in hE "av" "a" st0 rfl hE.hav (by simp [kDecls, List.lookup]) (N_le_KR N),
    st_in hE "bv" "b" st1 rfl hE.hbv (by simp [kDecls, List.lookup]) (N_le_KR N),
    st_out hE hN (by simp [kDecls, List.lookup]) hNS]
  rfl

/-! # Part 2. The comb profile and acyclicity

## 2a. The processes by family, their windows -/

def kProcs (N : Nat) : List Process2 := kStatics N ++ kGens (KL N)

/-- The write window of a process (`p` is the whole `2N-1`-bit output). -/
def winOf (N : Nat) : Process2 → Win
  | .assign (.slice n lo w) _ => (n, lo, w)
  | .assign (.ident n) _ => (n, 0, 2 * N - 1)
  | _ => ("", 0, 0)

def rhsOf : Process2 → Expr2
  | .assign _ e => e
  | _ => .lit ⟨#[]⟩

theorem kProcs_forall {N : Nat} {P : Process2 → Prop}
    (hs : ∀ p ∈ kStatics N, P p)
    (hsp : ∀ l t, l < KL N → t < 3 ^ l → ∀ p ∈ splitP (KL N) l t, P p)
    (hb : ∀ t, t < 3 ^ KL N → ∀ p ∈ baseP (KL N) t, P p)
    (hc : ∀ l t, l < KL N → t < 3 ^ l → ∀ p ∈ combP (KL N) l t, P p) :
    ∀ p ∈ kProcs N, P p := by
  intro p hp
  simp only [kProcs, kGens, List.mem_append, List.mem_flatMap, List.mem_range] at hp
  rcases hp with h | ⟨l, hl, t, ht, h⟩ | ⟨t, ht, h⟩ | ⟨l, hl, t, ht, h⟩
  · exact hs p h
  · exact hsp l t hl ht p h
  · exact hb t ht p h
  · exact hc l t hl ht p h

/-- Every process assigns a slice of `av`, `bv` or `rv` of positive width, or the whole `p`. -/
theorem kProcs_shape {N : Nat} (hN : 1 ≤ N) : ∀ p ∈ kProcs N,
    (∃ n lo w e, p = .assign (.slice n lo w) e ∧ n ∈ ["av", "bv", "rv"] ∧ 0 < w) ∨
      ∃ e, p = .assign (.ident "p") e := by
  have hR := KR_pos (KL N)
  refine kProcs_forall ?_ ?_ ?_ ?_
  · intro p hp
    simp only [kStatics, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl ⟨_, _, _, _, rfl, by decide, by omega⟩
    · exact Or.inl ⟨_, _, _, _, rfl, by decide, by omega⟩
    · exact Or.inr ⟨_, rfl⟩
  · intro l t hl ht p hp
    have := KW_pos (KL N) (l + 1)
    simp only [splitP, spLoP, spHiP, spMidP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Or.inl ⟨_, _, _, _, rfl, by decide, by omega⟩
  · intro t ht p hp
    simp only [baseP, bsP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Or.inl ⟨_, _, _, _, rfl, by decide, by omega⟩
  · intro l t hl ht p hp
    have := KW_pos (KL N) (l + 1)
    simp only [combP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      exact Or.inl ⟨_, _, _, _, rfl, by decide, by omega⟩

/-! ## 2b. Declarations of the instantiated design -/

theorem kM_decls (N : Nat) : (kM N).decls.toList = kDecls N := PDesign.assemble2_decls ..

theorem kM_declWidth (N : Nat) (n : String) :
    (kM N).declWidth n = ((kDecls N).find? fun dc => dc.name == n).map Decl.width := by
  simp only [Design2.declWidth, kM_decls]

theorem kM_declWidth_av (N : Nat) : (kM N).declWidth "av" = some ((KL N + 1) * KR (KL N)) := by
  simp [kM_declWidth, kDecls]
theorem kM_declWidth_bv (N : Nat) : (kM N).declWidth "bv" = some ((KL N + 1) * KR (KL N)) := by
  simp [kM_declWidth, kDecls]
theorem kM_declWidth_rv (N : Nat) : (kM N).declWidth "rv" = some ((KL N + 1) * KS (KL N)) := by
  simp [kM_declWidth, kDecls]
theorem kM_declWidth_p (N : Nat) : (kM N).declWidth "p" = some (2 * N - 1) := by
  simp [kM_declWidth, kDecls]

theorem kM_inputNames (N : Nat) : (kM N).inputNames.toList = ["a", "b"] := by
  simp [Design2.inputNames, kM_decls, kDecls]

/-- The target of every process has exactly its `winOf` window. -/
theorem kProcs_wins {N : Nat} (hN : 1 ≤ N) : ∀ p ∈ kProcs N, ∀ t e, p = .assign t e →
    t.windows? (kM N) = some [winOf N p] ∧ t.wins (kM N) = [winOf N p] := by
  intro p hp t e hpe
  rcases kProcs_shape hN p hp with ⟨n, lo, w, e', rfl, -⟩ | ⟨e', rfl⟩
  · simp only [Process2.assign.injEq] at hpe
    obtain ⟨rfl, -⟩ := hpe
    exact ⟨rfl, by simp [winOf]⟩
  · simp only [Process2.assign.injEq] at hpe
    obtain ⟨rfl, -⟩ := hpe
    have hw : (Lhs2.ident "p").window? (kM N) = some ("p", 0, 2 * N - 1) := by
      simp [Lhs2.window?, kM_declWidth_p]
    exact ⟨Lhs2.windows?_of_window? hw, Lhs2.wins_of_window? hw⟩

/-! ## 2c. The window list, and one driver per bit -/

def wsS (N : Nat) : List Win := [("av", 0, KR (KL N)), ("bv", 0, KR (KL N)), ("p", 0, 2 * N - 1)]

def wsSp (L l t : Nat) : List Win :=
  [("av", (l + 1) * KR L + (3 * t + 0) * KW L (l + 1), KW L (l + 1)),
   ("bv", (l + 1) * KR L + (3 * t + 0) * KW L (l + 1), KW L (l + 1)),
   ("av", (l + 1) * KR L + (3 * t + 1) * KW L (l + 1), KW L (l + 1)),
   ("bv", (l + 1) * KR L + (3 * t + 1) * KW L (l + 1), KW L (l + 1)),
   ("av", (l + 1) * KR L + (3 * t + 2) * KW L (l + 1), KW L (l + 1)),
   ("bv", (l + 1) * KR L + (3 * t + 2) * KW L (l + 1), KW L (l + 1))]

def wsBs (L t : Nat) : List Win :=
  [("rv", L * KS L + (8 * t + 0), 1), ("rv", L * KS L + (8 * t + 1), 1), ("rv", L * KS L + (8 * t + 2), 1),
   ("rv", L * KS L + (8 * t + 3), 1), ("rv", L * KS L + (8 * t + 4), 1), ("rv", L * KS L + (8 * t + 5), 1),
   ("rv", L * KS L + (8 * t + 6), 1)]

def wsCb (L l t : Nat) : List Win :=
  [("rv", l * KS L + t * 2 * KW L l, KW L (l + 1)),
   ("rv", l * KS L + (t * 2 * KW L l + KW L (l + 1)), KW L (l + 1) - 1),
   ("rv", l * KS L + (t * 2 * KW L l + KW L l - 1), 1),
   ("rv", l * KS L + (t * 2 * KW L l + KW L l), KW L (l + 1) - 1),
   ("rv", l * KS L + (t * 2 * KW L l + KW L l + KW L (l + 1) - 1), KW L (l + 1))]

def wsA (L : Nat) : List Win := (List.range L).flatMap fun l => (List.range (3 ^ l)).flatMap (wsSp L l)
def wsB (L : Nat) : List Win := (List.range (3 ^ L)).flatMap (wsBs L)
def wsC (L : Nat) : List Win := (List.range L).flatMap fun l => (List.range (3 ^ l)).flatMap (wsCb L l)

theorem kProcs_winOf (N : Nat) :
    (kProcs N).map (winOf N) = wsS N ++ (wsA (KL N) ++ (wsB (KL N) ++ wsC (KL N))) := by
  simp only [kProcs, kGens, kStatics, List.map_append, List.map_cons, List.map_nil, List.map_flatMap,
    wsA, wsB, wsC]
  rfl

macro "ov_close" : tactic =>
  `(tactic| (rw [Win.overlaps_eq_false]; first | (left; decide) | (right; left; omega) | (right; right; omega)))

theorem wsSp_self (L l t : Nat) : (wsSp L l t).Pairwise fun a b => Win.overlaps a b = false := by
  have e1 := rowMajor_le (K := KW L (l + 1)) (show 3 * t + 0 < 3 * t + 1 by omega)
  have e2 := rowMajor_le (K := KW L (l + 1)) (show 3 * t + 0 < 3 * t + 2 by omega)
  have e3 := rowMajor_le (K := KW L (l + 1)) (show 3 * t + 1 < 3 * t + 2 by omega)
  simp only [wsSp, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> ov_close

theorem wsBs_self (L t : Nat) : (wsBs L t).Pairwise fun a b => Win.overlaps a b = false := by
  simp only [wsBs, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    ov_close

theorem wsCb_self {L l t : Nat} (hl : l < L) : (wsCb L l t).Pairwise fun a b => Win.overlaps a b = false := by
  have hW := KW_succ hl
  have hm := KW_pos L (l + 1)
  simp only [wsCb, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> ov_close

theorem mem_wsSp {L l t : Nat} {w : Win} (h : w ∈ wsSp L l t) :
    (w.1 = "av" ∨ w.1 = "bv") ∧ ∃ c, c ≤ 2 ∧ w.2.1 = (l + 1) * KR L + (3 * t + c) * KW L (l + 1) ∧
      w.2.2 = KW L (l + 1) := by
  simp only [wsSp, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨Or.inl rfl, 0, by omega, rfl, rfl⟩ | exact ⟨Or.inr rfl, 0, by omega, rfl, rfl⟩
      | exact ⟨Or.inl rfl, 1, by omega, rfl, rfl⟩ | exact ⟨Or.inr rfl, 1, by omega, rfl, rfl⟩
      | exact ⟨Or.inl rfl, 2, by omega, rfl, rfl⟩ | exact ⟨Or.inr rfl, 2, by omega, rfl, rfl⟩

theorem mem_wsBs {L t : Nat} {w : Win} (h : w ∈ wsBs L t) :
    w.1 = "rv" ∧ ∃ k, k ≤ 6 ∧ w.2.1 = L * KS L + (8 * t + k) ∧ w.2.2 = 1 := by
  simp only [wsBs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨rfl, 0, by omega, rfl, rfl⟩ | exact ⟨rfl, 1, by omega, rfl, rfl⟩
      | exact ⟨rfl, 2, by omega, rfl, rfl⟩ | exact ⟨rfl, 3, by omega, rfl, rfl⟩
      | exact ⟨rfl, 4, by omega, rfl, rfl⟩ | exact ⟨rfl, 5, by omega, rfl, rfl⟩
      | exact ⟨rfl, 6, by omega, rfl, rfl⟩

/-- A combination window lies inside its node's slot `[t * 2W, t * 2W + 2W)` of row `l`. -/
theorem mem_wsCb {L l t : Nat} (hl : l < L) {w : Win} (h : w ∈ wsCb L l t) :
    w.1 = "rv" ∧ ∃ x, w.2.1 = l * KS L + (t * 2 * KW L l + x) ∧ x + w.2.2 ≤ 2 * KW L l ∧ 0 < w.2.2 := by
  have hW := KW_succ hl
  have hm := KW_pos L (l + 1)
  simp only [wsCb, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, 0, by simp, by simp; omega, by simp; omega⟩
  · exact ⟨rfl, KW L (l + 1), rfl, by simp; omega, by simp; omega⟩
  · exact ⟨rfl, KW L l - 1, by simp; omega, by simp; omega, by simp⟩
  · exact ⟨rfl, KW L l, rfl, by simp; omega, by simp; omega⟩
  · exact ⟨rfl, KW L l + KW L (l + 1) - 1, by simp; omega, by simp; omega, by simp; omega⟩

/-- Node slots of one row are disjoint: `t * 2W + 2W ≤ t' * 2W` for `t < t'`. -/
theorem slot_le {W t t' : Nat} (h : t < t') : t * 2 * W + 2 * W ≤ t' * 2 * W := by
  have := rowMajor_le (K := 2 * W) h
  rw [Nat.mul_assoc t 2 W, Nat.mul_assoc t' 2 W]
  exact this

theorem wsA_pairwise (L : Nat) : (wsA L).Pairwise fun a b => Win.overlaps a b = false := by
  apply pairwise_flatMap_range
  · intro l hl
    apply pairwise_flatMap_range
    · intro t _
      exact wsSp_self L l t
    · intro t t' htt' ht' a ha b hb
      obtain ⟨hna, c, hc, hla, hwa⟩ := mem_wsSp ha
      obtain ⟨hnb, c', hc', hlb, hwb⟩ := mem_wsSp hb
      have := rowMajor_le (K := KW L (l + 1)) (show 3 * t + c < 3 * t' + c' by omega)
      obtain ⟨na, la, wa⟩ := a
      obtain ⟨nb, lb, wb⟩ := b
      simp only at hna hnb hla hlb hwa hwb
      subst hla hlb hwa hwb
      ov_close
  · intro l l' hll' hl' a ha b hb
    simp only [List.mem_flatMap, List.mem_range] at ha hb
    obtain ⟨t, ht, ha⟩ := ha
    obtain ⟨t', ht', hb⟩ := hb
    obtain ⟨hna, c, hc, hla, hwa⟩ := mem_wsSp ha
    obtain ⟨hnb, c', hc', hlb, hwb⟩ := mem_wsSp hb
    have hf := (split_fits (show l < L by omega) ht c hc).1
    have hr := rowMajor_le (K := KR L) (show l + 1 < l' + 1 by omega)
    obtain ⟨na, la, wa⟩ := a
    obtain ⟨nb, lb, wb⟩ := b
    simp only at hna hnb hla hlb hwa hwb
    subst hla hlb hwa hwb
    ov_close

theorem wsB_pairwise (L : Nat) : (wsB L).Pairwise fun a b => Win.overlaps a b = false := by
  apply pairwise_flatMap_range
  · intro t _
    exact wsBs_self L t
  · intro t t' htt' ht' a ha b hb
    obtain ⟨hna, k, hk, hla, hwa⟩ := mem_wsBs ha
    obtain ⟨hnb, k', hk', hlb, hwb⟩ := mem_wsBs hb
    obtain ⟨na, la, wa⟩ := a
    obtain ⟨nb, lb, wb⟩ := b
    simp only at hna hnb hla hlb hwa hwb
    subst hla hlb hwa hwb
    ov_close

theorem wsC_pairwise (L : Nat) : (wsC L).Pairwise fun a b => Win.overlaps a b = false := by
  apply pairwise_flatMap_range
  · intro l hl
    apply pairwise_flatMap_range
    · intro t _
      exact wsCb_self hl
    · intro t t' htt' ht' a ha b hb
      obtain ⟨hna, x, hla, hxa, -⟩ := mem_wsCb hl ha
      obtain ⟨hnb, x', hlb, hxb, -⟩ := mem_wsCb hl hb
      have := slot_le (W := KW L l) htt'
      obtain ⟨na, la, wa⟩ := a
      obtain ⟨nb, lb, wb⟩ := b
      simp only at hna hnb hla hlb hxa hxb
      subst hla hlb
      ov_close
  · intro l l' hll' hl' a ha b hb
    simp only [List.mem_flatMap, List.mem_range] at ha hb
    obtain ⟨t, ht, ha⟩ := ha
    obtain ⟨t', ht', hb⟩ := hb
    obtain ⟨hna, x, hla, hxa, -⟩ := mem_wsCb (show l < L by omega) ha
    obtain ⟨hnb, x', hlb, hxb, -⟩ := mem_wsCb hl' hb
    have hpar : t * 2 * KW L l + 2 * KW L l ≤ KS L := by
      have := node_fits (L := L) (l := l) (t := t) (by omega) ht
      have h2 : (t + 1) * KW L l = t * KW L l + KW L l := Nat.succ_mul _ _
      have h3 : t * 2 * KW L l = 2 * (t * KW L l) := by rw [Nat.mul_comm t 2, Nat.mul_assoc]
      rw [KS_eq]
      omega
    have hr := rowMajor_le (K := KS L) hll'
    obtain ⟨na, la, wa⟩ := a
    obtain ⟨nb, lb, wb⟩ := b
    simp only at hna hnb hla hlb hxa hxb
    subst hla hlb
    ov_close

/-- The parent slot of a combination node fits its row. -/
theorem comb_slot {L l t : Nat} (hl : l < L) (ht : t < 3 ^ l) : t * 2 * KW L l + 2 * KW L l ≤ KS L := by
  have := node_fits (L := L) (l := l) (t := t) (by omega) ht
  have h2 : (t + 1) * KW L l = t * KW L l + KW L l := Nat.succ_mul _ _
  have h3 : t * 2 * KW L l = 2 * (t * KW L l) := by rw [Nat.mul_comm t 2, Nat.mul_assoc]
  rw [KS_eq]
  omega

theorem mem_wsA {L : Nat} {w : Win} (h : w ∈ wsA L) : w.1 = "av" ∨ w.1 = "bv" := by
  simp only [wsA, List.mem_flatMap, List.mem_range] at h
  obtain ⟨l, -, t, -, h⟩ := h
  exact (mem_wsSp h).1

theorem mem_wsB {L : Nat} {w : Win} (h : w ∈ wsB L) :
    w.1 = "rv" ∧ ∃ x, w.2.1 = L * KS L + x ∧ x + w.2.2 ≤ KS L := by
  simp only [wsB, List.mem_flatMap, List.mem_range] at h
  obtain ⟨t, ht, h⟩ := h
  obtain ⟨hn, k, hk, hlo, hw⟩ := mem_wsBs h
  refine ⟨hn, 8 * t + k, hlo, ?_⟩
  have := node_fits (L := L) (l := L) (t := t) (Nat.le_refl L) ht
  unfold KW at this
  simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at this
  rw [hw, KS_eq]
  omega

theorem mem_wsC {L : Nat} {w : Win} (h : w ∈ wsC L) :
    w.1 = "rv" ∧ ∃ l x, l < L ∧ w.2.1 = l * KS L + x ∧ x + w.2.2 ≤ KS L := by
  simp only [wsC, List.mem_flatMap, List.mem_range] at h
  obtain ⟨l, hl, t, ht, h⟩ := h
  obtain ⟨hn, x, hlo, hx, -⟩ := mem_wsCb hl h
  exact ⟨hn, l, t * 2 * KW L l + x, hl, hlo, by have := comb_slot hl ht; omega⟩

theorem ws_pairwise (N : Nat) :
    (wsS N ++ (wsA (KL N) ++ (wsB (KL N) ++ wsC (KL N)))).Pairwise fun a b => Win.overlaps a b = false := by
  simp only [List.pairwise_append]
  refine ⟨?_, ⟨wsA_pairwise _, ⟨wsB_pairwise _, wsC_pairwise _, ?_⟩, ?_⟩, ?_⟩
  · simp [wsS, Win.overlaps_eq_false]
  · intro a ha b hb
    obtain ⟨hna, x, hla, hxa⟩ := mem_wsB ha
    obtain ⟨hnb, l, x', hl, hlb, hxb⟩ := mem_wsC hb
    have hr := rowMajor_le (K := KS (KL N)) hl
    obtain ⟨na, la, wa⟩ := a
    obtain ⟨nb, lb, wb⟩ := b
    simp only at hna hnb hla hlb hxa hxb
    subst hla hlb
    ov_close
  · intro a ha b hb
    have hna := mem_wsA ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb
    · have hnb := (mem_wsB hb).1
      obtain ⟨na, la, wa⟩ := a
      obtain ⟨nb, lb, wb⟩ := b
      simp only at hna hnb
      rw [Win.overlaps_eq_false]
      left
      rcases hna with rfl | rfl <;> subst hnb <;> decide
    · have hnb := (mem_wsC hb).1
      obtain ⟨na, la, wa⟩ := a
      obtain ⟨nb, lb, wb⟩ := b
      simp only at hna hnb
      rw [Win.overlaps_eq_false]
      left
      rcases hna with rfl | rfl <;> subst hnb <;> decide
  · intro a ha b hb
    simp only [wsS, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb
    · simp only [wsA, List.mem_flatMap, List.mem_range] at hb
      obtain ⟨l, hl, t, ht, hb⟩ := hb
      obtain ⟨hnb, c, hc, hlb, hwb⟩ := mem_wsSp hb
      have hr := rowMajor_le (K := KR (KL N)) (show 0 < l + 1 by omega)
      obtain ⟨nb, lb, wb⟩ := b
      simp only at hnb hlb hwb
      subst hlb hwb
      rcases ha with rfl | rfl | rfl <;> rcases hnb with rfl | rfl <;> ov_close
    · obtain ⟨hnb, -⟩ := mem_wsB hb
      obtain ⟨nb, lb, wb⟩ := b
      simp only at hnb
      subst hnb
      rcases ha with rfl | rfl | rfl <;> ov_close
    · obtain ⟨hnb, -⟩ := mem_wsC hb
      obtain ⟨nb, lb, wb⟩ := b
      simp only at hnb
      subst hnb
      rcases ha with rfl | rfl | rfl <;> ov_close

/-! ## 2d. Every window is inside one row of its signal -/

def wsAll (N : Nat) : List Win := wsS N ++ (wsA (KL N) ++ (wsB (KL N) ++ wsC (KL N)))

theorem wsAll_row {N : Nat} {n : String} {lo wd : Nat} (h : (n, lo, wd) ∈ wsAll N) :
    ((n = "av" ∨ n = "bv") ∧ ∃ r x, r ≤ KL N ∧ lo = r * KR (KL N) + x ∧
        x + wd ≤ KR (KL N) ∧ 0 < wd) ∨
      (n = "rv" ∧ ∃ r x, r ≤ KL N ∧ lo = r * KS (KL N) + x ∧ x + wd ≤ KS (KL N) ∧ 0 < wd) ∨
      (n = "p" ∧ wd = 2 * N - 1) := by
  have hR := KR_pos (KL N)
  simp only [wsAll, List.mem_append] at h
  rcases h with h | h | h | h
  · simp only [wsS, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨Or.inl rfl, 0, 0, by omega, by simp, by omega, by omega⟩
    · exact Or.inl ⟨Or.inr rfl, 0, 0, by omega, by simp, by omega, by omega⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp only [wsA, List.mem_flatMap, List.mem_range] at h
    obtain ⟨l, hl, t, ht, h⟩ := h
    obtain ⟨hn, c, hc, hlo, hw⟩ := mem_wsSp h
    have hf := (split_fits hl ht c hc).1
    have hm := KW_pos (KL N) (l + 1)
    simp only at hn hlo hw
    exact Or.inl ⟨hn, l + 1, (3 * t + c) * KW (KL N) (l + 1), by omega, hlo, by rw [hw]; omega,
      by rw [hw]; omega⟩
  · have hw : 0 < wd := by
      simp only [wsB, List.mem_flatMap, List.mem_range] at h
      obtain ⟨t, -, h⟩ := h
      obtain ⟨-, -, -, -, hw⟩ := mem_wsBs h
      simp only at hw
      omega
    obtain ⟨hn, x, hlo, hx⟩ := mem_wsB h
    simp only at hn hlo hx
    exact Or.inr (Or.inl ⟨hn, KL N, x, Nat.le_refl _, hlo, hx, hw⟩)
  · have hw : 0 < wd := by
      simp only [wsC, List.mem_flatMap, List.mem_range] at h
      obtain ⟨l, hl, t, -, h⟩ := h
      obtain ⟨-, x, -, -, hw⟩ := mem_wsCb hl h
      exact hw
    obtain ⟨hn, l, x, hl, hlo, hx⟩ := mem_wsC h
    simp only at hn hlo hx
    exact Or.inr (Or.inl ⟨hn, l, x, by omega, hlo, hx, hw⟩)

theorem winOf_mem {N : Nat} {p : Process2} (hp : p ∈ kProcs N) : winOf N p ∈ wsAll N := by
  rw [wsAll, ← kProcs_winOf]
  exact List.mem_map_of_mem hp

/-! ## 2e. The comb profile -/

section comb

variable {N : Nat} (hN : 1 ≤ N)
include hN

theorem kM_getElem?_of_mem {p : Process2} (h : p ∈ kProcs N) : ∃ k : Nat, (kM N).processes[k]? = some p := by
  rw [kProcs, ← kM_processes hN, List.mem_iff_getElem?] at h
  obtain ⟨k, hk⟩ := h
  rw [Array.getElem?_toList] at hk
  exact ⟨k, hk⟩

theorem kM_mem_of_getElem? {k : Nat} {p : Process2} (h : (kM N).processes[k]? = some p) : p ∈ kProcs N := by
  rw [kProcs, ← kM_processes hN, List.mem_iff_getElem?]
  exact ⟨k, by rw [Array.getElem?_toList]; exact h⟩

theorem kM_writes {j : Nat} {w : Win} (h : (kM N).Writes j w) :
    ∃ p, (kM N).processes[j]? = some p ∧ p ∈ kProcs N ∧ w = winOf N p := by
  obtain ⟨t, e, hp, hw⟩ := h
  have hm := kM_mem_of_getElem? hN hp
  obtain ⟨-, hws⟩ := kProcs_wins hN _ hm t e rfl
  rw [hws, List.mem_singleton] at hw
  exact ⟨_, hp, hm, hw⟩

omit hN in
theorem kProcs_pairwise : (kProcs N).Pairwise fun p q => Win.overlaps (winOf N p) (winOf N q) = false := by
  have h := ws_pairwise N
  rw [← kProcs_winOf, List.pairwise_map] at h
  exact h

theorem kM_disjoint : ∀ i j wi wj, i ≠ j → (kM N).Writes i wi → (kM N).Writes j wj →
    Win.overlaps wi wj = false := by
  intro i j wi wj hij hi hj
  obtain ⟨p, hp, -, rfl⟩ := kM_writes hN hi
  obtain ⟨q, hq, -, rfl⟩ := kM_writes hN hj
  have hpw := kProcs_pairwise (N := N)
  rw [kProcs, ← kM_processes hN, List.pairwise_iff_getElem] at hpw
  rw [← Array.getElem?_toList, List.getElem?_eq_some_iff] at hp hq
  obtain ⟨hil, hp⟩ := hp
  obtain ⟨hjl, hq⟩ := hq
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have := hpw i j hil hjl h
    rw [hp, hq] at this
    exact this
  · have := hpw j i hjl hil h
    rw [hp, hq] at this
    rw [Win.overlaps_comm]
    exact this

theorem kws_inWidth {w : Win} (h : w ∈ wsAll N) :
    ∃ dw, (kM N).declWidth w.1 = some dw ∧ w.2.1 + w.2.2 ≤ dw := by
  rcases h' : w with ⟨n, lo, wd⟩
  rw [h'] at h
  simp only [wsAll, List.mem_append] at h
  rcases h with h | h | h | h
  · simp only [wsS, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    have := Nat.le_mul_of_pos_left (KR (KL N)) (show 0 < KL N + 1 by omega)
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨_, kM_declWidth_av N, by simp; omega⟩
    · exact ⟨_, kM_declWidth_bv N, by simp; omega⟩
    · exact ⟨_, kM_declWidth_p N, by simp⟩
  · simp only [wsA, List.mem_flatMap, List.mem_range] at h
    obtain ⟨l, hl, t, ht, h⟩ := h
    obtain ⟨hn, c, hc, hlo, hw⟩ := mem_wsSp h
    have hf := (split_fits hl ht c hc).1
    have hr := rowMajor_le (K := KR (KL N)) (show l + 1 < KL N + 1 by omega)
    simp only at hn hlo hw
    subst hlo hw
    rcases hn with rfl | rfl
    · exact ⟨_, kM_declWidth_av N, by simp only; omega⟩
    · exact ⟨_, kM_declWidth_bv N, by simp only; omega⟩
  · obtain ⟨hn, x, hlo, hx⟩ := mem_wsB h
    have hr : KL N * KS (KL N) + KS (KL N) = (KL N + 1) * KS (KL N) := (Nat.succ_mul _ _).symm
    simp only at hn hlo hx
    subst hn hlo
    exact ⟨_, kM_declWidth_rv N, by simp only; omega⟩
  · obtain ⟨hn, l, x, hl, hlo, hx⟩ := mem_wsC h
    have hr := rowMajor_le (K := KS (KL N)) (show l < KL N + 1 by omega)
    simp only at hn hlo hx
    subst hn hlo
    exact ⟨_, kM_declWidth_rv N, by simp only; omega⟩

omit hN in
theorem kProcs_rhsFree : ∀ p ∈ kProcs N, (rhsOf p).unsupportedFree = true := by
  refine kProcs_forall ?_ ?_ ?_ ?_
  · intro p hp
    simp only [kStatics, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rfl
  · intro l t _ _ p hp
    simp only [splitP, spLoP, spHiP, spMidP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro t _ p hp
    simp only [baseP, bsP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro l t _ _ p hp
    simp only [combP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> rfl

def kNames : List String := ["a", "b", "p", "av", "bv", "rv"]

omit hN in
theorem kProcs_rhsDeclared : ∀ p ∈ kProcs N, ((rhsOf p).idents.all fun x => x ∈ kNames) = true := by
  refine kProcs_forall ?_ ?_ ?_ ?_
  · intro p hp
    simp only [kStatics, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rfl
  · intro l t _ _ p hp
    simp only [splitP, spLoP, spHiP, spMidP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro t _ p hp
    simp only [baseP, bsP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro l t _ _ p hp
    simp only [combP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem kM_comb : CombDesign (kM N) where
  nodup := by
    rw [kM_decls]
    simp only [kDecls, List.map_cons, List.map_nil]
    decide
  assign := by
    intro j p hp
    have hm := kM_mem_of_getElem? hN hp
    rcases kProcs_shape hN p hm with ⟨n, lo, w, e, rfl, -⟩ | ⟨e, rfl⟩
    · exact ⟨_, _, _, rfl, (kProcs_wins hN _ hm _ _ rfl).1⟩
    · exact ⟨_, _, _, rfl, (kProcs_wins hN _ hm _ _ rfl).1⟩
  inWidth := by
    intro j n lo w h
    obtain ⟨p, -, hm, hw⟩ := kM_writes hN h
    have := kws_inWidth hN (winOf_mem hm)
    rw [← hw] at this
    exact this
  notInput := by
    rintro n ⟨j, lo, w, h⟩
    obtain ⟨p, -, hm, hw⟩ := kM_writes hN h
    have hmem := winOf_mem hm
    rw [← hw] at hmem
    have hr := wsAll_row hmem
    rw [kM_inputNames]
    rcases hr with ⟨rfl | rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  disjoint := kM_disjoint hN
  selfDisjoint := by
    intro j t e hp
    rcases kProcs_shape hN _ (kM_mem_of_getElem? hN hp) with ⟨n, lo, w, e', h, -⟩ | ⟨e', h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
      exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro j t e hp
    exact kProcs_rhsFree _ (kM_mem_of_getElem? hN hp)
  rhsDeclared := by
    intro j t e hp x hx
    have h := List.all_eq_true.mp (kProcs_rhsDeclared _ (kM_mem_of_getElem? hN hp)) x hx
    rw [kM_decls]
    simpa [kNames, kDecls] using h
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [kM_decls] at hdc
    simp [kDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [kM_decls] at hdc
    simp [kDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end comb

/-! ## 2f. Acyclicity: operand rows by level, the base level, then product rows bottom up -/

/-- The rank of a written window: operand row `r` ranks `r`; the base product row `L` ranks `L + 1`;
product row `r < L` ranks `2L + 1 - r`; the output ranks `2L + 2`. -/
def rkW (L : Nat) (w : Win) : Nat :=
  if w.1 = "av" ∨ w.1 = "bv" then w.2.1 / KR L
  else if w.1 = "rv" then (if w.2.1 / KS L = L then L + 1 else 2 * L + 1 - w.2.1 / KS L)
  else 2 * L + 2

def kRank (N : Nat) (k : Nat) : Nat :=
  match (kM N).processes[k]? with
  | some p => rkW (KL N) (winOf N p)
  | none => 0

theorem rowdiv {M l i : Nat} (hi : i < M) : (l * M + i) / M = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < M), Nat.div_eq_of_lt hi, Nat.zero_add]

theorem rkW_ab {L r x w : Nat} {n : String} (hn : n = "av" ∨ n = "bv") (hx : x < KR L) :
    rkW L (n, r * KR L + x, w) = r := by
  simp only [rkW, hn, if_true, rowdiv hx]

theorem rkW_rv {L r x w : Nat} (hx : x < KS L) :
    rkW L ("rv", r * KS L + x, w) = if r = L then L + 1 else 2 * L + 1 - r := by
  simp [rkW, rowdiv hx]

theorem rkW_p {L lo w : Nat} : rkW L ("p", lo, w) = 2 * L + 2 := by simp [rkW]

/-- Two overlapping windows that each fit one row of width `K` are in the same row. -/
theorem row_eq {K r r' x x' w w' : Nat} (hx : x + w ≤ K) (hx' : x' + w' ≤ K)
    (h1 : r * K + x < r' * K + x' + w') (h2 : r' * K + x' < r * K + x + w) : r = r' := by
  rcases Nat.lt_trichotomy r r' with h | h | h
  · have := rowMajor_le (K := K) h; omega
  · exact h
  · have := rowMajor_le (K := K) h; omega

/-- A window read `[r*K + x, +w)` of signal `n` that overlaps a written window lies in that window's row. -/
theorem read_hits {N : Nat} {n : String} {r x w : Nat} {ww : Win} (hw : ww ∈ wsAll N)
    (hov : (ReadWin.win n (r * (if n = "rv" then KS (KL N) else KR (KL N)) + x) w).overlaps ww = true)
    (hx : x + w ≤ (if n = "rv" then KS (KL N) else KR (KL N))) (hn : n = "av" ∨ n = "bv" ∨ n = "rv") :
    ((n = "av" ∨ n = "bv") ∧ rkW (KL N) ww = r) ∨ (n = "rv" ∧ rkW (KL N) ww = rkW (KL N) ("rv", r * KS (KL N), 1)) := by
  obtain ⟨nw, lo, wd⟩ := ww
  simp only [ReadWin.overlaps, Win.overlaps_eq_true] at hov
  obtain ⟨rfl, h1, h2⟩ := hov
  rcases wsAll_row hw with ⟨hn', r', x', -, hlo, hx', hw'⟩ | ⟨hn', r', x', -, hlo, hx', hw'⟩ | hn'
  · have hne : n ≠ "rv" := by rcases hn' with rfl | rfl <;> decide
    simp only [hne, if_false] at h1 h2 hx
    subst hlo
    have := row_eq hx hx' h1 h2
    subst this
    exact Or.inl ⟨hn', rkW_ab hn' (by omega)⟩
  · subst hn'
    simp only [if_true] at h1 h2 hx
    subst hlo
    have := row_eq hx hx' h1 h2
    subst this
    have hS := KS_eq (KL N)
    have hR := KR_pos (KL N)
    refine Or.inr ⟨rfl, ?_⟩
    rw [rkW_rv (by omega), show r * KS (KL N) = r * KS (KL N) + 0 by rfl, rkW_rv (by omega)]
  · obtain ⟨hn', -⟩ := hn'
    subst hn'
    rcases hn with h | h | h <;> exact absurd h (by decide)

theorem rkW_rv_le {L r x w : Nat} (hx : x < KS L) (hr : r ≤ L) : rkW L ("rv", r * KS L + x, w) ≤ 2 * L + 1 := by
  rw [rkW_rv hx]
  split <;> omega

theorem read_ab {N : Nat} {n : String} {r x w : Nat} {ww : Win} (hw : ww ∈ wsAll N)
    (hov : (ReadWin.win n (r * KR (KL N) + x) w).overlaps ww = true)
    (hx : x + w ≤ KR (KL N)) (hn : n = "av" ∨ n = "bv") : rkW (KL N) ww = r := by
  have hne : ¬ (n = "rv") := by rcases hn with rfl | rfl <;> decide
  have h := read_hits (n := n) (r := r) (x := x) (w := w) hw (by simpa [hne] using hov)
    (by simpa [hne] using hx) (by rcases hn with h | h <;> simp [h])
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h hne

theorem read_rv {N : Nat} {r x w : Nat} {ww : Win} (hw : ww ∈ wsAll N)
    (hov : (ReadWin.win "rv" (r * KS (KL N) + x) w).overlaps ww = true)
    (hx : x + w ≤ KS (KL N)) : rkW (KL N) ww = rkW (KL N) ("rv", r * KS (KL N), 1) := by
  have h := read_hits (n := "rv") (r := r) (x := x) (w := w) hw (by simpa using hov) (by simpa using hx)
    (by simp)
  rcases h with ⟨h, -⟩ | ⟨-, h⟩
  · rcases h with h | h <;> exact absurd h (by decide)
  · exact h

theorem read_rv_any {N : Nat} {lo w : Nat} {ww : Win} (hw : ww ∈ wsAll N)
    (hov : (ReadWin.win "rv" lo w).overlaps ww = true) : rkW (KL N) ww ≤ 2 * KL N + 1 := by
  obtain ⟨nw, lw, wd⟩ := ww
  simp only [ReadWin.overlaps, Win.overlaps_eq_true] at hov
  obtain ⟨rfl, -, -⟩ := hov
  rcases wsAll_row hw with ⟨hn, -⟩ | ⟨-, r, x, hr, hlo, hx, hw0⟩ | ⟨hn, -⟩
  · rcases hn with h | h <;> exact absurd h (by decide)
  · subst hlo
    exact rkW_rv_le (by omega) hr
  · exact absurd hn (by decide)

/-- **Every read is of a strictly lower rank** (reader by reader). -/
theorem kProcs_reads {N : Nat} (hN : 1 ≤ N) : ∀ p ∈ kProcs N, ∀ r ∈ (rhsOf p).reads, ∀ ww ∈ wsAll N,
    r.overlaps ww = true → rkW (KL N) ww < rkW (KL N) (winOf N p) := by
  have hR := KR_pos (KL N)
  have hS := KS_eq (KL N)
  refine kProcs_forall ?_ ?_ ?_ ?_
  · intro p hp r hr ww hww hov
    simp only [kStatics, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · simp [rhsOf, Expr2.reads] at hr
      subst hr
      obtain ⟨nw, lw, wd⟩ := ww
      simp only [ReadWin.overlaps, beq_iff_eq] at hov
      subst hov
      rcases wsAll_row hww with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> (try rcases h with h | h) <;>
        exact absurd h (by decide)
    · simp [rhsOf, Expr2.reads] at hr
      subst hr
      obtain ⟨nw, lw, wd⟩ := ww
      simp only [ReadWin.overlaps, beq_iff_eq] at hov
      subst hov
      rcases wsAll_row hww with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> (try rcases h with h | h) <;>
        exact absurd h (by decide)
    · simp [rhsOf, Expr2.reads, Expr2.sliceReads] at hr
      subst hr
      have := read_rv_any hww hov
      simp only [winOf, rkW_p]
      omega
  · intro l t hl ht p hp r hr ww hww hov
    have hf0 := split_fits hl ht 0 (by omega)
    have hf1 := split_fits hl ht 1 (by omega)
    have hf2 := split_fits hl ht 2 (by omega)
    have hm := KW_pos (KL N) (l + 1)
    simp only [splitP, spLoP, spHiP, spMidP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rhsOf, Expr2.reads, Expr2.sliceReads] at hr <;>
      (try rcases hr with rfl | rfl) <;> (try subst hr) <;>
      simp only [winOf] <;>
      first
        | (rw [read_ab hww hov (by omega) (by simp), rkW_ab (by simp) (by omega)]; omega)
        | (rw [read_ab hww hov (by omega) (by simp), rkW_ab (by simp) (by omega)]; omega)
  · intro t ht p hp r hr ww hww hov
    have h4 : 4 * t + 4 ≤ KR (KL N) := by
      have := node_fits (L := KL N) (l := KL N) (t := t) (Nat.le_refl _) ht
      unfold KW at this
      simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at this
      omega
    simp only [baseP, bsP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rhsOf, Expr2.reads, Expr2.sliceReads] at hr <;>
      simp only [winOf] <;>
      rw [rkW_rv (by omega), if_pos rfl] <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [read_ab hww hov (by omega) (by simp)]; omega)
  · intro l t hl ht p hp r hr ww hww hov
    have hm4 := KW_pos (KL N) (l + 1)
    have hWm := KW_succ hl
    have hpar := comb_slot hl ht
    have hch : ∀ c, c ≤ 2 → (3 * t + c) * KW (KL N) l + KW (KL N) l ≤ KS (KL N) := by
      intro c hc
      have := node_fits (L := KL N) (l := l + 1) (t := 3 * t + c) (by omega) (by rw [Nat.pow_succ]; omega)
      have h2 : (3 * t + c + 1) * KW (KL N) (l + 1) = (3 * t + c) * KW (KL N) (l + 1) + KW (KL N) (l + 1) :=
        Nat.succ_mul _ _
      have h3 : (3 * t + c) * KW (KL N) l = 2 * ((3 * t + c) * KW (KL N) (l + 1)) := by
        rw [hWm, Nat.mul_left_comm]
      omega
    have h0 := hch 0 (by omega)
    have h1 := hch 1 (by omega)
    have h2 := hch 2 (by omega)
    have h0' : 3 * t * KW (KL N) l + KW (KL N) l ≤ KS (KL N) := by simpa using h0
    have hlt : (if l + 1 = KL N then KL N + 1 else 2 * KL N + 1 - (l + 1)) < 2 * KL N + 1 - l := by
      split <;> omega
    have hne : l ≠ KL N := by omega
    simp only [combP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      simp [rhsOf, Expr2.reads, Expr2.sliceReads] at hr <;>
      simp only [winOf] <;>
      rw [rkW_rv (by omega), if_neg hne] <;>
      (try rcases hr with rfl | rfl | rfl | rfl) <;> (try subst hr) <;>
      (rw [read_rv hww hov (by omega), show (l + 1) * KS (KL N) = (l + 1) * KS (KL N) + 0 by rfl,
        rkW_rv (by omega)]; exact hlt)

theorem kM_acyclic {N : Nat} (hN : 1 ≤ N) : Acyclic (kM N) := by
  refine ⟨kRank N, ?_⟩
  intro i j ti ei tj ej wj hi hj hwj ⟨r, hr, hov⟩
  have hmi := kM_mem_of_getElem? hN hi
  have hmj := kM_mem_of_getElem? hN hj
  obtain ⟨-, hws⟩ := kProcs_wins hN _ hmj tj ej rfl
  rw [hws, List.mem_singleton] at hwj
  subst hwj
  have hlt := kProcs_reads hN _ hmi r hr _ (winOf_mem hmj) hov
  simp only [kRank, hi, hj]
  exact hlt

/-! ## 2g. `design.sem N` is the instantiated design -/

theorem kara_sem_eq {N : Nat} (hN : 1 ≤ N) : design.sem N = kM N := by
  show design.pdesign.instantiateGD2 [(N : Int)] = kM N
  refine PDesign.instantiateGD2_of_combDesign (kara_instantiate2 hN) (kM_comb hN) ?_
  intro i n lo w h
  obtain ⟨p, -, hm, hw⟩ := kM_writes hN h
  have hmem := winOf_mem hm
  rw [← hw] at hmem
  rcases wsAll_row hmem with ⟨-, -, -, -, -, -, hw0⟩ | ⟨-, -, -, -, -, -, hw0⟩ | ⟨-, hw0⟩
  · exact hw0
  · exact hw0
  · omega

/-- **The structure step, for every `N ≥ 1`**: the design is in the comb profile and acyclic. -/
theorem kara_structure {N : Nat} (hN : 1 ≤ N) : CombDesign (design.sem N) ∧ Acyclic (design.sem N) := by
  rw [kara_sem_eq hN]
  exact ⟨kM_comb hN, kM_acyclic hN⟩

/-! # Part 3. The arithmetic of carry-less products and of one Karatsuba step

Copied from `design/tasks-week2/clmul/karatsuba/Karatsuba.lean` (the array-view part left out): `bx`, the
Spec's double sum `cl`, the Karatsuba identity over coefficient functions (`karatsuba_full`) and the
combination layer's specification (`comb_spec`). -/

namespace ClmulArith


open SvGolf.Tasks.Clmul

/-- `bx f n`: the XOR of `f 0, …, f (n-1)`. -/
def bx (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => bx f n ^^ f n

theorem bx_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j, j < n → f j = g j) : bx f n = bx g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bx]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem bx_trunc {f : Nat → Bool} {n m : Nat} (hnm : n ≤ m) (h : ∀ j, n ≤ j → j < m → f j = false) :
    bx f m = bx f n := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst hn; rfl
    · simp only [bx]
      rw [ih (by omega) (fun j hj1 hj2 => h j hj1 (by omega)), h m (by omega) (by omega)]
      simp

theorem foldl_xor (f : Nat → Bool) (n : Nat) (acc : Bool) :
    (List.range n).foldl (fun acc i => acc ^^ f i) acc = (acc ^^ bx f n) := by
  induction n generalizing acc with
  | zero => simp [bx]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]
    simp only [bx]
    cases acc <;> cases bx f n <;> cases f n <;> rfl

/-- The Spec's double sum is the nested `bx`. -/
theorem coeff_eq (N : Nat) (a b : BitVec N) (k : Nat) :
    coeff N a b k =
      bx (fun i => bx (fun j => decide (i + j = k) && a.getLsbD i && b.getLsbD j) N) N := by
  unfold coeff
  simp only [foldl_xor]
  simp [bx]

theorem bx_pair (i k : Nat) (x : Bool) (c : Nat → Bool) (n : Nat) :
    bx (fun j => decide (i + j = k) && x && c j) n = (decide (i ≤ k ∧ k - i < n) && x && c (k - i)) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    simp only [bx, ih]
    by_cases h : i + n = k
    · have h1 : k - i = n := by omega
      have h2 : ¬ (k - i < n) := by omega
      have h3 : i ≤ k ∧ k - i < n + 1 := by omega
      simp [h, h1, h2, h3]
    · have h4 : (decide (i ≤ k ∧ k - i < n + 1)) = (decide (i ≤ k ∧ k - i < n)) := by
        apply decide_eq_decide.mpr; omega
      have h5 : decide (i + n = k) = false := by simp [h]
      rw [h5, h4]; simp

theorem getLsbD_ofBits : ∀ (n : Nat) (f : Nat → Bool) (k : Nat),
    (ofBits n f).getLsbD k = (decide (k < n) && f k)
  | 0, f, k => by simp [ofBits]
  | n + 1, f, k => by
    rw [ofBits, BitVec.getLsbD_append, getLsbD_ofBits n]
    cases k with
    | zero => simp [BitVec.getLsbD_ofBool]
    | succ k => simp [BitVec.getLsbD_ofBool]


theorem bx_succ (f : Nat → Bool) (n : Nat) : bx f (n + 1) = (bx f n ^^ f n) := rfl

theorem bx_false {f : Nat → Bool} {n : Nat} (h : ∀ t, t < n → f t = false) : bx f n = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bx_succ, ih (fun t ht => h t (by omega)), h n (by omega)]; rfl

/-! ## One level of Karatsuba -/

/-- The carry-less product of two `n`-bit operands, bit `k`: the double sum of the Spec. -/
def cl (n : Nat) (A B : Nat → Bool) (k : Nat) : Bool :=
  bx (fun i => bx (fun j => decide (i + j = k) && A i && B j) n) n

theorem bx_add (f : Nat → Bool) (m n : Nat) :
    bx f (m + n) = (bx f m ^^ bx (fun t => f (m + t)) n) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    rw [← Nat.add_assoc, bx_succ, ih, bx_succ]
    cases bx f m <;> cases bx (fun t => f (m + t)) n <;> cases f (m + n) <;> rfl

theorem bx_xor (f g : Nat → Bool) (n : Nat) :
    bx (fun t => f t ^^ g t) n = (bx f n ^^ bx g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bx_succ, ih, bx_succ, bx_succ]
    cases bx f n <;> cases bx g n <;> cases f n <;> cases g n <;> rfl

theorem bx_and (c : Bool) (f : Nat → Bool) (n : Nat) :
    bx (fun t => c && f t) n = (c && bx f n) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    rw [bx_succ, ih, bx_succ]
    cases c <;> cases bx f n <;> cases f n <;> rfl

theorem cl_big {n : Nat} {A B : Nat → Bool} {k : Nat} (hk : 2 * n ≤ k + 1) : cl n A B k = false := by
  unfold cl
  apply bx_false
  intro i hi
  apply bx_false
  intro j hj
  have : ¬ (i + j = k) := by omega
  simp [this]

/-- A double sum shifted by `s`: only `k ≥ s` sees it, at `k - s`. -/
theorem cl_shift (n s k : Nat) (P Q : Nat → Bool) :
    bx (fun i => bx (fun j => decide (i + j + s = k) && P i && Q j) n) n =
      (decide (s ≤ k) && cl n P Q (k - s)) := by
  by_cases h : s ≤ k
  · have e : ∀ i j, decide (i + j + s = k) = decide (i + j = k - s) := by
      intro i j; apply decide_eq_decide.mpr; omega
    simp only [e, h, decide_true, Bool.true_and]
    rfl
  · have e : ∀ i j, decide (i + j + s = k) = false := by
      intro i j; simp; omega
    have h' : decide (s ≤ k) = false := by simp; omega
    simp only [e, h', Bool.false_and]
    apply bx_false; intro i hi; apply bx_false; intro j hj; rfl

theorem cl_sum (H : Nat) (X Y : Nat → Bool) (m : Nat) :
    cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) m =
      (cl H X Y m ^^ (cl H X (fun j => Y (H + j)) m ^^ (cl H (fun i => X (H + i)) Y m ^^
        cl H (fun i => X (H + i)) (fun j => Y (H + j)) m))) := by
  unfold cl
  have e : ∀ i j, (decide (i + j = m) && (X i ^^ X (H + i)) && (Y j ^^ Y (H + j))) =
      ((decide (i + j = m) && X i && Y j) ^^ ((decide (i + j = m) && X i && Y (H + j)) ^^
        ((decide (i + j = m) && X (H + i) && Y j) ^^ (decide (i + j = m) && X (H + i) && Y (H + j))))) := by
    intro i j
    cases decide (i + j = m) <;> cases X i <;> cases X (H + i) <;> cases Y j <;> cases Y (H + j) <;> rfl
  simp only [e, bx_xor]

theorem karatsuba (H : Nat) (X Y : Nat → Bool) (k : Nat) :
    cl (H + H) X Y k =
      (cl H X Y k ^^
        ((decide (H ≤ k) && cl H X (fun j => Y (H + j)) (k - H)) ^^
          ((decide (H ≤ k) && cl H (fun i => X (H + i)) Y (k - H)) ^^
            (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H)))))) := by
  have h1 : ∀ i, bx (fun j => decide (i + j = k) && X i && Y j) (H + H) =
      (bx (fun j => decide (i + j = k) && X i && Y j) H ^^
        bx (fun u => decide (i + (H + u) = k) && X i && Y (H + u)) H) := fun i => bx_add _ H H
  have h2 : ∀ t, bx (fun j => decide (H + t + j = k) && X (H + t) && Y j) (H + H) =
      (bx (fun j => decide (H + t + j = k) && X (H + t) && Y j) H ^^
        bx (fun u => decide (H + t + (H + u) = k) && X (H + t) && Y (H + u)) H) := fun t => bx_add _ H H
  have hA01 : bx (fun i => bx (fun u => decide (i + (H + u) = k) && X i && Y (H + u)) H) H =
      (decide (H ≤ k) && cl H X (fun j => Y (H + j)) (k - H)) := by
    have e : ∀ i u, decide (i + (H + u) = k) = decide (i + u + H = k) := by
      intro i u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H H k X (fun j => Y (H + j))
  have hA10 : bx (fun t => bx (fun u => decide (H + t + u = k) && X (H + t) && Y u) H) H =
      (decide (H ≤ k) && cl H (fun i => X (H + i)) Y (k - H)) := by
    have e : ∀ t u, decide (H + t + u = k) = decide (t + u + H = k) := by
      intro t u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H H k (fun i => X (H + i)) Y
  have hA11 : bx (fun t => bx (fun u => decide (H + t + (H + u) = k) && X (H + t) && Y (H + u)) H) H =
      (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H))) := by
    have e : ∀ t u, decide (H + t + (H + u) = k) = decide (t + u + (H + H) = k) := by
      intro t u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H (H + H) k (fun i => X (H + i)) (fun j => Y (H + j))
  show bx (fun i => bx (fun j => decide (i + j = k) && X i && Y j) (H + H)) (H + H) = _
  rw [bx_add]
  simp only [h1, h2, bx_xor]
  rw [hA01, hA10, hA11]
  have hL : cl H X Y k = bx (fun i => bx (fun j => decide (i + j = k) && X i && Y j) H) H := rfl
  rw [hL]
  simp only [Bool.xor_assoc]

theorem karatsuba_full (H : Nat) (X Y : Nat → Bool) (k : Nat) :
    cl (H + H) X Y k =
      (cl H X Y k ^^
        ((decide (H ≤ k) && (cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (k - H) ^^
            cl H X Y (k - H) ^^ cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - H))) ^^
          (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H))))) := by
  rw [karatsuba, cl_sum]
  generalize cl H X Y k = l0
  generalize cl H X Y (k - H) = l1
  generalize cl H X (fun j => Y (H + j)) (k - H) = a
  generalize cl H (fun i => X (H + i)) Y (k - H) = b
  generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - H) = h1
  generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H)) = h2
  generalize decide (H ≤ k) = c1
  generalize decide (H + H ≤ k) = c2
  cases l0 <;> cases l1 <;> cases a <;> cases b <;> cases h1 <;> cases h2 <;> cases c1 <;> cases c2 <;> rfl


theorem cl_congr {n : Nat} {A A' B B' : Nat → Bool} (hA : ∀ i, i < n → A i = A' i)
    (hB : ∀ j, j < n → B j = B' j) (k : Nat) : cl n A B k = cl n A' B' k := by
  unfold cl
  apply bx_congr
  intro i hi
  apply bx_congr
  intro j hj
  rw [hA i hi, hB j hj]

/-- Operands that vanish from `N` on: the sums over `M ≥ N` positions see only the first `N`. -/
theorem cl_trunc {N M : Nat} (hNM : N ≤ M) {A B : Nat → Bool} (hA : ∀ i, N ≤ i → A i = false)
    (hB : ∀ j, N ≤ j → B j = false) (k : Nat) : cl M A B k = cl N A B k := by
  unfold cl
  have inner : ∀ i, bx (fun j => decide (i + j = k) && A i && B j) M =
      bx (fun j => decide (i + j = k) && A i && B j) N := by
    intro i
    apply bx_trunc hNM
    intro j hj _
    rw [hB j hj]; simp
  simp only [inner]
  apply bx_trunc hNM
  intro i hi _
  rw [bx_false]
  intro j hj
  rw [hA i hi]; simp

theorem comb_spec {H : Nat} (hH : 1 ≤ H) {X Y : Nat → Bool} {PL PH PM PF : Nat → Bool}
    (hL : ∀ k, k < 2 * H - 1 → PL k = cl H X Y k)
    (hHh : ∀ k, k < 2 * H - 1 → PH k = cl H (fun i => X (H + i)) (fun j => Y (H + j)) k)
    (hM : ∀ k, k < 2 * H - 1 → PM k = cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) k)
    (c0 : ∀ i, i < H → PF i = PL i)
    (c1 : ∀ i, i + 1 < H → PF (H + i) = (PL (H + i) ^^ (PM i ^^ PL i ^^ PH i)))
    (c1' : PF (2 * H - 1) = (PM (H - 1) ^^ PL (H - 1) ^^ PH (H - 1)))
    (c2 : ∀ i, i + 1 < H → PF (2 * H + i) = (PH i ^^ (PM (H + i) ^^ PL (H + i) ^^ PH (H + i))))
    (c3 : ∀ i, i < H → PF (3 * H - 1 + i) = PH (H - 1 + i)) :
    ∀ k, k < 4 * H - 1 → PF k = cl (H + H) X Y k := by
  intro k hk
  rw [karatsuba_full]
  have big : ∀ (A B : Nat → Bool) m, 2 * H - 1 ≤ m → cl H A B m = false :=
    fun A B m hm => cl_big (by omega)
  by_cases h1 : k < H
  · have d1 : decide (H ≤ k) = false := by simp; omega
    have d2 : decide (H + H ≤ k) = false := by simp; omega
    rw [c0 k h1, hL k (by omega), d1, d2]; simp
  by_cases h2 : k < 2 * H - 1
  · obtain ⟨i, rfl⟩ : ∃ i, k = H + i := ⟨k - H, by omega⟩
    have d1 : decide (H ≤ H + i) = true := by simp
    have d2 : decide (H + H ≤ H + i) = false := by simp; omega
    have e1 : H + i - H = i := by omega
    rw [c1 i (by omega), hL (H + i) h2, hL i (by omega), hHh i (by omega), hM i (by omega), d1, d2, e1]
    simp
  by_cases h3 : k = 2 * H - 1
  · subst h3
    have d1 : decide (H ≤ 2 * H - 1) = true := by simp; omega
    have d2 : decide (H + H ≤ 2 * H - 1) = false := by simp; omega
    have e1 : 2 * H - 1 - H = H - 1 := by omega
    rw [c1', hM (H - 1) (by omega), hL (H - 1) (by omega), hHh (H - 1) (by omega), d1, d2, e1,
      big X Y (2 * H - 1) (by omega)]
    simp
  by_cases h4 : k < 3 * H - 1
  · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * H + i := ⟨k - 2 * H, by omega⟩
    have d1 : decide (H ≤ 2 * H + i) = true := by simp; omega
    have d2 : decide (H + H ≤ 2 * H + i) = true := by simp; omega
    have e1 : 2 * H + i - H = H + i := by omega
    have e2 : 2 * H + i - (H + H) = i := by omega
    rw [c2 i (by omega), hHh i (by omega), hM (H + i) (by omega), hL (H + i) (by omega),
      hHh (H + i) (by omega), d1, d2, e1, e2, big X Y (2 * H + i) (by omega)]
    simp only [Bool.true_and, Bool.false_xor]
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) i = a
    generalize cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (H + i) = m
    generalize cl H X Y (H + i) = l
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (H + i) = h
    cases a <;> cases m <;> cases l <;> cases h <;> rfl
  · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * H - 1 + i := ⟨k - (3 * H - 1), by omega⟩
    have d1 : decide (H ≤ 3 * H - 1 + i) = true := by simp; omega
    have d2 : decide (H + H ≤ 3 * H - 1 + i) = true := by simp; omega
    have e1 : 3 * H - 1 + i - H = 2 * H - 1 + i := by omega
    have e2 : 3 * H - 1 + i - (H + H) = H - 1 + i := by omega
    have bm : cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (2 * H - 1 + i) = false :=
      big _ _ _ (by omega)
    have bl : cl H X Y (2 * H - 1 + i) = false := big _ _ _ (by omega)
    have bh : cl H (fun i => X (H + i)) (fun j => Y (H + j)) (2 * H - 1 + i) = false := big _ _ _ (by omega)
    have bl0 : cl H X Y (3 * H - 1 + i) = false := big _ _ _ (by omega)
    rw [c3 i (by omega), hHh (H - 1 + i) (by omega), d1, d2, e1, e2, bm, bl, bh, bl0]
    simp

end ClmulArith

/-! # Part 4. The settled state

## 4a. Known windows -/

open ClmulArith SvGolf.Tasks.Clmul

abbrev kb (b : Bool) : LVec := LVec.ofBitVec (BitVec.ofBool b)

/-- `w` known bits of `u` from `lo`, the bit `lo + k` being `g k`. -/
def KB (u : LVec) (lo : Nat) (g : Nat → Bool) (w : Nat) : Prop :=
  ∀ k, k < w → u.extract (lo + k) 1 = kb (g k)

theorem KB.win {u : LVec} {lo w : Nat} {g : Nat → Bool} (h : KB u lo g w) :
    u.extract lo w = LVec.ofBitVec (ofBits w g) := by
  apply LVec.eq_ofBitVec_of_extract_one (LVec.width_extract _ _ _)
  intro i hi
  rw [LVec.extract_extract _ (by omega), h i hi, getLsbD_ofBits]
  simp [hi]

theorem KB.of_win {u : LVec} {lo w : Nat} {X : BitVec w} (h : u.extract lo w = LVec.ofBitVec X) :
    KB u lo (fun k => X.getLsbD k) w := by
  intro k hk
  rw [← LVec.extract_extract u (show k + 1 ≤ w by omega), h, LVec.extract_one_ofBitVec X hk]

theorem KB.mono {u : LVec} {lo w w' : Nat} {g : Nat → Bool} (h : KB u lo g w) (hw : w' ≤ w) :
    KB u lo g w' := fun k hk => h k (by omega)

theorem KB.sub {u : LVec} {lo w : Nat} {g : Nat → Bool} (h : KB u lo g w) (a w' : Nat) (ha : a + w' ≤ w)
    (lo' : Nat) (hlo : lo' = lo + a) : KB u lo' (fun k => g (a + k)) w' := by
  intro k hk
  rw [hlo, Nat.add_assoc]
  exact h (a + k) (by omega)

theorem KB.congr {u : LVec} {lo w : Nat} {g g' : Nat → Bool} (h : KB u lo g w)
    (hg : ∀ k, k < w → g k = g' k) : KB u lo g' w := fun k hk => by rw [← hg k hk]; exact h k hk

theorem KB.addr {u : LVec} {lo lo' w : Nat} {g : Nat → Bool} (h : KB u lo g w) (hlo : lo = lo') :
    KB u lo' g w := hlo ▸ h

theorem ev_win {st : SvState} {n : String} {u : LVec} (hu : SvState.lookup st n = some u) {lo w : Nat}
    {g : Nat → Bool} (h : KB u lo g w) :
    evalPure2 st (.slice (.ident n) lo w) = .ok (LVec.ofBitVec (ofBits w g)) := by
  simp only [evalPure2_slice, evalPure2_ident_of_lookup hu, Pure2.res_ok_bind, Pure2.res_pure_eq, h.win]

/-- **One equation, read back**: the window a slice assign writes holds its right-hand side's value. -/
theorem eq_win {d : Design2} {st : SvState} (heqs : CombEqs d st) {j : Nat} {n : String} {lo w : Nat}
    {e : Expr2} (hp : d.processes[j]? = some (.assign (.slice n lo w) e)) {u : LVec}
    (hu : SvState.lookup st n = some u) {X : BitVec w} (he : evalPure2 st e = .ok (LVec.ofBitVec X)) :
    KB u lo (fun k => X.getLsbD k) w := by
  obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs hp he
  rw [hu, Option.some.injEq] at hold
  subst hold
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq] at hext
  exact KB.of_win hext

theorem getLsbD_ofBits_lt {w k : Nat} {g : Nat → Bool} (hk : k < w) : (ofBits w g).getLsbD k = g k := by
  rw [getLsbD_ofBits]
  simp [hk]

/-! ## 4b. Where each process sits -/

theorem mem_static {N : Nat} {p : Process2} (hp : p ∈ kStatics N) : p ∈ kProcs N := by
  simp only [kProcs, List.mem_append]
  exact Or.inl hp

theorem mem_split {N l t : Nat} {p : Process2} (hl : l < KL N) (ht : t < 3 ^ l) (hp : p ∈ splitP (KL N) l t) :
    p ∈ kProcs N := by
  simp only [kProcs, kGens, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr (Or.inl ⟨l, hl, t, ht, hp⟩)

theorem mem_base {N t : Nat} {p : Process2} (ht : t < 3 ^ KL N) (hp : p ∈ baseP (KL N) t) :
    p ∈ kProcs N := by
  simp only [kProcs, kGens, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr (Or.inr (Or.inl ⟨t, ht, hp⟩))

theorem mem_comb {N l t : Nat} {p : Process2} (hl : l < KL N) (ht : t < 3 ^ l) (hp : p ∈ combP (KL N) l t) :
    p ∈ kProcs N := by
  simp only [kProcs, kGens, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr (Or.inr (Or.inr ⟨l, hl, t, ht, hp⟩))

/-! ## 4c. The operands: what each level's operand rows hold -/

/-- **The operand of node `t` of level `l`**, bit `i`: level 0 is the zero-extended input `f`; child
`3t` of a node takes its low half, child `3t + 1` its high half, child `3t + 2` their XOR. -/
def opd (L : Nat) (f : Nat → Bool) : Nat → Nat → Nat → Bool
  | 0, _, i => f i
  | l + 1, t, i =>
      if t % 3 = 0 then opd L f l (t / 3) i
      else if t % 3 = 1 then opd L f l (t / 3) (i + KW L (l + 1))
      else (opd L f l (t / 3) i ^^ opd L f l (t / 3) (i + KW L (l + 1)))

theorem opd_c0 (L : Nat) (f : Nat → Bool) (l t i : Nat) : opd L f (l + 1) (3 * t + 0) i = opd L f l t i := by
  simp only [opd]
  rw [if_pos (by omega), show (3 * t + 0) / 3 = t by omega]

theorem opd_c1 (L : Nat) (f : Nat → Bool) (l t i : Nat) :
    opd L f (l + 1) (3 * t + 1) i = opd L f l t (i + KW L (l + 1)) := by
  simp only [opd]
  rw [if_neg (by omega), if_pos (by omega), show (3 * t + 1) / 3 = t by omega]

theorem opd_c2 (L : Nat) (f : Nat → Bool) (l t i : Nat) :
    opd L f (l + 1) (3 * t + 2) i = (opd L f l t i ^^ opd L f l t (i + KW L (l + 1))) := by
  simp only [opd]
  rw [if_neg (by omega), if_neg (by omega), show (3 * t + 2) / 3 = t by omega]

theorem KW0_le_KR (L : Nat) : KW L 0 ≤ KR L := by
  unfold KW KR
  have : 2 ^ L ≤ 3 ^ L := Nat.pow_le_pow_left (by decide) _
  simp only [Nat.sub_zero]
  omega

/-- **The operand invariant**: row `l` of `av` (of `bv`) holds, for every node `t < 3^l`, the node's
operand of `W l = 4 * 2^(L - l)` bits. -/
theorem opd_inv {N : Nat} (hN : 1 ≤ N) {st : SvState} (heqs : CombEqs (kM N) st) {v : String}
    (hv : v = "av" ∨ v = "bv") {u : LVec} (hu : SvState.lookup st v = some u) {f : Nat → Bool}
    (h0 : KB u 0 f (KR (KL N))) :
    ∀ l, l ≤ KL N → ∀ t, t < 3 ^ l →
      KB u (l * KR (KL N) + t * KW (KL N) l) (opd (KL N) f l t) (KW (KL N) l) := by
  intro l
  induction l with
  | zero =>
    intro _ t ht
    have ht0 : t = 0 := by simp at ht; omega
    subst ht0
    exact (KB.mono h0 (KW0_le_KR _)).addr (by simp)
  | succ l ih =>
    intro hl t ht
    have hl' : l < KL N := by omega
    obtain ⟨p, c, hc, rfl⟩ : ∃ p c, c < 3 ∧ t = 3 * p + c :=
      ⟨t / 3, t % 3, Nat.mod_lt _ (by decide), (Nat.div_add_mod t 3).symm⟩
    have hp3 : p < 3 ^ l := by rw [Nat.pow_succ] at ht; omega
    have hpar := ih (by omega) p hp3
    have hW := KW_succ hl'
    have hm := KW_pos (KL N) (l + 1)
    have hlo : KB u (l * KR (KL N) + p * KW (KL N) l) (opd (KL N) f l p) (KW (KL N) (l + 1)) :=
      KB.mono hpar (by omega)
    have hhi : KB u (l * KR (KL N) + (p * KW (KL N) l + KW (KL N) (l + 1)))
        (fun k => opd (KL N) f l p (KW (KL N) (l + 1) + k)) (KW (KL N) (l + 1)) :=
      KB.sub hpar _ _ (by omega) _ (by omega)
    have ev0 := ev_win hu hlo
    have ev1 := ev_win hu hhi
    have hmemv : ∀ q, q ∈ splitP (KL N) l p → q ∈ kProcs N := fun q hq => mem_split hl' hp3 hq
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
    · have hmem : spLoP v (KL N) l p ∈ kProcs N :=
        hmemv _ (by rcases hv with rfl | rfl <;> simp [splitP])
      obtain ⟨j, hj⟩ := kM_getElem?_of_mem hN hmem
      refine (eq_win heqs hj hu ev0).congr (fun k hk => ?_)
      rw [getLsbD_ofBits_lt hk, opd_c0]
    · have hmem : spHiP v (KL N) l p ∈ kProcs N :=
        hmemv _ (by rcases hv with rfl | rfl <;> simp [splitP])
      obtain ⟨j, hj⟩ := kM_getElem?_of_mem hN hmem
      refine (eq_win heqs hj hu ev1).congr (fun k hk => ?_)
      rw [getLsbD_ofBits_lt hk, opd_c1, Nat.add_comm k]
    · have hmem : spMidP v (KL N) l p ∈ kProcs N :=
        hmemv _ (by rcases hv with rfl | rfl <;> simp [splitP])
      obtain ⟨j, hj⟩ := kM_getElem?_of_mem hN hmem
      refine (eq_win heqs hj hu (evalPure2_xor_ofBitVec ev0 ev1)).congr (fun k hk => ?_)
      rw [BitVec.getLsbD_xor, getLsbD_ofBits_lt hk, getLsbD_ofBits_lt hk, opd_c2,
        Nat.add_comm (KW (KL N) (l + 1)) k]

/-! ## 4d. Gates over known bits -/

theorem ev_bit {st : SvState} {n : String} {u : LVec} {lo : Nat} {b : Bool}
    (hu : SvState.lookup st n = some u) (h : u.extract lo 1 = kb b) :
    evalPure2 st (.slice (.ident n) lo 1) = .ok (kb b) := by
  simp only [evalPure2_slice, evalPure2_ident_of_lookup hu, Pure2.res_ok_bind, Pure2.res_pure_eq, h]

theorem ev_and2 {st : SvState} {e₁ e₂ : Expr2} {a b : Bool} (h₁ : evalPure2 st e₁ = .ok (kb a))
    (h₂ : evalPure2 st e₂ = .ok (kb b)) : evalPure2 st (.binary .and e₁ e₂) = .ok (kb (a && b)) := by
  rw [evalPure2_and_ofBitVec h₁ h₂, BitVec.ofBool_and_ofBool]

theorem ev_xor2 {st : SvState} {e₁ e₂ : Expr2} {a b : Bool} (h₁ : evalPure2 st e₁ = .ok (kb a))
    (h₂ : evalPure2 st e₂ = .ok (kb b)) : evalPure2 st (.binary .xor e₁ e₂) = .ok (kb (a ^^ b)) := by
  rw [evalPure2_xor_ofBitVec h₁ h₂, BitVec.ofBool_xor_ofBool]

/-- A one-bit assign of a known bit, read back. -/
theorem eq_bit {d : Design2} {st : SvState} (heqs : CombEqs d st) {j : Nat} {n : String} {lo : Nat}
    {e : Expr2} (hp : d.processes[j]? = some (.assign (.slice n lo 1) e)) {u : LVec}
    (hu : SvState.lookup st n = some u) {b : Bool} (he : evalPure2 st e = .ok (kb b)) :
    u.extract lo 1 = kb b := by
  have h := eq_win heqs hp hu he 0 (by omega)
  simpa using h

/-! ## 4e. The base level: 4 x 4 schoolbook columns -/

section cols

variable (A B : Nat → Bool)

theorem col0 : (A 0 && B 0) = cl 4 A B 0 := by
  simp only [cl, bx]
  generalize A 0 = a0, A 1 = a1, A 2 = a2, A 3 = a3, B 0 = b0, B 1 = b1, B 2 = b2, B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

theorem col1 : ((A 0 && B 1) ^^ (A 1 && B 0)) = cl 4 A B 1 := by
  simp only [cl, bx]
  generalize A 0 = a0, A 1 = a1, A 2 = a2, A 3 = a3, B 0 = b0, B 1 = b1, B 2 = b2, B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

theorem col2 : (((A 0 && B 2) ^^ (A 1 && B 1)) ^^ (A 2 && B 0)) = cl 4 A B 2 := by
  simp only [cl, bx]
  generalize A 0 = a0, A 1 = a1, A 2 = a2, A 3 = a3, B 0 = b0, B 1 = b1, B 2 = b2, B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

theorem col3 : (((A 0 && B 3) ^^ (A 1 && B 2)) ^^ ((A 2 && B 1) ^^ (A 3 && B 0))) = cl 4 A B 3 := by
  simp only [cl, bx]
  generalize A 0 = a0, A 1 = a1, A 2 = a2, A 3 = a3, B 0 = b0, B 1 = b1, B 2 = b2, B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

theorem col4 : (((A 1 && B 3) ^^ (A 2 && B 2)) ^^ (A 3 && B 1)) = cl 4 A B 4 := by
  simp only [cl, bx]
  generalize A 0 = a0, A 1 = a1, A 2 = a2, A 3 = a3, B 0 = b0, B 1 = b1, B 2 = b2, B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

theorem col5 : ((A 2 && B 3) ^^ (A 3 && B 2)) = cl 4 A B 5 := by
  simp only [cl, bx]
  generalize A 0 = a0, A 1 = a1, A 2 = a2, A 3 = a3, B 0 = b0, B 1 = b1, B 2 = b2, B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

theorem col6 : (A 3 && B 3) = cl 4 A B 6 := by
  simp only [cl, bx]
  generalize A 0 = a0, A 1 = a1, A 2 = a2, A 3 = a3, B 0 = b0, B 1 = b1, B 2 = b2, B 3 = b3
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide

end cols

theorem KW_self (L : Nat) : KW L L = 4 := by simp [KW]

/-- **The base level**: product slot `t` of row `L` holds the carry-less product of the node's two 4-bit
operands. -/
theorem base_inv {N : Nat} (hN : 1 ≤ N) {st : SvState} (heqs : CombEqs (kM N) st) {uA uB uR : LVec}
    (hA : SvState.lookup st "av" = some uA) (hB : SvState.lookup st "bv" = some uB)
    (hR : SvState.lookup st "rv" = some uR) {fa fb : Nat → Bool}
    (hopA : ∀ t, t < 3 ^ KL N →
      KB uA (KL N * KR (KL N) + t * KW (KL N) (KL N)) (opd (KL N) fa (KL N) t) (KW (KL N) (KL N)))
    (hopB : ∀ t, t < 3 ^ KL N →
      KB uB (KL N * KR (KL N) + t * KW (KL N) (KL N)) (opd (KL N) fb (KL N) t) (KW (KL N) (KL N)))
    {t : Nat} (ht : t < 3 ^ KL N) :
    KB uR (KL N * KS (KL N) + t * 2 * KW (KL N) (KL N))
      (cl (KW (KL N) (KL N)) (opd (KL N) fa (KL N) t) (opd (KL N) fb (KL N) t)) (2 * KW (KL N) (KL N) - 1) := by
  have ka := hopA t ht
  have kb' := hopB t ht
  rw [KW_self] at ka kb' ⊢
  generalize opd (KL N) fa (KL N) t = A at ka ⊢
  generalize opd (KL N) fb (KL N) t = B at kb' ⊢
  have ra : ∀ i, i < 4 → evalPure2 st (aSl (KL N) t i) = .ok (kb (A i)) := fun i hi =>
    ev_bit hA (by have := ka i hi; rwa [show KL N * KR (KL N) + t * 4 + i = KL N * KR (KL N) + (4 * t + i) by
      omega] at this)
  have rb : ∀ i, i < 4 → evalPure2 st (bSl (KL N) t i) = .ok (kb (B i)) := fun i hi =>
    ev_bit hB (by have := kb' i hi; rwa [show KL N * KR (KL N) + t * 4 + i = KL N * KR (KL N) + (4 * t + i) by
      omega] at this)
  have pe : ∀ i j, i < 4 → j < 4 → evalPure2 st (ppP (KL N) t i j) = .ok (kb (A i && B j)) :=
    fun i j hi hj => ev_and2 (ra i hi) (rb j hj)
  have hb : ∀ q, q ∈ baseP (KL N) t → ∃ j, (kM N).processes[j]? = some q :=
    fun q h => kM_getElem?_of_mem hN (mem_base ht h)
  intro k hk
  rw [show KL N * KS (KL N) + t * 2 * 4 + k = KL N * KS (KL N) + (8 * t + k) by omega]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨j, hj⟩ := hb (bsP (KL N) t 0 (ppP (KL N) t 0 0)) (by simp [baseP])
    rw [eq_bit heqs hj hR (pe 0 0 (by omega) (by omega)), col0]
  · obtain ⟨j, hj⟩ := hb (bsP (KL N) t 1 (xorP (ppP (KL N) t 0 1) (ppP (KL N) t 1 0))) (by simp [baseP])
    rw [eq_bit heqs hj hR (ev_xor2 (pe 0 1 (by omega) (by omega)) (pe 1 0 (by omega) (by omega))), col1]
  · obtain ⟨j, hj⟩ := hb (bsP (KL N) t 2 (xorP (xorP (ppP (KL N) t 0 2) (ppP (KL N) t 1 1)) (ppP (KL N) t 2 0)))
      (by simp [baseP])
    rw [eq_bit heqs hj hR (ev_xor2 (ev_xor2 (pe 0 2 (by omega) (by omega)) (pe 1 1 (by omega) (by omega)))
      (pe 2 0 (by omega) (by omega))), col2]
  · obtain ⟨j, hj⟩ := hb (bsP (KL N) t 3 (xorP (xorP (ppP (KL N) t 0 3) (ppP (KL N) t 1 2))
      (xorP (ppP (KL N) t 2 1) (ppP (KL N) t 3 0)))) (by simp [baseP])
    rw [eq_bit heqs hj hR (ev_xor2 (ev_xor2 (pe 0 3 (by omega) (by omega)) (pe 1 2 (by omega) (by omega)))
      (ev_xor2 (pe 2 1 (by omega) (by omega)) (pe 3 0 (by omega) (by omega)))), col3]
  · obtain ⟨j, hj⟩ := hb (bsP (KL N) t 4 (xorP (xorP (ppP (KL N) t 1 3) (ppP (KL N) t 2 2)) (ppP (KL N) t 3 1)))
      (by simp [baseP])
    rw [eq_bit heqs hj hR (ev_xor2 (ev_xor2 (pe 1 3 (by omega) (by omega)) (pe 2 2 (by omega) (by omega)))
      (pe 3 1 (by omega) (by omega))), col4]
  · obtain ⟨j, hj⟩ := hb (bsP (KL N) t 5 (xorP (ppP (KL N) t 2 3) (ppP (KL N) t 3 2))) (by simp [baseP])
    rw [eq_bit heqs hj hR (ev_xor2 (pe 2 3 (by omega) (by omega)) (pe 3 2 (by omega) (by omega))), col5]
  · obtain ⟨j, hj⟩ := hb (bsP (KL N) t 6 (ppP (KL N) t 3 3)) (by simp [baseP])
    rw [eq_bit heqs hj hR (pe 3 3 (by omega) (by omega)), col6]

/-! ## 4f. One Karatsuba step: the parent's columns from its children's products -/

/-- The combination layer's column formulas (the design's XOR trees), as a function of the column. -/
def colF (H : Nat) (PL PH PM : Nat → Bool) (k : Nat) : Bool :=
  if k < H then PL k
  else if k < 2 * H - 1 then (PL (k - H) ^^ PL k) ^^ (PH (k - H) ^^ PM (k - H))
  else if k = 2 * H - 1 then (PL (H - 1) ^^ PH (H - 1)) ^^ PM (H - 1)
  else if k < 3 * H - 1 then (PL (k - H) ^^ PH (k - 2 * H)) ^^ (PH (k - H) ^^ PM (k - H))
  else PH (k - 2 * H)

/-- **The Karatsuba step**: with the children's products in place, the column formulas are the
parent's carry-less product (`comb_spec`, the identity of `karatsuba_full`). -/
theorem colF_spec {H : Nat} (hH : 1 ≤ H) {X Y : Nat → Bool} :
    ∀ k, k < 4 * H - 1 →
      colF H (cl H X Y) (cl H (fun i => X (H + i)) (fun j => Y (H + j)))
        (cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j))) k = cl (H + H) X Y k := by
  apply comb_spec hH (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · intro i hi
    simp only [colF, if_pos hi]
  · intro i hi
    simp only [colF]
    rw [if_neg (by omega), if_pos (by omega), show H + i - H = i by omega]
    generalize cl H X Y i = a
    generalize cl H X Y (H + i) = b
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) i = c
    generalize cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) i = d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl
  · simp only [colF, if_neg (show ¬ (2 * H - 1 < H) by omega),
      if_neg (show ¬ (2 * H - 1 < 2 * H - 1) by omega), ↓reduceIte]
    generalize cl H X Y (H - 1) = a
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (H - 1) = c
    generalize cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (H - 1) = d
    cases a <;> cases c <;> cases d <;> rfl
  · intro i hi
    simp only [colF]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show 2 * H + i - H = H + i by omega, show 2 * H + i - 2 * H = i by omega]
    generalize cl H X Y (H + i) = a
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) i = b
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (H + i) = c
    generalize cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (H + i) = d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl
  · intro i hi
    simp only [colF]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show 3 * H - 1 + i - 2 * H = H - 1 + i by omega]

/-! ## 4g. The products: what each level's product rows hold -/

/-- **The product invariant**, from the base level up: product slot `t` of row `l` holds the carry-less
product of node `(l, t)`'s operands (`2 W - 1` bits). -/
theorem prod_inv {N : Nat} (hN : 1 ≤ N) {st : SvState} (heqs : CombEqs (kM N) st) {uA uB uR : LVec}
    (hA : SvState.lookup st "av" = some uA) (hB : SvState.lookup st "bv" = some uB)
    (hR : SvState.lookup st "rv" = some uR) {fa fb : Nat → Bool}
    (hopA : ∀ l, l ≤ KL N → ∀ t, t < 3 ^ l →
      KB uA (l * KR (KL N) + t * KW (KL N) l) (opd (KL N) fa l t) (KW (KL N) l))
    (hopB : ∀ l, l ≤ KL N → ∀ t, t < 3 ^ l →
      KB uB (l * KR (KL N) + t * KW (KL N) l) (opd (KL N) fb l t) (KW (KL N) l)) :
    ∀ d l, l + d = KL N → ∀ t, t < 3 ^ l →
      KB uR (l * KS (KL N) + t * 2 * KW (KL N) l)
        (cl (KW (KL N) l) (opd (KL N) fa l t) (opd (KL N) fb l t)) (2 * KW (KL N) l - 1) := by
  intro d
  induction d with
  | zero =>
    intro l hl t ht
    obtain rfl : l = KL N := by omega
    exact base_inv hN heqs hA hB hR (fun t ht => hopA _ (Nat.le_refl _) t ht)
      (fun t ht => hopB _ (Nat.le_refl _) t ht) ht
  | succ d ih =>
    intro l hl t ht
    have hlL : l < KL N := by omega
    have hW := KW_succ hlL
    have hm := KW_pos (KL N) (l + 1)
    have hc : ∀ c, c ≤ 2 → KB uR ((l + 1) * KS (KL N) + (3 * t + c) * KW (KL N) l)
        (cl (KW (KL N) (l + 1)) (opd (KL N) fa (l + 1) (3 * t + c)) (opd (KL N) fb (l + 1) (3 * t + c)))
        (2 * KW (KL N) (l + 1) - 1) := by
      intro c hc
      exact (ih (l + 1) (by omega) (3 * t + c) (by rw [Nat.pow_succ]; omega)).addr
        (by rw [Nat.mul_assoc (3 * t + c) 2, ← hW])
    generalize hX : opd (KL N) fa l t = X
    generalize hY : opd (KL N) fb l t = Y
    generalize hmm : KW (KL N) (l + 1) = m at hm hW hc
    have hPL : KB uR ((l + 1) * KS (KL N) + (3 * t + 0) * KW (KL N) l) (cl m X Y) (2 * m - 1) :=
      (hc 0 (by omega)).congr fun k _ =>
        cl_congr (fun i _ => by rw [opd_c0, hX]) (fun j _ => by rw [opd_c0, hY]) k
    have hPH : KB uR ((l + 1) * KS (KL N) + (3 * t + 1) * KW (KL N) l)
        (cl m (fun i => X (m + i)) (fun j => Y (m + j))) (2 * m - 1) :=
      (hc 1 (by omega)).congr fun k _ =>
        cl_congr (fun i _ => by rw [opd_c1, hX, hmm, Nat.add_comm]) (fun j _ => by rw [opd_c1, hY, hmm, Nat.add_comm]) k
    have hPM : KB uR ((l + 1) * KS (KL N) + (3 * t + 2) * KW (KL N) l)
        (cl m (fun i => X i ^^ X (m + i)) (fun j => Y j ^^ Y (m + j))) (2 * m - 1) :=
      (hc 2 (by omega)).congr fun k _ =>
        cl_congr (fun i _ => by rw [opd_c2, hX, hmm, Nat.add_comm i]) (fun j _ => by rw [opd_c2, hY, hmm, Nat.add_comm j]) k
    have hspec := colF_spec (H := m) (by omega) (X := X) (Y := Y)
    generalize cl m X Y = PL at hPL hspec
    generalize cl m (fun i => X (m + i)) (fun j => Y (m + j)) = PH at hPH hspec
    generalize cl m (fun i => X i ^^ X (m + i)) (fun j => Y j ^^ Y (m + j)) = PM at hPM hspec
    generalize hWW : KW (KL N) l = W at hW hPL hPH hPM ⊢
    subst hW
    refine KB.congr (g := colF m PL PH PM) ?_ (fun k hk => by rw [hspec k (by omega), show m + m = 2 * m by omega])
    -- the five column ranges, from the five combination assigns
    have hcb : ∀ q, q ∈ combP (KL N) l t → ∃ j, (kM N).processes[j]? = some q :=
      fun q h => kM_getElem?_of_mem hN (mem_comb hlL ht h)
    simp only [combP, List.mem_cons, List.not_mem_nil, or_false, hWW, hmm] at hcb
    obtain ⟨j0, hj0⟩ := hcb _ (Or.inl rfl)
    obtain ⟨j1, hj1⟩ := hcb _ (Or.inr (Or.inl rfl))
    obtain ⟨j2, hj2⟩ := hcb _ (Or.inr (Or.inr (Or.inl rfl)))
    obtain ⟨j3, hj3⟩ := hcb _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    obtain ⟨j4, hj4⟩ := hcb _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    -- the reads
    have rL := ev_win hR (hPL.mono (w' := m) (by omega))
    have rL' := ev_win hR (hPL.mono (w' := m - 1) (by omega))
    have rLh := ev_win hR (KB.sub hPL m (m - 1) (by omega) ((l + 1) * KS (KL N) + ((3 * t + 0) * (2 * m) + m)) (by omega))
    have rH' := ev_win hR (hPH.mono (w' := m - 1) (by omega))
    have rHh := ev_win hR (KB.sub hPH m (m - 1) (by omega) ((l + 1) * KS (KL N) + ((3 * t + 1) * (2 * m) + m)) (by omega))
    have rHt := ev_win hR (KB.sub hPH (m - 1) m (by omega) ((l + 1) * KS (KL N) + ((3 * t + 1) * (2 * m) + m - 1)) (by omega))
    have rM' := ev_win hR (hPM.mono (w' := m - 1) (by omega))
    have rMh := ev_win hR (KB.sub hPM m (m - 1) (by omega) ((l + 1) * KS (KL N) + ((3 * t + 2) * (2 * m) + m)) (by omega))
    have bL := ev_bit hR (hPL (m - 1) (by omega))
    have bH := ev_bit hR (hPH (m - 1) (by omega))
    have bM := ev_bit hR (hPM (m - 1) (by omega))
    rw [show (l + 1) * KS (KL N) + (3 * t + 0) * (2 * m) + (m - 1) =
      (l + 1) * KS (KL N) + ((3 * t + 0) * (2 * m) + m - 1) by omega] at bL
    rw [show (l + 1) * KS (KL N) + (3 * t + 1) * (2 * m) + (m - 1) =
      (l + 1) * KS (KL N) + ((3 * t + 1) * (2 * m) + m - 1) by omega] at bH
    rw [show (l + 1) * KS (KL N) + (3 * t + 2) * (2 * m) + (m - 1) =
      (l + 1) * KS (KL N) + ((3 * t + 2) * (2 * m) + m - 1) by omega] at bM
    have w0 := eq_win heqs hj0 hR rL
    have w1 := eq_win heqs hj1 hR (evalPure2_xor_ofBitVec (evalPure2_xor_ofBitVec rL' rLh)
      (evalPure2_xor_ofBitVec rH' rM'))
    have w2 := eq_bit heqs hj2 hR (ev_xor2 (ev_xor2 bL bH) bM)
    have w3 := eq_win heqs hj3 hR (evalPure2_xor_ofBitVec (evalPure2_xor_ofBitVec rLh rH')
      (evalPure2_xor_ofBitVec rHh rMh))
    have w4 := eq_win heqs hj4 hR rHt
    intro k hk
    by_cases k0 : k < m
    · have := w0 k k0
      simp only [getLsbD_ofBits_lt k0] at this
      simp only [colF, if_pos k0]
      exact this
    by_cases k1 : k < 2 * m - 1
    · obtain ⟨i, rfl⟩ : ∃ i, k = m + i := ⟨k - m, by omega⟩
      have := w1 i (by omega)
      simp only [BitVec.getLsbD_xor, getLsbD_ofBits_lt (show i < m - 1 by omega)] at this
      rw [show l * KS (KL N) + t * 2 * (2 * m) + (m + i) = l * KS (KL N) + (t * 2 * (2 * m) + m) + i by omega,
        this]
      simp only [colF, if_neg k0, if_pos k1, show m + i - m = i by omega]
    by_cases k2 : k = 2 * m - 1
    · subst k2
      rw [show l * KS (KL N) + t * 2 * (2 * m) + (2 * m - 1) = l * KS (KL N) + (t * 2 * (2 * m) + 2 * m - 1) by omega,
        w2]
      simp only [colF, if_neg k0, if_neg k1, ↓reduceIte]
    by_cases k3 : k < 3 * m - 1
    · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * m + i := ⟨k - 2 * m, by omega⟩
      have := w3 i (by omega)
      simp only [BitVec.getLsbD_xor, getLsbD_ofBits_lt (show i < m - 1 by omega)] at this
      rw [show l * KS (KL N) + t * 2 * (2 * m) + (2 * m + i) = l * KS (KL N) + (t * 2 * (2 * m) + 2 * m) + i by omega,
        this]
      simp only [colF, if_neg k0, if_neg k1, if_neg k2, if_pos k3, show 2 * m + i - m = m + i by omega,
        show 2 * m + i - 2 * m = i by omega]
    · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * m - 1 + i := ⟨k - (3 * m - 1), by omega⟩
      have := w4 i (by omega)
      simp only [getLsbD_ofBits_lt (show i < m by omega)] at this
      rw [show l * KS (KL N) + t * 2 * (2 * m) + (3 * m - 1 + i) =
        l * KS (KL N) + (t * 2 * (2 * m) + 2 * m + m - 1) + i by omega, this]
      simp only [colF, if_neg k0, if_neg k1, if_neg k2, if_neg k3, show 3 * m - 1 + i - 2 * m = m - 1 + i by omega]

/-! ## 4h. The output, and the statement -/

/-- **The settled state**: in every solution of the design's equations with known inputs `x`, `y`, the
output `p` holds the carry-less product `a (x) b` on `2N - 1` bits. -/
theorem kara_settled {N : Nat} (hN : 1 ≤ N) {st : SvState} (heqs : CombEqs (kM N) st)
    (hs : StateShape (kM N) st) {x y : BitVec N} (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    SvState.lookup st "p" = some (LVec.ofBitVec (ofBits (2 * N - 1) (coeff N x y))) := by
  have hst : ∀ q, q ∈ kStatics N → ∃ j, (kM N).processes[j]? = some q :=
    fun q h => kM_getElem?_of_mem hN (mem_static h)
  simp only [kStatics, List.mem_cons, List.not_mem_nil, or_false] at hst
  obtain ⟨j0, hj0⟩ := hst _ (Or.inl rfl)
  obtain ⟨j1, hj1⟩ := hst _ (Or.inr (Or.inl rfl))
  obtain ⟨j2, hj2⟩ := hst _ (Or.inr (Or.inr rfl))
  obtain ⟨uA, hA, hA0⟩ := CombEqs.extract_slice heqs hj0
    (evalPure2_resize_ofBitVec (KR (KL N)) (evalPure2_ident_ofBitVec ha))
  obtain ⟨uB, hB, hB0⟩ := CombEqs.extract_slice heqs hj1
    (evalPure2_resize_ofBitVec (KR (KL N)) (evalPure2_ident_ofBitVec hb))
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq] at hA0 hB0
  have h0A : KB uA 0 x.getLsbD (KR (KL N)) :=
    (KB.of_win hA0).congr (fun k hk => by simp [hk])
  have h0B : KB uB 0 y.getLsbD (KR (KL N)) :=
    (KB.of_win hB0).congr (fun k hk => by simp [hk])
  have h3 : 0 < 3 ^ KL N := Nat.pos_of_ne_zero (by simp)
  obtain ⟨jb, hjb⟩ := kM_getElem?_of_mem hN
    (mem_base (N := N) h3 (show bsP (KL N) 0 0 (ppP (KL N) 0 0 0) ∈ baseP (KL N) 0 by simp [baseP]))
  obtain ⟨uR, hR, -⟩ := hs.driven "rv" ⟨jb, _, _, Design2.writes_of_window? hjb rfl⟩
  have hopA := opd_inv hN heqs (Or.inl rfl) hA h0A
  have hopB := opd_inv hN heqs (Or.inr rfl) hB h0B
  have hP := prod_inv hN heqs hA hB hR hopA hopB (KL N) 0 (by omega) 0 (by simp)
  have hNP := N_le_P N
  have hW0 : KW (KL N) 0 = 4 * 2 ^ KL N := by simp [KW]
  have hP' : KB uR 0 (cl (KW (KL N) 0) x.getLsbD y.getLsbD) (2 * N - 1) :=
    (hP.mono (by omega)).addr (by simp)
  have hp := CombEqs.lookup_ident (kM_comb hN) heqs hs hj2 (ev_win hR hP') (kM_declWidth_p N)
  rw [hp, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_ofBits_lt hk, getLsbD_ofBits_lt hk, coeff_eq]
  have hza : ∀ i, N ≤ i → x.getLsbD i = false := fun i hi => BitVec.getLsbD_of_ge x i hi
  have hzb : ∀ i, N ≤ i → y.getLsbD i = false := fun i hi => BitVec.getLsbD_of_ge y i hi
  rw [cl_trunc (by omega : N ≤ KW (KL N) 0) hza hzb k]
  rfl

/-- **The level-generate Karatsuba design**: the `clmul` statement, for every `N` in the task's range. -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  rw [kara_sem_eq hN']
  refine CombTask.satisfiedAt_of_comb ?_ (kM_comb hN') (kM_acyclic hN') ?_
  · simp [CombTask.Interface, inputPorts, outputPorts, kM_decls, kDecls, SvGolf.Tasks.Clmul.task]
  · intro st heqs hs v hv
    obtain ⟨x, y, ⟨⟩⟩ := v
    simp only [SvGolf.Tasks.Clmul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
    obtain ⟨ha, hb⟩ := hv
    exact kara_settled hN' heqs hs ha hb

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

/--
info: 'Submission.kara_structure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kara_structure

end Submission

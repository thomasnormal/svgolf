import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2
import LeanModels.Sv.Lib.Prefix
import LeanModels.Sv.CombView

/-!
# The Sklansky parallel-prefix adder of task `add` (`add_n_sklansky.sv`), proved by hand

This file proves `theorem Submission.solution : Submission.Goal` for the design as written: a Sklansky
parallel-prefix adder in generate loops, with the `int` localparam `L = $clog2(N + 1)`, a conditional generate
inside the level loop and the partner index `((i >> l) << l) - 1`. The `sv_comb` tactics refuse this source
(`sv_structure`: a conditional generate inside a generate loop is outside their fragment), so every step is done
by hand, on the route of `tasks/add/reference/add_n_byhand.lean` and `tasks/mul/reference/mul_n_byhand.lean`.
`N` stays a variable throughout; nothing is unrolled.

## Route

1. **The design at symbolic `N`** (sections 1-3): the envelope's items pinned by `rfl`; the parameter
   environment, in which `L` is `canonInt 32 true (clog2 (N + 1))`, which is `clog2 (N + 1)` below `2^31`
   (`lv_canon`); the declarations (`g`, `p` are `(L+1)(N+1)` bits, row-major `g[r][c]` at `r (N+1) + c`); every
   template at in-range genvars, the generate-if decided by `evalGenGuard` (bit `l` of `i`), the partner index
   evaluated to `i / 2^l * 2^l - 1`; the three generate blocks; `instantiate2` (`skl_instantiate2`).
2. **The comb profile** (`skl_comb`): every process an assign of a 1-bit window, in range, the windows pairwise
   disjoint (`pairwise_wins`), so `design.sem N` is the instantiated design (`skl_sem_eq`).
3. **Acyclicity** (`skl_acyclic`): a writer of `g` or `p` at offset `o` ranks `o + 1`, `x` ranks `0`, `s` and
   `cout` rank above every offset; row `l + 1` reads only row `l` below its own offsets.
4. **The settled state** (`skl_settled`): by induction on the level, position `i` of row `l` holds the
   recurrence `Core.sklRec` of the adder's positions, so row `L` holds the carries (`Core.skl_carry_clog2`, the
   block invariant, copied from `add_n_sklansky_core.lean` beside the design), and `s`, `cout` are the sum.
5. **The statement** (`solution`): `CombTask.satisfiedAt_of_comb`, as in `add_n_byhand.lean`.
-/

namespace Submission

open LeanModels.Sv SvGolf

local notation "gI" => PExpr.genvarRef "i"
local notation "gL" => PExpr.genvarRef "l"
local notation "nRef" => PExpr.paramRef "N" none
local notation "lRef" => PExpr.paramRef "L" none
local notation "iP1" => PExpr.binary (SymBinOp.m0 BinOp.add) (PExpr.genvarRef "i") (PExpr.int 1)
local notation "lP1" => PExpr.binary (SymBinOp.m0 BinOp.add) (PExpr.genvarRef "l") (PExpr.int 1)
def partE : PExpr := .binary (.m0 .sub) (.binary .shl (.binary .shr gI gL) gL) (.int 1)
def guardE : PExpr := .binary (.m0 .eq) (.binary (.m0 .and) (.binary .shr gI gL) (.int 1)) (.int 1)


/-! ## The prefix mathematics (section `SklCore` of `tests/add/baselines/add_n_sklansky_core.lean`, the part this
proof uses, copied verbatim into its own namespace) -/

namespace Core

open LeanModels.Sv.Lib

theorem shl_shr (l i : Nat) : (i >>> l) <<< l = i / 2 ^ l * 2 ^ l := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

theorem guard_iff_div (l i : Nat) : (i >>> l) % 2 = 1 ↔ i / 2 ^ l % 2 = 1 := by
  rw [Nat.shiftRight_eq_div_pow]

theorem aligned_odd {i P : Nat} (hP : 0 < P) (hq : i / P % 2 = 1) :
    i / (P * 2) * (P * 2) + P = i / P * P ∧ (i / P * P - 1) / P * P = i / (P * 2) * (P * 2) := by
  rw [← Nat.div_div_eq_div_mul]
  generalize i / P = q at *
  obtain ⟨Q, rfl⟩ : ∃ Q, q = 2 * Q + 1 := ⟨q / 2, by omega⟩
  have h2 : (2 * Q + 1) / 2 = Q := by omega
  have e1 : (2 * Q + 1) * P = 2 * (Q * P) + P := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e2 : Q * (P * 2) = 2 * (Q * P) := by rw [← Nat.mul_assoc, Nat.mul_comm (Q * P) 2]
  have e3 : (2 * (Q * P) + P - 1) / P = 2 * Q := by
    rw [show 2 * (Q * P) + P - 1 = (P - 1) + 2 * Q * P by rw [Nat.mul_assoc]; omega,
      Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [h2, e1, e2, e3]
  exact ⟨rfl, Nat.mul_assoc 2 Q P⟩

theorem aligned_even {i P : Nat} (hq : ¬ i / P % 2 = 1) : i / (P * 2) * (P * 2) = i / P * P := by
  rw [← Nat.div_div_eq_div_mul]
  generalize i / P = q at *
  obtain ⟨Q, rfl⟩ : ∃ Q, q = 2 * Q := ⟨q / 2, by omega⟩
  rw [show 2 * Q / 2 = Q by omega, Nat.mul_comm P 2, ← Nat.mul_assoc, Nat.mul_comm Q 2]

theorem shl_shr_le (l i : Nat) : (i >>> l) <<< l ≤ i := by
  rw [shl_shr]
  exact Nat.div_mul_le_self i (2 ^ l)

theorem shl_shr_pos {l i : Nat} (hg : (i >>> l) % 2 = 1) : 1 ≤ (i >>> l) <<< l := by
  rw [guard_iff_div] at hg
  obtain ⟨h1, -⟩ := aligned_odd (Nat.two_pow_pos l) hg
  rw [shl_shr, ← h1]
  have := Nat.two_pow_pos l
  omega

theorem partner_lt {l i : Nat} (hg : (i >>> l) % 2 = 1) : ((i >>> l) <<< l) - 1 < i := by
  have h1 := shl_shr_pos hg
  have h2 := shl_shr_le l i
  omega

theorem shl_shr_of_lt {l i : Nat} (hi : i < 2 ^ l) : (i >>> l) <<< l = 0 := by
  rw [shl_shr, Nat.div_eq_of_lt hi, Nat.zero_mul]

def sklRec (pos : Nat → Bool × Bool) : Nat → Nat → Bool × Bool
  | 0, i => pos i
  | l + 1, i =>
    if (i >>> l) % 2 = 1 then pgOp (sklRec pos l i) (sklRec pos l (((i >>> l) <<< l) - 1))
    else sklRec pos l i

theorem sklRec_zero (pos : Nat → Bool × Bool) (i : Nat) : sklRec pos 0 i = pos i := rfl

theorem sklRec_succ (pos : Nat → Bool × Bool) (l i : Nat) :
    sklRec pos (l + 1) i =
      if (i >>> l) % 2 = 1 then pgOp (sklRec pos l i) (sklRec pos l (((i >>> l) <<< l) - 1))
      else sklRec pos l i := rfl

theorem block_op (f : Nat → Bool × Bool) {l i : Nat} (hg : (i >>> l) % 2 = 1) :
    pgOp (pgBlock f ((i >>> l) <<< l) i)
        (pgBlock f (((((i >>> l) <<< l) - 1) >>> l) <<< l) (((i >>> l) <<< l) - 1)) =
      pgBlock f ((i >>> (l + 1)) <<< (l + 1)) i := by
  have hpos := shl_shr_pos hg
  have hle := shl_shr_le l i
  rw [guard_iff_div] at hg
  obtain ⟨h1, h2⟩ := aligned_odd (Nat.two_pow_pos l) hg
  rw [shl_shr l (((i >>> l) <<< l) - 1), shl_shr (l + 1), Nat.pow_succ]
  rw [shl_shr] at hpos hle ⊢
  rw [h2]
  have hP := Nat.two_pow_pos l
  generalize i / 2 ^ l * 2 ^ l = b at *
  generalize i / (2 ^ l * 2) * (2 ^ l * 2) = c at *
  have := pgBlock_combine f (j := c) (m := b - 1) (k := i) (by omega) (by omega)
  rw [show b - 1 + 1 = b by omega] at this
  exact this

theorem block_pass (f : Nat → Bool × Bool) {l i : Nat} (hg : ¬ (i >>> l) % 2 = 1) :
    pgBlock f ((i >>> l) <<< l) i = pgBlock f ((i >>> (l + 1)) <<< (l + 1)) i := by
  rw [guard_iff_div] at hg
  rw [shl_shr, shl_shr, Nat.pow_succ, aligned_even hg]

theorem sklRec_block (pos : Nat → Bool × Bool) :
    ∀ l i, sklRec pos l i = pgBlock pos ((i >>> l) <<< l) i
  | 0, i => by
    rw [sklRec_zero, Nat.shiftRight_zero, Nat.shiftLeft_zero, pgBlock_self]
  | l + 1, i => by
    rw [sklRec_succ]
    by_cases hg : (i >>> l) % 2 = 1
    · rw [if_pos hg, sklRec_block pos l i, sklRec_block pos l, block_op pos hg]
    · rw [if_neg hg, sklRec_block pos l i, block_pass pos hg]

theorem sklRec_top (pos : Nat → Bool × Bool) {l i : Nat} (hi : i < 2 ^ l) :
    sklRec pos l i = pgBlock pos 0 i := by
  rw [sklRec_block, shl_shr_of_lt hi]

theorem skl_carry (a b : Nat → Bool) (cin : Bool) {L i : Nat} (hi : i < 2 ^ L) :
    sklRec (addPos a b cin) L i = (rippleCarry a b cin i, false) := by
  rw [sklRec_top _ hi, pgBlock_addPos_zero]

theorem skl_carry_clog2 (a b : Nat → Bool) (cin : Bool) {N i : Nat} (hi : i ≤ N) :
    sklRec (addPos a b cin) (clog2 (N + 1)) i = (rippleCarry a b cin i, false) :=
  skl_carry a b cin (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hi) (CombView.le_two_pow_clog2 (N + 1)))

end Core

def g00T : PProcess := .assignL (.arrayElem "g" [.int 0, .int 0]) (.ident "cin")
def p00T : PProcess := .assignL (.arrayElem "p" [.int 0, .int 0]) (.lit { bits := #[Logic.l0] })
def coutT : PProcess := .assign "cout" (.arrayElem "g" [lRef, nRef])

def xT : PProcess :=
  .assignL (.bitSel "x" gI) (.binary (.m0 .xor) ((PExpr.ident "a").bitSel gI) ((PExpr.ident "b").bitSel gI))
def g0T : PProcess :=
  .assignL (.arrayElem "g" [.int 0, iP1]) (.binary (.m0 .and) ((PExpr.ident "a").bitSel gI) ((PExpr.ident "b").bitSel gI))
def p0T : PProcess :=
  .assignL (.arrayElem "p" [.int 0, iP1]) (.binary (.m0 .xor) ((PExpr.ident "a").bitSel gI) ((PExpr.ident "b").bitSel gI))
def gOpT : PProcess :=
  .assignL (.arrayElem "g" [lP1, gI])
    (.binary (.m0 .or) (.arrayElem "g" [gL, gI])
      (.binary (.m0 .and) (.arrayElem "p" [gL, gI]) (.arrayElem "g" [gL, partE])))
def pOpT : PProcess :=
  .assignL (.arrayElem "p" [lP1, gI]) (.binary (.m0 .and) (.arrayElem "p" [gL, gI]) (.arrayElem "p" [gL, partE]))
def gPassT : PProcess := .assignL (.arrayElem "g" [lP1, gI]) (.arrayElem "g" [gL, gI])
def pPassT : PProcess := .assignL (.arrayElem "p" [lP1, gI]) (.arrayElem "p" [gL, gI])
def sT : PProcess :=
  .assignL (.bitSel "s" gI) (.binary (.m0 .xor) ((PExpr.ident "x").bitSel gI) (.arrayElem "g" [lRef, gI]))

def inGen : GenItem :=
  .genFor (some "g_in") "i" (.int 0) (.binary .slt gI nRef) (.unary .inc gI) (some 16)
    ([xT, g0T, p0T].map GenItem.process)
def nodeGen : GenItem :=
  .genFor (some "g_node") "i" (.int 0) (.binary .slt gI (.binary (.m0 .add) nRef (.int 1)))
    (.unary .inc gI) (some 17)
    [.genIf guardE ([gOpT, pOpT].map GenItem.process) ([gPassT, pPassT].map GenItem.process)]
def lvlGen : GenItem :=
  .genFor (some "g_lvl") "l" (.int 0) (.binary .slt gL lRef) (.unary .inc gL) (some 5) [nodeGen]
def sumGen : GenItem :=
  .genFor (some "g_sum") "i" (.int 0) (.binary .slt gI nRef) (.unary .inc gI) (some 16)
    ([sT].map GenItem.process)

theorem skl_generates : design.pdesign.generates = [inGen, lvlGen, sumGen] := rfl
theorem skl_static_source : design.pdesign.processes = [g00T, p00T, coutT] := rfl
theorem skl_others : design.pdesign.others = [] := rfl

def sklScope (N L : Int) : IEnv := { vals := [("L", L), ("N", N)], pwidths := [("N", 32), ("L", 32)] }
def sklEnv (N L : Int) : IEnv := { sklScope N L with dims := dimTable (sklScope N L) design.pdesign.decls }

theorem canon_small {v : Nat} (h : v < 2 ^ 31) : canonInt 32 true (v : Int) = v := by
  unfold canonInt
  have h1 : (v : Int).emod ((2 : Int) ^ 32) = v := Int.emod_eq_of_lt (by omega) (by omega)
  have h3 : (2 : Int) ^ (32 - 1) = 2147483648 := by decide
  rw [h1, h3]
  have h2 : ¬ ((2147483648 : Int) ≤ (v : Int)) := by omega
  simp [h2]

theorem skl_paramEnv_raw (N : Nat) :
    design.pdesign.paramEnv2 [(N : Int)] = .ok (sklEnv N (canonInt 32 true (clog2 (N + 1)))) := by
  rfl


def sklDeclsRaw (wv wg : Nat) : List Decl :=
  [{ name := "a", width := wv, isInput := true },
   { name := "b", width := wv, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := wv, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "g", width := wg },
   { name := "p", width := wg },
   { name := "x", width := wv }]

theorem skl_decls (N L : Int) :
    buildDecls (sklEnv N L) design.pdesign.decls =
      .ok (sklDeclsRaw ((N - 1).natAbs + 1) ((L.natAbs + 1) * (N.natAbs + 1))) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    sklEnv, sklScope, List.lookup, sklDeclsRaw, Gen2.except_ok_bind]

def sklElems (N : Int) : List (String × Nat) :=
  [("a", 1), ("b", 1), ("cin", 1), ("s", 1), ("cout", 1), ("g", N.natAbs + 1), ("p", N.natAbs + 1),
   ("x", 1)]

private theorem except_pure' {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem skl_elems (N L : Int) :
    buildElems (sklEnv N L) design.pdesign.decls = .ok (sklElems N) := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PType.elemWidth, PDim.width,
    evalInt, sklEnv, sklScope, List.lookup, sklElems, Gen2.except_ok_bind, List.foldlM_cons,
    except_pure']

def gpDims : List PDim := [⟨lRef, .int 0⟩, ⟨nRef, .int 0⟩]
theorem skl_g_dims : design.pdesign.packedDims.lookup "g" = some gpDims := rfl
theorem skl_p_dims : design.pdesign.packedDims.lookup "p" = some gpDims := rfl

private theorem gp_eval (N L : Int) (ws : List (String × Nat)) :
    evalDims { sklScope N L with widths := ws } gpDims = .ok [(L, 0), (N, 0)] :=
  evalDims_cons_of (d := ⟨lRef, .int 0⟩) (evalInt_paramRef_of (by simp [sklScope]))
    (evalInt_int 0)
    (evalDims_cons_of (d := ⟨nRef, .int 0⟩) (evalInt_paramRef_of (by simp [sklScope, List.lookup]))
      (evalInt_int 0) evalDims_nil)

theorem sklEnv_g (N L : Int) : (sklEnv N L).dims.lookup "g" = some [(L, 0), (N, 0)] :=
  PDesign.dimTable_lookup_of skl_g_dims (gp_eval N L)
theorem sklEnv_p (N L : Int) : (sklEnv N L).dims.lookup "p" = some [(L, 0), (N, 0)] :=
  PDesign.dimTable_lookup_of skl_p_dims (gp_eval N L)

structure SklEnvOk (E : IEnv) (N L : Nat) : Prop where
  n : E.vals.lookup "N" = some (N : Int)
  l : E.vals.lookup "L" = some (L : Int)
  g : E.dims.lookup "g" = some [((L : Int), 0), ((N : Int), 0)]
  p : E.dims.lookup "p" = some [((L : Int), 0), ((N : Int), 0)]

theorem SklEnvOk.bind {E : IEnv} {N L : Nat} (h : SklEnvOk E N L) (g : String) (hgN : g ≠ "N")
    (hgL : g ≠ "L") (v : Int) : SklEnvOk (E.bindVal g v) N L :=
  ⟨by simp [IEnv.bindVal, List.lookup, h.n, beq_false_of_ne (Ne.symm hgN)],
   by simp [IEnv.bindVal, List.lookup, h.l, beq_false_of_ne (Ne.symm hgL)],
   by simpa [IEnv.bindVal] using h.g, by simpa [IEnv.bindVal] using h.p⟩

theorem sklEnvOk (N L : Nat) (decls : List Decl) :
    SklEnvOk ((sklEnv N L).withDecls decls) N L :=
  ⟨by simp [sklEnv, sklScope, List.lookup], by simp [sklEnv, sklScope], by simpa using sklEnv_g N L,
   by simpa using sklEnv_p N L⟩

/-- A path `g[r][c]` / `p[r][c]` over `[L:0][N:0]`. -/
theorem win_gp {E : IEnv} {N L : Nat} {n : String}
    (hd : E.dims.lookup n = some [((L : Int), 0), ((N : Int), 0)])
    {ie je : PExpr} {r c : Nat}
    (hi : evalInt E ie = .ok (r : Int)) (hj : evalInt E je = .ok (c : Int)) (hr : r ≤ L)
    (hc : c ≤ N) :
    arrayElemWindow E n [ie, je] = .ok (((r * (N + 1) + c : Nat) : Int), 1, true) := by
  rw [arrayElemWindow_desc0_2 hd
    (by omega) (by omega) hi (by omega) (by omega) hj (by omega) (by omega)]
  have : (r : Int) * ((N : Int) + 1) + (c : Int) = ((r * (N + 1) + c : Nat) : Int) := by simp
  rw [this]

theorem read1 {E : IEnv} {elems : List (String × Nat)} {n : String} {is : List PExpr} {k : Nat}
    (h : arrayElemWindow E n is = .ok ((k : Int), 1, true)) :
    fitExpr2 E elems (some 1) (.arrayElem n is) = .slice (.ident n) k 1 := by
  rw [fitExpr2_arrayElem_of h, arrayElemRead_of_inRange h, Int.toNat_natCast]

theorem target1 {E : IEnv} {elems : List (String × Nat)} {n : String} {is : List PExpr} {k : Nat}
    (h : arrayElemWindow E n is = .ok ((k : Int), 1, true)) :
    instLhs2 E elems (.arrayElem n is) = .ok (.slice n k 1, 1) := by
  rw [instLhs2_arrayElem, arrayElemTarget_of_inRange h, Int.toNat_natCast]

theorem partE_eval (E : IEnv) (l i : Nat) (hpos : 1 ≤ i / 2 ^ l * 2 ^ l) :
    evalInt ((E.bindVal "l" l).bindVal "i" i) partE = .ok (((i / 2 ^ l * 2 ^ l - 1 : Nat) : Int)) := by
  have h1 : ¬ ((i : Int) < 0) := by omega
  have h2 : ¬ ((l : Int) < 0) := by omega
  simp [partE, evalInt, IEnv.bindVal, List.lookup, Gen2.except_ok_bind, h1, h2]
  have h4 : ((i / 2 ^ l * 2 ^ l : Nat) : Int) = (i : Int) / 2 ^ l * 2 ^ l := by push_cast; rfl
  omega

theorem guard_eval (E : IEnv) (l i : Nat) :
    evalGenGuard ((E.bindVal "l" l).bindVal "i" i) guardE =
      .ok (if i / 2 ^ l % 2 = 1 then 1 else 0) := by
  have h2 : ¬ ((l : Int) < 0) := by omega
  have h3 : (0 : Int) ≤ (i : Int) / 2 ^ l := by
    have : (2 : Int) ^ l = ((2 ^ l : Nat) : Int) := by push_cast; rfl
    rw [this]; exact Int.ediv_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  simp [guardE, evalGenGuard, IEnv.bindVal, List.lookup, Gen2.except_ok_bind, h2]
  rw [Int.max_eq_left h3]
  have hcast : (i : Int) / 2 ^ l % 2 = ((i / 2 ^ l % 2 : Nat) : Int) := by push_cast; rfl
  rw [hcast]
  by_cases hc : i / 2 ^ l % 2 = 1
  · rw [if_pos hc, hc]; rfl
  · have h0 : i / 2 ^ l % 2 = 0 := by omega
    rw [if_neg hc, h0]; rfl

/-! ## The instantiated vocabulary -/

def rd (n : String) (k : Nat) : Expr2 := .slice (.ident n) k 1
def lit0 : LVec := { bits := #[Logic.l0] }

def g00P : Process2 := .assign (.slice "g" 0 1) (.ident "cin")
def p00P : Process2 := .assign (.slice "p" 0 1) (.lit lit0)
def coutP (N L : Nat) : Process2 := .assign (.ident "cout") (rd "g" (L * (N + 1) + N))
def xP (i : Nat) : Process2 := .assign (.slice "x" i 1) (.binary .xor (rd "a" i) (rd "b" i))
def g0P (i : Nat) : Process2 := .assign (.slice "g" (i + 1) 1) (.binary .and (rd "a" i) (rd "b" i))
def p0P (i : Nat) : Process2 := .assign (.slice "p" (i + 1) 1) (.binary .xor (rd "a" i) (rd "b" i))
/-- The partner of position `i` at level `l`: the top of the aligned block below `i`'s. -/
def part (l i : Nat) : Nat := i / 2 ^ l * 2 ^ l - 1
def gOpP (N l i : Nat) : Process2 :=
  .assign (.slice "g" ((l + 1) * (N + 1) + i) 1)
    (.binary .or (rd "g" (l * (N + 1) + i))
      (.binary .and (rd "p" (l * (N + 1) + i)) (rd "g" (l * (N + 1) + part l i))))
def pOpP (N l i : Nat) : Process2 :=
  .assign (.slice "p" ((l + 1) * (N + 1) + i) 1)
    (.binary .and (rd "p" (l * (N + 1) + i)) (rd "p" (l * (N + 1) + part l i)))
def gPassP (N l i : Nat) : Process2 :=
  .assign (.slice "g" ((l + 1) * (N + 1) + i) 1) (rd "g" (l * (N + 1) + i))
def pPassP (N l i : Nat) : Process2 :=
  .assign (.slice "p" ((l + 1) * (N + 1) + i) 1) (rd "p" (l * (N + 1) + i))
def sP (N L i : Nat) : Process2 :=
  .assign (.slice "s" i 1) (.binary .xor (rd "x" i) (rd "g" (L * (N + 1) + i)))
/-- Position `i` at level `l`: the combining cells when bit `l` of `i` is set, the passing cells otherwise. -/
def nodeP (N l i : Nat) : List Process2 :=
  if i / 2 ^ l % 2 = 1 then [gOpP N l i, pOpP N l i] else [gPassP N l i, pPassP N l i]

/-! ## The templates at in-range genvars -/

section cells

variable {E : IEnv} {elems : List (String × Nat)} {N L : Nat}

theorem gv1 (E : IEnv) (g : String) (v : Int) : evalInt (E.bindVal g v) (.genvarRef g) = .ok v :=
  evalInt_genvarRef_of (by simp [IEnv.bindVal])

theorem gvI2 (E : IEnv) (l i : Int) : evalInt ((E.bindVal "l" l).bindVal "i" i) gI = .ok i :=
  evalInt_genvarRef_of (by simp [IEnv.bindVal])
theorem gvL2 (E : IEnv) (l i : Int) : evalInt ((E.bindVal "l" l).bindVal "i" i) gL = .ok l :=
  evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])

theorem iP1_eval (E : IEnv) (i : Nat) :
    evalInt (E.bindVal "i" i) iP1 = .ok ((i + 1 : Nat) : Int) := by
  rw [evalInt_add_of rfl rfl (gv1 E "i" i) (evalInt_int 1)]
  simp

theorem lP1_eval (E : IEnv) (l i : Nat) :
    evalInt ((E.bindVal "l" l).bindVal "i" i) lP1 = .ok ((l + 1 : Nat) : Int) := by
  rw [evalInt_add_of rfl rfl (gvL2 E l i) (evalInt_int 1)]
  simp

theorem x_inst (ha : elems.lookup "a" = some 1) (hb : elems.lookup "b" = some 1)
    (hx : elems.lookup "x" = some 1) (i : Nat) :
    instProcess2 (E.bindVal "i" i) elems xT = xP i := by
  have hiv := gv1 E "i" i
  rw [xT, instProcess2_assignL _ (instLhs2_bitSel hx hiv (by omega)), fitExpr2_binary,
    instExpr2_xor, fitExpr2_bitSel_ident ha hiv (by omega), fitExpr2_bitSel_ident hb hiv (by omega)]
  simp [xP, rd]

theorem g0_inst (h : SklEnvOk E N L) (ha : elems.lookup "a" = some 1)
    (hb : elems.lookup "b" = some 1) (i : Nat) (hi : i < N) :
    instProcess2 (E.bindVal "i" i) elems g0T = g0P i := by
  have h' := h.bind "i" (by decide) (by decide) i
  have hiv := gv1 E "i" i
  have hw := win_gp (n := "g") h'.g (r := 0) (evalInt_int 0) (iP1_eval E i) (by omega) (by omega)
  rw [g0T, instProcess2_assignL _ (target1 hw), fitExpr2_binary,
    instExpr2_and, fitExpr2_bitSel_ident ha hiv (by omega), fitExpr2_bitSel_ident hb hiv (by omega)]
  simp [g0P, rd]

theorem p0_inst (h : SklEnvOk E N L) (ha : elems.lookup "a" = some 1)
    (hb : elems.lookup "b" = some 1) (i : Nat) (hi : i < N) :
    instProcess2 (E.bindVal "i" i) elems p0T = p0P i := by
  have h' := h.bind "i" (by decide) (by decide) i
  have hiv := gv1 E "i" i
  have hw := win_gp (n := "p") h'.p (r := 0) (evalInt_int 0) (iP1_eval E i) (by omega) (by omega)
  rw [p0T, instProcess2_assignL _ (target1 hw), fitExpr2_binary,
    instExpr2_xor, fitExpr2_bitSel_ident ha hiv (by omega), fitExpr2_bitSel_ident hb hiv (by omega)]
  simp [p0P, rd]

theorem part_lt {l i : Nat} (hg : i / 2 ^ l % 2 = 1) : 1 ≤ i / 2 ^ l * 2 ^ l ∧ part l i < i := by
  have hP := Nat.two_pow_pos l
  have h1 : 1 ≤ i / 2 ^ l := by
    generalize i / 2 ^ l = q at hg ⊢
    omega
  have h2 : 2 ^ l ≤ i / 2 ^ l * 2 ^ l := Nat.le_mul_of_pos_left _ h1
  have h3 : i / 2 ^ l * 2 ^ l ≤ i := Nat.div_mul_le_self i (2 ^ l)
  unfold part
  generalize i / 2 ^ l * 2 ^ l = m at h2 h3 ⊢
  generalize 2 ^ l = P at hP h2
  omega

theorem gOp_inst (h : SklEnvOk E N L) (l i : Nat) (hl : l < L) (hi : i ≤ N)
    (hg : i / 2 ^ l % 2 = 1) :
    instProcess2 ((E.bindVal "l" l).bindVal "i" i) elems gOpT = gOpP N l i := by
  have h' := (h.bind "l" (by decide) (by decide) l).bind "i" (by decide) (by decide) i
  obtain ⟨hpos, hpl⟩ := part_lt hg
  have hwT := win_gp (n := "g") h'.g (lP1_eval E l i) (gvI2 E l i) (by omega) hi
  have hwG := win_gp (n := "g") h'.g (gvL2 E l i) (gvI2 E l i) (by omega) hi
  have hwP := win_gp (n := "p") h'.p (gvL2 E l i) (gvI2 E l i) (by omega) hi
  have hwQ := win_gp (n := "g") h'.g (gvL2 E l i) (partE_eval E l i hpos) (by omega)
    (by unfold part at hpl; omega)
  rw [gOpT, instProcess2_assignL _ (target1 hwT), fitExpr2_binary, instExpr2_or, read1 hwG,
    fitExpr2_binary, instExpr2_and, read1 hwP, read1 hwQ]
  rfl

theorem pOp_inst (h : SklEnvOk E N L) (l i : Nat) (hl : l < L) (hi : i ≤ N)
    (hg : i / 2 ^ l % 2 = 1) :
    instProcess2 ((E.bindVal "l" l).bindVal "i" i) elems pOpT = pOpP N l i := by
  have h' := (h.bind "l" (by decide) (by decide) l).bind "i" (by decide) (by decide) i
  obtain ⟨hpos, hpl⟩ := part_lt hg
  have hwT := win_gp (n := "p") h'.p (lP1_eval E l i) (gvI2 E l i) (by omega) hi
  have hwP := win_gp (n := "p") h'.p (gvL2 E l i) (gvI2 E l i) (by omega) hi
  have hwQ := win_gp (n := "p") h'.p (gvL2 E l i) (partE_eval E l i hpos) (by omega)
    (by unfold part at hpl; omega)
  rw [pOpT, instProcess2_assignL _ (target1 hwT), fitExpr2_binary, instExpr2_and, read1 hwP,
    read1 hwQ]
  rfl

theorem gPass_inst (h : SklEnvOk E N L) (l i : Nat) (hl : l < L) (hi : i ≤ N) :
    instProcess2 ((E.bindVal "l" l).bindVal "i" i) elems gPassT = gPassP N l i := by
  have h' := (h.bind "l" (by decide) (by decide) l).bind "i" (by decide) (by decide) i
  have hwT := win_gp (n := "g") h'.g (lP1_eval E l i) (gvI2 E l i) (by omega) hi
  have hwG := win_gp (n := "g") h'.g (gvL2 E l i) (gvI2 E l i) (by omega) hi
  rw [gPassT, instProcess2_assignL _ (target1 hwT), read1 hwG]
  rfl

theorem pPass_inst (h : SklEnvOk E N L) (l i : Nat) (hl : l < L) (hi : i ≤ N) :
    instProcess2 ((E.bindVal "l" l).bindVal "i" i) elems pPassT = pPassP N l i := by
  have h' := (h.bind "l" (by decide) (by decide) l).bind "i" (by decide) (by decide) i
  have hwT := win_gp (n := "p") h'.p (lP1_eval E l i) (gvI2 E l i) (by omega) hi
  have hwG := win_gp (n := "p") h'.p (gvL2 E l i) (gvI2 E l i) (by omega) hi
  rw [pPassT, instProcess2_assignL _ (target1 hwT), read1 hwG]
  rfl

theorem s_inst (h : SklEnvOk E N L) (hs : elems.lookup "s" = some 1)
    (hx : elems.lookup "x" = some 1) (i : Nat) (hi : i < N) :
    instProcess2 (E.bindVal "i" i) elems sT = sP N L i := by
  have h' := h.bind "i" (by decide) (by decide) i
  have hiv := gv1 E "i" i
  have hw := win_gp (n := "g") h'.g (evalInt_paramRef_of h'.l) hiv (Nat.le_refl L) (by omega)
  rw [sT, instProcess2_assignL _ (instLhs2_bitSel hs hiv (by omega)), fitExpr2_binary,
    instExpr2_xor, fitExpr2_bitSel_ident hx hiv (by omega), read1 hw]
  simp [sP, rd]

end cells


/-! ## The generate blocks -/

theorem n_bound {E : IEnv} {N : Nat} (h : E.vals.lookup "N" = some (N : Int))
    (g : String) (hg : g ≠ "N") (v : Int) :
    evalInt (E.bindVal g v) nRef = .ok (N : Int) := by
  apply evalInt_paramRef_of
  simp [IEnv.bindVal, List.lookup, h, beq_false_of_ne (Ne.symm hg)]

theorem n_bound_int {E : IEnv} {N : Nat} (h : E.vals.lookup "N" = some (N : Int))
    (g : String) (hg : g ≠ "N") (v : Int) :
    PExpr.isInt (E.bindVal g v) nRef = true :=
  isInt_paramRef_of (v := (N : Int)) (by simp [IEnv.bindVal, List.lookup, h, beq_false_of_ne (Ne.symm hg)])

theorem in_expand (E : IEnv) (elems : List (String × Nat)) (N L F : Nat) (hF : N < F)
    (h : SklEnvOk E N L) (ha : elems.lookup "a" = some 1) (hb : elems.lookup "b" = some 1)
    (hx : elems.lookup "x" = some 1) :
    inGen.expand2 E elems F = .ok ((List.range N).flatMap fun i => [xP i, g0P i, p0P i]) := by
  rw [inGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => [xP v.toNat, g0P v.toNat, p0P v.toNat])
      (evalInt_int 0) (n_bound_int h.n "i" (by decide)) (n_bound h.n "i" (by decide))
      (by simpa using hF)]
  · congr 1
    rw [intRange_zero, List.flatMap_map]
    simp
  · intro v hv0 hvN
    obtain ⟨i, rfl⟩ : ∃ i : Nat, v = (i : Int) := ⟨v.toNat, by omega⟩
    have hiN : i < N := by omega
    rw [expandList2_processes]
    simp only [List.map_cons, List.map_nil, Int.toNat_natCast]
    rw [x_inst ha hb hx i, g0_inst h ha hb i hiN, p0_inst h ha hb i hiN]

theorem node_expand (E : IEnv) (elems : List (String × Nat)) (N L F l : Nat) (hl : l < L)
    (hF : N + 1 < F) (h : SklEnvOk E N L) :
    nodeGen.expand2 (E.bindVal "l" l) elems F = .ok ((List.range (N + 1)).flatMap (nodeP N l)) := by
  have hb := h.bind "l" (by decide) (by decide) l
  rw [nodeGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int) + 1)
      (f := fun v => nodeP N l v.toNat)
      (evalInt_int 0)
      (fun v => isInt_binary_of rfl (n_bound_int hb.n "i" (by decide) v) rfl)
      (fun v => evalInt_add_of (n_bound_int hb.n "i" (by decide) v) rfl
        (n_bound hb.n "i" (by decide) v) (evalInt_int 1))
      (by omega)]
  · congr 1
    have hc : ((N : Int) + 1 - 0).toNat = N + 1 := by omega
    rw [hc, intRange_zero, List.flatMap_map]
    simp
  · intro v hv0 hvN
    obtain ⟨i, rfl⟩ : ∃ i : Nat, v = (i : Int) := ⟨v.toNat, by omega⟩
    have hiN : i ≤ N := by omega
    apply expandList2_singleton_ok
    simp only [Int.toNat_natCast, nodeP]
    by_cases hg : i / 2 ^ l % 2 = 1
    · rw [if_pos hg, GenItem.expand2_genIf_of_ne (v := 1) (by rw [guard_eval, if_pos hg]) (by decide),
        expandList2_processes]
      simp only [List.map_cons, List.map_nil]
      rw [gOp_inst h l i hl hiN hg, pOp_inst h l i hl hiN hg]
    · rw [if_neg hg, GenItem.expand2_genIf_of_eq (by rw [guard_eval, if_neg hg]),
        expandList2_processes]
      simp only [List.map_cons, List.map_nil]
      rw [gPass_inst h l i hl hiN, pPass_inst h l i hl hiN]

theorem lvl_expand (E : IEnv) (elems : List (String × Nat)) (N L F : Nat)
    (hFL : L < F) (hF : N + 1 < F) (h : SklEnvOk E N L) :
    lvlGen.expand2 E elems F =
      .ok ((List.range L).flatMap fun l => (List.range (N + 1)).flatMap (nodeP N l)) := by
  rw [lvlGen, GenItem.expand2_genFor_ascending_flatMap (N := (L : Int))
      (f := fun v => (List.range (N + 1)).flatMap (nodeP N v.toNat))
      (evalInt_int 0)
      (fun v => isInt_paramRef_of (v := (L : Int))
        (by simp [IEnv.bindVal, List.lookup, h.l]))
      (fun v => evalInt_paramRef_of (by simp [IEnv.bindVal, List.lookup, h.l]))
      (by omega)]
  · congr 1
    rw [intRange_zero, List.flatMap_map]
    simp
  · intro v hv0 hvL
    obtain ⟨l, rfl⟩ : ∃ l : Nat, v = (l : Int) := ⟨v.toNat, by omega⟩
    apply expandList2_singleton_ok
    rw [Int.toNat_natCast]
    exact node_expand E elems N L F l (by omega) hF h

theorem sum_expand (E : IEnv) (elems : List (String × Nat)) (N L F : Nat) (hF : N < F)
    (h : SklEnvOk E N L) (hs : elems.lookup "s" = some 1) (hx : elems.lookup "x" = some 1) :
    sumGen.expand2 E elems F = .ok ((List.range N).map (sP N L)) := by
  rw [sumGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => [sP N L v.toNat])
      (evalInt_int 0) (n_bound_int h.n "i" (by decide)) (n_bound h.n "i" (by decide))
      (by simpa using hF)]
  · congr 1
    rw [intRange_zero, List.flatMap_map]
    simp only [Int.sub_zero, Int.toNat_natCast]
    exact Gen2.flatMap_singleton_map (sP N L) (List.range N)
  · intro v hv0 hvN
    obtain ⟨i, rfl⟩ : ∃ i : Nat, v = (i : Int) := ⟨v.toNat, by omega⟩
    rw [expandList2_processes]
    simp only [List.map_cons, List.map_nil, Int.toNat_natCast]
    rw [s_inst h hs hx i (by omega)]


/-! ## Assembling `instantiate2` -/

theorem skl_static (N L wv wg : Nat) :
    design.pdesign.processes.map
        (instProcess2 ((sklEnv N L).withDecls (sklDeclsRaw wv wg)) (sklElems N)) =
      [g00P, p00P, coutP N L] := by
  have E := sklEnvOk N L (sklDeclsRaw wv wg)
  rw [skl_static_source]
  simp only [List.map_cons, List.map_nil]
  have hw00 := win_gp (n := "g") E.g (r := 0) (c := 0) (evalInt_int 0) (evalInt_int 0)
    (by omega) (by omega)
  have hp00 := win_gp (n := "p") E.p (r := 0) (c := 0) (evalInt_int 0) (evalInt_int 0)
    (by omega) (by omega)
  have hco := win_gp (n := "g") E.g (evalInt_paramRef_of E.l) (evalInt_paramRef_of E.n)
    (Nat.le_refl L) (Nat.le_refl N)
  have hcin : ((sklEnv N L).withDecls (sklDeclsRaw wv wg)).widths.lookup "cin" = some 1 := by
    simp [sklDeclsRaw, List.lookup]
  have hcout : ((sklEnv N L).withDecls (sklDeclsRaw wv wg)).widths.lookup "cout" = some 1 := by
    simp [sklDeclsRaw, List.lookup]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  · rw [g00T, instProcess2_assignL _ (target1 hw00), fitExpr2_ident hcin]
    simp [g00P]
  · have hz : ({ bits := #[Logic.l0] } : LVec).width = 1 := rfl
    rw [p00T, instProcess2_assignL _ (target1 hp00), fitExpr2_lit, if_pos hz]
    simp [p00P, lit0]
  · rw [coutT, instProcess2_assign _ hcout, read1 hco]
    rfl

theorem fuel_big (N : Nat) : N + 1 < PDesign.surfaceFuel [(N : Int)] := by
  have := Nat.le_mul_self (N + 2)
  simp [PDesign.surfaceFuel]
  omega

theorem skl_gens (N L : Nat) (hL : L ≤ N + 1) (decls : List Decl) :
    expandList2 ((sklEnv N L).withDecls decls) (sklElems N) (PDesign.surfaceFuel [(N : Int)])
      design.pdesign.generates =
      .ok (((List.range N).flatMap fun i => [xP i, g0P i, p0P i])
        ++ (((List.range L).flatMap fun l => (List.range (N + 1)).flatMap (nodeP N l))
        ++ (List.range N).map (sP N L))) := by
  have hF := fuel_big N
  have E := sklEnvOk N L decls
  rw [skl_generates]
  exact expandList2_cons_ok
    (in_expand _ _ N L _ (by omega) E (by simp [sklElems])
      (by simp [sklElems, List.lookup]) (by simp [sklElems, List.lookup]))
    (expandList2_cons_ok (lvl_expand _ _ N L _ (by omega) hF E)
      (expandList2_singleton_ok
        (sum_expand _ _ N L _ (by omega) E (by simp [sklElems, List.lookup])
          (by simp [sklElems, List.lookup]))))

/-- The ceiling logarithm `L = clog2 (N + 1)`. -/
abbrev lv (N : Nat) : Nat := clog2 (N + 1)

theorem lv_le (N : Nat) : lv N ≤ N + 1 := CombView.clog2_le (N + 1)

theorem lv_small (N : Nat) (hN : N < 2 ^ 31) : lv N < 2 ^ 31 := by
  have h31 : (2 : Nat) ^ 31 = 2147483648 := rfl
  rw [h31] at hN ⊢
  unfold lv clog2
  split
  · omega
  · have := (Nat.log2_lt (n := N + 1 - 1) (k := 31) (by omega)).mpr (by rw [h31]; omega)
    omega

theorem lv_canon (N : Nat) (hN : N < 2 ^ 31) : canonInt 32 true (lv N : Int) = (lv N : Int) :=
  canon_small (lv_small N hN)

theorem skl_paramEnv (N : Nat) (hN : N < 2 ^ 31) :
    design.pdesign.paramEnv2 [(N : Int)] = .ok (sklEnv N (lv N)) := by
  rw [skl_paramEnv_raw, lv_canon N hN]

def sklDesign (N : Nat) : Design2 :=
  design.pdesign.assemble2 (sklEnv N (lv N))
    (sklDeclsRaw (((N : Int) - 1).natAbs + 1) ((((lv N : Int)).natAbs + 1) * ((N : Int).natAbs + 1)))
    (sklElems N)
    (((List.range N).flatMap fun i => [xP i, g0P i, p0P i])
        ++ (((List.range (lv N)).flatMap fun l => (List.range (N + 1)).flatMap (nodeP N l))
        ++ (List.range N).map (sP N (lv N))))

theorem skl_instantiate2 (N : Nat) (hN : N < 2 ^ 31) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) = .ok (sklDesign N) := by
  have hd := skl_decls (N : Int) (lv N : Int)
  exact PDesign.instantiate2_of_ok rfl (skl_paramEnv N hN) hd (skl_elems _ _)
    (skl_gens N (lv N) (lv_le N) _)

/-- The whole instantiated process list. -/
def sklProcs (N : Nat) : List Process2 :=
  [g00P, p00P, coutP N (lv N)]
    ++ (((List.range N).flatMap fun i => [xP i, g0P i, p0P i])
    ++ (((List.range (lv N)).flatMap fun l => (List.range (N + 1)).flatMap (nodeP N l))
    ++ (List.range N).map (sP N (lv N))))

/-- The declarations for `N ≥ 1`: `a b s x` of `N` bits, `cin cout` of 1 bit, `g p` of `(L+1)(N+1)` bits. -/
def sklDecls (N : Nat) : List Decl := sklDeclsRaw N ((lv N + 1) * (N + 1))

theorem sklDesign_processes (N : Nat) : (sklDesign N).processes.toList = sklProcs N := by
  simp only [sklDesign, PDesign.assemble2_processes, skl_static, skl_others, List.map_nil,
    List.append_nil, sklProcs]

theorem sklDesign_decls (N : Nat) (hN : 1 ≤ N) : (sklDesign N).decls.toList = sklDecls N := by
  rw [sklDesign, PDesign.assemble2_decls, sklDecls]
  have hv : ((N : Int) - 1).natAbs + 1 = N := by omega
  have hl : ((lv N : Int)).natAbs = lv N := Int.natAbs_natCast _
  have hn : ((N : Int)).natAbs = N := Int.natAbs_natCast _
  rw [hv, hl, hn]


/-! ## The process table and the declarations, for any design that has them -/

theorem procs_cases {N : Nat} {p : Process2} (h : p ∈ sklProcs N) :
    p = g00P ∨ p = p00P ∨ p = coutP N (lv N) ∨
    (∃ i, i < N ∧ (p = xP i ∨ p = g0P i ∨ p = p0P i)) ∨
    (∃ l, l < lv N ∧ ∃ i, i ≤ N ∧
      ((i / 2 ^ l % 2 = 1 ∧ (p = gOpP N l i ∨ p = pOpP N l i)) ∨
       (¬ i / 2 ^ l % 2 = 1 ∧ (p = gPassP N l i ∨ p = pPassP N l i)))) ∨
    (∃ i, i < N ∧ p = sP N (lv N) i) := by
  simp only [sklProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range, List.mem_map] at h
  rcases h with (h | h | h) | ⟨i, hi, h⟩ | ⟨l, hl, i, hi, h⟩ | ⟨i, hi, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, by simpa using h⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, hl, i, by omega, ?_⟩))))
    unfold nodeP at h
    by_cases hg : i / 2 ^ l % 2 = 1
    · rw [if_pos hg] at h
      exact Or.inl ⟨hg, by simpa using h⟩
    · rw [if_neg hg] at h
      exact Or.inr ⟨hg, by simpa using h⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, h.symm⟩))))

section Profile

variable {N : Nat} {d : Design2} (hN : 1 ≤ N) (hp : d.processes.toList = sklProcs N)
  (hd : d.decls.toList = sklDecls N)

include hp in
theorem mem_of_get {j : Nat} {p : Process2} (h : d.processes[j]? = some p) : p ∈ sklProcs N := by
  rw [← hp]
  exact List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact h)

include hp in
theorem get_of_mem {p : Process2} (h : p ∈ sklProcs N) : ∃ j : Nat, d.processes[j]? = some p := by
  rw [← hp] at h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
  exact ⟨j, by rw [← Array.getElem?_toList]; exact hj⟩

include hd in
theorem skl_declWidth (n : String) :
    d.declWidth n = ((sklDecls N).find? fun dc => dc.name == n).map Decl.width := by
  simp only [Design2.declWidth, hd]

include hd in
theorem dw_g : d.declWidth "g" = some ((lv N + 1) * (N + 1)) := by
  simp [skl_declWidth hd, sklDecls, sklDeclsRaw]
include hd in
theorem dw_p : d.declWidth "p" = some ((lv N + 1) * (N + 1)) := by
  simp [skl_declWidth hd, sklDecls, sklDeclsRaw]
include hd in
theorem dw_x : d.declWidth "x" = some N := by simp [skl_declWidth hd, sklDecls, sklDeclsRaw]
include hd in
theorem dw_s : d.declWidth "s" = some N := by simp [skl_declWidth hd, sklDecls, sklDeclsRaw]
include hd in
theorem dw_cout : d.declWidth "cout" = some 1 := by simp [skl_declWidth hd, sklDecls, sklDeclsRaw]

include hd in
theorem skl_inputNames : d.inputNames.toList = ["a", "b", "cin"] := by
  simp [Design2.inputNames, hd, sklDecls, sklDeclsRaw]

/-- The one write window of each process. -/
def winOf : Process2 → Win
  | .assign (.slice n lo w) _ => (n, lo, w)
  | _ => ("cout", 0, 1)

include hd in
theorem wins_eq {p : Process2} (hm : p ∈ sklProcs N) {t : Lhs2} {e : Expr2} (he : p = .assign t e) :
    t.wins d = [winOf p] := by
  rcases procs_cases hm with rfl | rfl | rfl | ⟨i, -, rfl | rfl | rfl⟩ |
      ⟨l, -, i, -, ⟨-, rfl | rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨i, -, rfl⟩ <;>
    simp only [g00P, p00P, coutP, xP, g0P, p0P, gOpP, pOpP, gPassP, pPassP, sP,
      Process2.assign.injEq] at he <;>
    obtain ⟨rfl, rfl⟩ := he <;>
    simp [winOf, dw_cout hd, g00P, p00P, coutP, xP, g0P, p0P, gOpP, pOpP, gPassP, pPassP, sP]

include hp hd in
theorem writes_win {j : Nat} {wn : Win} (h : d.Writes j wn) :
    ∃ p, d.processes[j]? = some p ∧ p ∈ sklProcs N ∧ wn = winOf p := by
  obtain ⟨t, e, hj, hw⟩ := h
  have hm := mem_of_get hp hj
  rw [wins_eq hd hm rfl, List.mem_singleton] at hw
  exact ⟨_, hj, hm, hw⟩


end Profile

/-! ## One driver per bit: the windows are pairwise disjoint -/

theorem winOf_node (N l i : Nat) :
    (nodeP N l i).map winOf = [("g", (l + 1) * (N + 1) + i, 1), ("p", (l + 1) * (N + 1) + i, 1)] := by
  unfold nodeP
  split <;> rfl

def winsA (N : Nat) : List Win :=
  (List.range N).flatMap fun i => [("x", i, 1), ("g", i + 1, 1), ("p", i + 1, 1)]
def winsB (N L : Nat) : List Win :=
  (List.range L).flatMap fun l => (List.range (N + 1)).flatMap fun i =>
    [("g", (l + 1) * (N + 1) + i, 1), ("p", (l + 1) * (N + 1) + i, 1)]
def winsC (N : Nat) : List Win := (List.range N).map fun i => ("s", i, 1)

theorem procs_wins (N : Nat) :
    (sklProcs N).map winOf =
      [("g", 0, 1), ("p", 0, 1), ("cout", 0, 1)] ++ (winsA N ++ (winsB N (lv N) ++ winsC N)) := by
  simp only [sklProcs, List.map_append, List.map_cons, List.map_nil, List.map_flatMap, winOf_node,
    winsA, winsB, winsC, List.map_map]
  rfl

theorem mem_winsA {N : Nat} {a : Win} :
    a ∈ winsA N ↔ ∃ i, i < N ∧ (a = ("x", i, 1) ∨ a = ("g", i + 1, 1) ∨ a = ("p", i + 1, 1)) := by
  simp [winsA]

theorem mem_winsB {N L : Nat} {a : Win} :
    a ∈ winsB N L ↔ ∃ l, l < L ∧ ∃ i, i < N + 1 ∧
      (a = ("g", (l + 1) * (N + 1) + i, 1) ∨ a = ("p", (l + 1) * (N + 1) + i, 1)) := by
  simp [winsB]

theorem mem_winsC {N : Nat} {a : Win} : a ∈ winsC N ↔ ∃ i, i < N ∧ a = ("s", i, 1) := by
  simp [winsC, eq_comm]

/-- `Win.overlaps … = false`, the closer: other signals, or disjoint ranges. -/
macro "ovf" : tactic =>
  `(tactic| (rw [Win.overlaps_eq_false]; first | (left; decide) | (right; left; omega) | (right; right; omega)))

theorem row_ge (N l : Nat) : N + 1 ≤ (l + 1) * (N + 1) := Nat.le_mul_of_pos_left (N + 1) (by omega)

theorem row_lt {N l l' : Nat} (h : l < l') : (l + 1) * (N + 1) + (N + 1) ≤ (l' + 1) * (N + 1) :=
  rowMajor_le (by omega)

theorem pairwise_wins (N L : Nat) :
    ([("g", 0, 1), ("p", 0, 1), ("cout", 0, 1)] ++ (winsA N ++ (winsB N L ++ winsC N))).Pairwise
      fun a b : Win => Win.overlaps a b = false := by
  have hA : (winsA N).Pairwise fun a b : Win => Win.overlaps a b = false := by
    apply pairwise_flatMap_range
    · intro k _
      simp [Win.overlaps_eq_false]
    · intro j k hjk _ a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> ovf
  have hB : (winsB N L).Pairwise fun a b : Win => Win.overlaps a b = false := by
    apply pairwise_flatMap_range
    · intro l _
      apply pairwise_flatMap_range
      · intro k _
        simp [Win.overlaps_eq_false]
      · intro j k hjk _ a ha b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> ovf
    · intro l l' hll _ a ha b hb
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      obtain ⟨i, hi, ha⟩ := ha
      obtain ⟨i', hi', hb⟩ := hb
      have := row_lt (N := N) hll
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> ovf
  have hC : (winsC N).Pairwise fun a b : Win => Win.overlaps a b = false := by
    rw [winsC, List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun {a b} _ _ hab => by ovf) List.pairwise_lt_range
  have hAB : ∀ a ∈ winsA N, ∀ b ∈ winsB N L, Win.overlaps a b = false := by
    intro a ha b hb
    obtain ⟨i, hi, ha⟩ := mem_winsA.mp ha
    obtain ⟨l, hl, i', hi', hb⟩ := mem_winsB.mp hb
    have := row_ge N l
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> ovf
  have hAC : ∀ a ∈ winsA N, ∀ b ∈ winsC N, Win.overlaps a b = false := by
    intro a ha b hb
    obtain ⟨i, hi, ha⟩ := mem_winsA.mp ha
    obtain ⟨i', hi', rfl⟩ := mem_winsC.mp hb
    rcases ha with rfl | rfl | rfl <;> ovf
  have hBC : ∀ a ∈ winsB N L, ∀ b ∈ winsC N, Win.overlaps a b = false := by
    intro a ha b hb
    obtain ⟨l, hl, i, hi, ha⟩ := mem_winsB.mp ha
    obtain ⟨i', hi', rfl⟩ := mem_winsC.mp hb
    rcases ha with rfl | rfl <;> ovf
  have hS : ∀ a ∈ [("g", 0, 1), ("p", 0, 1), ("cout", 0, 1)],
      ∀ b ∈ winsA N ++ (winsB N L ++ winsC N), Win.overlaps a b = false := by
    intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb
    · obtain ⟨i, hi, hb⟩ := mem_winsA.mp hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> ovf
    · obtain ⟨l, hl, i, hi, hb⟩ := mem_winsB.mp hb
      have := row_ge N l
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> ovf
    · obtain ⟨i, hi, rfl⟩ := mem_winsC.mp hb
      rcases ha with rfl | rfl | rfl <;> ovf
  refine List.pairwise_append.mpr ⟨by decide, List.pairwise_append.mpr ⟨hA,
    List.pairwise_append.mpr ⟨hB, hC, hBC⟩, ?_⟩, hS⟩
  intro a ha b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hAB a ha b hb
  · exact hAC a ha b hb




/-! ## The comb profile -/

section Comb

variable {N : Nat} {d : Design2} (hN : 1 ≤ N) (hp : d.processes.toList = sklProcs N)
  (hd : d.decls.toList = sklDecls N)

include hp hd in
theorem skl_disjoint :
    ∀ i j wi wj, i ≠ j → d.Writes i wi → d.Writes j wj → Win.overlaps wi wj = false := by
  intro i j wi wj hij hi hj
  obtain ⟨p, hpi, -, rfl⟩ := writes_win hp hd hi
  obtain ⟨q, hqj, -, rfl⟩ := writes_win hp hd hj
  have hpw := pairwise_wins N (lv N)
  rw [← procs_wins, ← hp, List.pairwise_iff_getElem] at hpw
  rw [← Array.getElem?_toList] at hpi hqj
  obtain ⟨hi', hgi⟩ := List.getElem?_eq_some_iff.mp hpi
  obtain ⟨hj', hgj⟩ := List.getElem?_eq_some_iff.mp hqj
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have := hpw i j (by simpa using hi') (by simpa using hj') h
    simpa [hgi, hgj] using this
  · have := hpw j i (by simpa using hj') (by simpa using hi') h
    rw [Win.overlaps_comm]
    simpa [hgi, hgj] using this

include hp hd in
theorem skl_writes_pos : ∀ i n lo w, d.Writes i (n, lo, w) → 0 < w := by
  intro i n lo w h
  obtain ⟨p, -, hm, hw⟩ := writes_win hp hd h
  rcases procs_cases hm with rfl | rfl | rfl | ⟨i, -, rfl | rfl | rfl⟩ |
      ⟨l, -, i, -, ⟨-, rfl | rfl⟩ | ⟨-, rfl | rfl⟩⟩ | ⟨i, -, rfl⟩ <;>
    simp only [winOf, g00P, p00P, coutP, xP, g0P, p0P, gOpP, pOpP, gPassP, pPassP, sP,
      Prod.mk.injEq] at hw <;> omega

theorem cell_lt {N L l i : Nat} (hl : l < L) (hi : i ≤ N) :
    (l + 1) * (N + 1) + i + 1 ≤ (L + 1) * (N + 1) := by
  have := rowMajor_le (K := N + 1) (show l + 1 < L + 1 by omega)
  omega

set_option hygiene false in
macro "proc_cases" h:term : tactic =>
  `(tactic| rcases procs_cases $h with h | h | h | ⟨i, hi, h | h | h⟩ |
      ⟨l, hl, i, hi, ⟨hg, h | h⟩ | ⟨hg, h | h⟩⟩ | ⟨i, hi, h⟩)

set_option hygiene false in
macro "proc_unfold" "at" h:ident : tactic =>
  `(tactic| simp only [g00P, p00P, coutP, xP, g0P, p0P, gOpP, pOpP, gPassP, pPassP, sP,
      Process2.assign.injEq] at $h:ident)

include hN hp hd in
theorem skl_comb : CombDesign d where
  nodup := by
    rw [hd]
    simp only [sklDecls, sklDeclsRaw, List.map_cons, List.map_nil]
    decide
  assign := by
    intro j p hj
    have hm := mem_of_get hp hj
    proc_cases hm <;> subst h <;>
      first | exact ⟨_, _, _, rfl, rfl⟩ | exact ⟨_, _, [("cout", 0, 1)], rfl, by simp [dw_cout hd]⟩
  inWidth := by
    intro j n lo w h
    obtain ⟨p, -, hm, hw⟩ := writes_win hp hd h
    have h1 := row_ge N (lv N)
    proc_cases hm <;> subst h <;>
      simp only [winOf, g00P, p00P, coutP, xP, g0P, p0P, gOpP, pOpP, gPassP, pPassP, sP,
        Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl, rfl⟩ := hw
    all_goals first
      | exact ⟨_, dw_g hd, cell_lt hl hi⟩
      | exact ⟨_, dw_p hd, cell_lt hl hi⟩
      | exact ⟨_, dw_g hd, by omega⟩
      | exact ⟨_, dw_p hd, by omega⟩
      | exact ⟨_, dw_x hd, by omega⟩
      | exact ⟨_, dw_s hd, by omega⟩
      | exact ⟨_, dw_cout hd, by omega⟩
  notInput := by
    rintro n ⟨j, lo, w, h⟩
    obtain ⟨p, -, hm, hw⟩ := writes_win hp hd h
    rw [skl_inputNames hd]
    proc_cases hm <;> subst h <;>
      simp only [winOf, g00P, p00P, coutP, xP, g0P, p0P, gOpP, pOpP, gPassP, pPassP, sP,
        Prod.mk.injEq] at hw <;> rw [hw.1] <;> decide
  disjoint := skl_disjoint hp hd
  selfDisjoint := by
    intro j t e hj
    have hm := mem_of_get hp hj
    proc_cases hm <;> proc_unfold at h <;> obtain ⟨rfl, -⟩ := h <;>
      exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro j t e hj
    have hm := mem_of_get hp hj
    proc_cases hm <;> proc_unfold at h <;> obtain ⟨-, rfl⟩ := h <;> rfl
  rhsDeclared := by
    intro j t e hj
    have hm := mem_of_get hp hj
    rw [hd]
    proc_cases hm <;> proc_unfold at h <;> obtain ⟨-, rfl⟩ := h <;>
      simp [Expr2.idents, rd, sklDecls, sklDeclsRaw]
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [hd] at hdc
    simp [sklDecls, sklDeclsRaw] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [hd] at hdc
    simp [sklDecls, sklDeclsRaw] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Comb

/-! ## Acyclicity: the rank certificate

A process that writes `g` or `p` at offset `o` gets rank `o + 1`; `x` gets `0`; `s` and `cout` get
`(L + 1)(N + 1) + 1`, above every offset of `g`. Row `l + 1` reads only row `l` (offsets below its own),
`s` reads `x` and row `L`, `cout` reads row `L`; nobody reads `s` or `cout`, and nobody writes `a`, `b`, `cin`. -/

def prk (N L : Nat) : Process2 → Nat
  | .assign (.slice n lo _) _ => if n = "x" then 0 else if n = "s" then (L + 1) * (N + 1) + 1 else lo + 1
  | _ => (L + 1) * (N + 1) + 1

def sklRank (d : Design2) (N : Nat) (j : Nat) : Nat :=
  match d.processes[j]? with
  | some p => prk N (lv N) p
  | none => 0

theorem prk_slice {N L lo w : Nat} {n : String} {e : Expr2} (hx : n ≠ "x") (hs : n ≠ "s") :
    prk N L (.assign (.slice n lo w) e) = lo + 1 := by
  simp only [prk, if_neg hx, if_neg hs]

theorem prk_x {N L lo w : Nat} {e : Expr2} : prk N L (.assign (.slice "x" lo w) e) = 0 := rfl

theorem prk_s {N L lo w : Nat} {e : Expr2} :
    prk N L (.assign (.slice "s" lo w) e) = (L + 1) * (N + 1) + 1 := by
  simp only [prk]
  rw [if_neg (by decide)]
  rfl

theorem prk_ident {N L : Nat} {n : String} {e : Expr2} :
    prk N L (.assign (.ident n) e) = (L + 1) * (N + 1) + 1 := rfl

/-- A writer of a window that some read observes ranks at most one above the read's offset (reads never
observe `s` or `cout`). -/
theorem rank_le_of_read {N : Nat} {q : Process2} (hq : q ∈ sklProcs N) {n : String} {k : Nat}
    (hn1 : n ≠ "s") (hn2 : n ≠ "cout") (hov : (ReadWin.win n k 1).overlaps (winOf q) = true) :
    prk N (lv N) q ≤ k + 1 := by
  proc_cases hq <;> subst h <;>
    simp only [winOf, g00P, p00P, coutP, xP, g0P, p0P, gOpP, pOpP, gPassP, pPassP, sP,
      ReadWin.overlaps, Win.overlaps_eq_true] at hov ⊢ <;>
    obtain ⟨rfl, h1, h2⟩ := hov
  all_goals first
    | exact absurd rfl hn1
    | exact absurd rfl hn2
    | (rw [prk_x]; omega)
    | (rw [prk_slice (by decide) (by decide)]; omega)

/-- Nobody writes the inputs. -/
theorem read_ab {N : Nat} {q : Process2} (hq : q ∈ sklProcs N) {k : Nat} (n : String)
    (hn : n = "a" ∨ n = "b") : (ReadWin.win n k 1).overlaps (winOf q) = false := by
  rcases hn with rfl | rfl <;>
  proc_cases hq <;> subst h <;>
    simp only [winOf, g00P, p00P, coutP, xP, g0P, p0P, gOpP, pOpP, gPassP, pPassP, sP,
      ReadWin.overlaps] <;>
    (rw [Win.overlaps_eq_false]; left; decide)

theorem no_whole_cin {N : Nat} {q : Process2} (hq : q ∈ sklProcs N) :
    (ReadWin.whole "cin").overlaps (winOf q) = false := by
  proc_cases hq <;> subst h <;>
    simp [winOf, g00P, p00P, coutP, xP, g0P, p0P, gOpP, pOpP, gPassP, pPassP, sP, ReadWin.overlaps]

macro "rank_close" : tactic =>
  `(tactic| first
    | (rw [prk_slice (by decide) (by decide)]; omega)
    | (rw [prk_ident]; omega)
    | (rw [prk_s]; omega))

section Acyc

variable {N : Nat} {d : Design2} (hp : d.processes.toList = sklProcs N)
  (hd : d.decls.toList = sklDecls N)

include hp hd in
theorem skl_acyclic : Acyclic d := by
  refine ⟨sklRank d N, ?_⟩
  intro i j ti ei tj ej wj hi hj hw hex
  have hmi := mem_of_get hp hi
  have hmj := mem_of_get hp hj
  rw [wins_eq hd hmj rfl, List.mem_singleton] at hw
  subst hw
  simp only [sklRank, hi, hj]
  generalize Process2.assign tj ej = q at hmj hex ⊢
  obtain ⟨r, hr, hov⟩ := hex
  have hL : (lv N + 1) * (N + 1) = lv N * (N + 1) + (N + 1) := Nat.succ_mul _ _
  have hW := row_ge N (lv N)
  proc_cases hmi <;> proc_unfold at h <;> obtain ⟨rfl, rfl⟩ := h
  all_goals simp only [Expr2.reads, Expr2.sliceReads, rd, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  all_goals (try have hl1 : (l + 1) * (N + 1) = l * (N + 1) + (N + 1) := Nat.succ_mul _ _)
  all_goals (try have hpl := (part_lt hg).2)
  all_goals first
    | (subst hr; rw [no_whole_cin hmj] at hov; cases hov)
    | (rcases hr with rfl | rfl <;> rw [read_ab hmj _ (by decide)] at hov <;> cases hov)
    | (rcases hr with rfl | rfl | rfl <;> (have := rank_le_of_read hmj (by decide) (by decide) hov) <;>
        rank_close)
    | (rcases hr with rfl | rfl <;> (have := rank_le_of_read hmj (by decide) (by decide) hov) <;>
        rank_close)
    | (subst hr; have := rank_le_of_read hmj (by decide) (by decide) hov; rank_close)

end Acyc

/-! ## `design.sem N` is the instantiated design -/

theorem skl_sem_eq (N : Nat) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) : design.sem N = sklDesign N := by
  show design.pdesign.instantiateGD2 [(N : Int)] = _
  exact PDesign.instantiateGD2_of_combDesign (skl_instantiate2 N hN')
    (skl_comb hN (sklDesign_processes N) (sklDesign_decls N hN))
    (skl_writes_pos (sklDesign_processes N) (sklDesign_decls N hN))

theorem sem_processes (N : Nat) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) :
    (design.sem N).processes.toList = sklProcs N := by
  rw [skl_sem_eq N hN hN', sklDesign_processes]

theorem sem_decls (N : Nat) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) :
    (design.sem N).decls.toList = sklDecls N := by
  rw [skl_sem_eq N hN hN', sklDesign_decls N hN]


/-! ## Membership of the cells the settled state reads -/

section Mem

variable {N : Nat}

theorem mem_g00 : g00P ∈ sklProcs N := by simp [sklProcs]
theorem mem_p00 : p00P ∈ sklProcs N := by simp [sklProcs]
theorem mem_cout : coutP N (lv N) ∈ sklProcs N := by simp [sklProcs]

theorem mem_in {i : Nat} (hi : i < N) {p : Process2} (hp : p ∈ [xP i, g0P i, p0P i]) :
    p ∈ sklProcs N :=
  List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hp⟩))

theorem mem_node {l i : Nat} (hl : l < lv N) (hi : i ≤ N) {p : Process2} (hp : p ∈ nodeP N l i) :
    p ∈ sklProcs N :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl,
      List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (by omega), hp⟩⟩)))

theorem mem_s {i : Nat} (hi : i < N) : sP N (lv N) i ∈ sklProcs N :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))

end Mem

/-! ## Gate algebra on known 1-bit values -/

section Gates

variable {st : SvState}

theorem eval_bit {n : String} {w : Nat} {x : BitVec w} {i : Nat}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) (hi : i < w) :
    evalPure2 st (rd n i) = .ok (LVec.ofBitVec (BitVec.ofBool (x.getLsbD i))) :=
  evalPure2_bit_ofBitVec (evalPure2_ident_ofBitVec h) hi

theorem eval_win {n : String} {u : LVec} {k : Nat} {b : Bool}
    (h : SvState.lookup st n = some u) (hk : u.extract k 1 = LVec.ofBitVec (BitVec.ofBool b)) :
    evalPure2 st (rd n k) = .ok (LVec.ofBitVec (BitVec.ofBool b)) := by
  simp only [rd, evalPure2_slice, evalPure2_ident_of_lookup h, Pure2.res_ok_bind, Pure2.res_pure_eq,
    hk]

theorem eval_and {l r : Expr2} {p q : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool q))) :
    evalPure2 st (.binary .and l r) = .ok (LVec.ofBitVec (BitVec.ofBool (p && q))) := by
  rw [evalPure2_and_ofBitVec hl hr, BitVec.ofBool_and_ofBool]

theorem eval_or {l r : Expr2} {p q : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool q))) :
    evalPure2 st (.binary .or l r) = .ok (LVec.ofBitVec (BitVec.ofBool (p || q))) := by
  rw [evalPure2_or_ofBitVec hl hr, BitVec.ofBool_or_ofBool]

theorem eval_xor {l r : Expr2} {p q : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool q))) :
    evalPure2 st (.binary .xor l r) = .ok (LVec.ofBitVec (BitVec.ofBool (p ^^ q))) := by
  rw [evalPure2_xor_ofBitVec hl hr, BitVec.ofBool_xor_ofBool]

theorem res1 (b : Bool) : (LVec.ofBitVec (BitVec.ofBool b)).resizeU 1 = LVec.ofBitVec (BitVec.ofBool b) := by
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

theorem lit0_eq : lit0 = LVec.ofBitVec (BitVec.ofBool false) := by decide

end Gates

/-! ## The settled state -/

theorem skl_settled {N : Nat} (hN : 1 ≤ N) (hN' : N < 2 ^ 31) {st : SvState}
    (heqs : CombEqs (design.sem N) st) (hs : StateShape (design.sem N) st)
    {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
      SvState.lookup st "cout" =
        some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  have hp := sem_processes N hN hN'
  have hd := sem_decls N hN hN'
  have hcomb := skl_comb hN hp hd
  have hdrv : ∀ {n : String} {lo : Nat} {e : Expr2},
      Process2.assign (.slice n lo 1) e ∈ sklProcs N → Driven (design.sem N) n := by
    intro n lo e h
    obtain ⟨j, hj⟩ := get_of_mem hp h
    exact ⟨j, lo, 1, ⟨_, _, hj, by simp⟩⟩
  obtain ⟨ug, hug, -⟩ := hs.driven "g" (hdrv (mem_g00 (N := N)))
  obtain ⟨up, hup, -⟩ := hs.driven "p" (hdrv (mem_p00 (N := N)))
  obtain ⟨ux, hux, -⟩ := hs.driven "x" (hdrv (mem_in (N := N) (i := 0) hN (p := xP 0) (by simp)))
  obtain ⟨us, hus, hsw⟩ := hs.driven "s" (hdrv (mem_s (N := N) (i := 0) hN))
  -- the inputs' bits, the positions of the adder
  have hrow : ∀ l, l ≤ lv N → ∀ i, i ≤ N →
      ug.extract (l * (N + 1) + i) 1 =
          LVec.ofBitVec (BitVec.ofBool (Core.sklRec (Lib.addPos x.getLsbD y.getLsbD ci) l i).1) ∧
        up.extract (l * (N + 1) + i) 1 =
          LVec.ofBitVec (BitVec.ofBool (Core.sklRec (Lib.addPos x.getLsbD y.getLsbD ci) l i).2) := by
    intro l
    induction l with
    | zero =>
      intro _ i hi
      rw [Nat.zero_mul, Nat.zero_add, Core.sklRec_zero]
      cases i with
      | zero =>
        obtain ⟨jg, hjg⟩ := get_of_mem hp (mem_g00 (N := N))
        obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs hjg (evalPure2_ident_ofBitVec hc)
        rw [hug, Option.some.injEq] at hold
        subst hold
        obtain ⟨jp, hjp⟩ := get_of_mem hp (mem_p00 (N := N))
        obtain ⟨old', hold', hext'⟩ := CombEqs.extract_slice heqs hjp (evalPure2_lit st lit0)
        rw [hup, Option.some.injEq] at hold'
        subst hold'
        refine ⟨by rw [hext, res1]; rfl, ?_⟩
        rw [hext', lit0_eq, res1]
        rfl
      | succ k =>
        have hk : k < N := by omega
        obtain ⟨jg, hjg⟩ := get_of_mem hp (mem_in (N := N) hk (p := g0P k) (by simp))
        obtain ⟨old, hold, hext⟩ :=
          CombEqs.extract_slice heqs hjg (eval_and (eval_bit ha hk) (eval_bit hb hk))
        rw [hug, Option.some.injEq] at hold
        subst hold
        obtain ⟨jp, hjp⟩ := get_of_mem hp (mem_in (N := N) hk (p := p0P k) (by simp))
        obtain ⟨old', hold', hext'⟩ :=
          CombEqs.extract_slice heqs hjp (eval_xor (eval_bit ha hk) (eval_bit hb hk))
        rw [hup, Option.some.injEq] at hold'
        subst hold'
        exact ⟨by rw [hext, res1]; rfl, by rw [hext', res1]; rfl⟩
    | succ l ih =>
      intro hl i hi
      have hlL : l < lv N := by omega
      have ih' := ih (by omega)
      rw [Core.sklRec_succ]
      obtain ⟨h1, h2⟩ := ih' i hi
      by_cases hg : (i >>> l) % 2 = 1
      · rw [if_pos hg]
        have hg' : i / 2 ^ l % 2 = 1 := (Core.guard_iff_div l i).mp hg
        have hpart : ((i >>> l) <<< l) - 1 = part l i := by rw [Core.shl_shr]; rfl
        have hplt := Core.partner_lt hg
        rw [hpart] at hplt ⊢
        obtain ⟨h3, h4⟩ := ih' (part l i) (by omega)
        obtain ⟨jg, hjg⟩ := get_of_mem hp (mem_node hlL hi (p := gOpP N l i) (by simp [nodeP, hg']))
        obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs hjg
          (eval_or (eval_win hug h1) (eval_and (eval_win hup h2) (eval_win hug h3)))
        rw [hug, Option.some.injEq] at hold
        subst hold
        obtain ⟨jp, hjp⟩ := get_of_mem hp (mem_node hlL hi (p := pOpP N l i) (by simp [nodeP, hg']))
        obtain ⟨old', hold', hext'⟩ := CombEqs.extract_slice heqs hjp
          (eval_and (eval_win hup h2) (eval_win hup h4))
        rw [hup, Option.some.injEq] at hold'
        subst hold'
        exact ⟨by rw [hext, res1]; rfl, by rw [hext', res1]; rfl⟩
      · rw [if_neg hg]
        have hg' : ¬ i / 2 ^ l % 2 = 1 := fun h => hg ((Core.guard_iff_div l i).mpr h)
        obtain ⟨jg, hjg⟩ := get_of_mem hp (mem_node hlL hi (p := gPassP N l i) (by simp [nodeP, hg']))
        obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs hjg (eval_win hug h1)
        rw [hug, Option.some.injEq] at hold
        subst hold
        obtain ⟨jp, hjp⟩ := get_of_mem hp (mem_node hlL hi (p := pPassP N l i) (by simp [nodeP, hg']))
        obtain ⟨old', hold', hext'⟩ := CombEqs.extract_slice heqs hjp (eval_win hup h2)
        rw [hup, Option.some.injEq] at hold'
        subst hold'
        exact ⟨by rw [hext, res1], by rw [hext', res1]⟩
  -- the last level holds the carries
  have hcarry : ∀ i, i ≤ N →
      ug.extract (lv N * (N + 1) + i) 1 = LVec.ofBitVec (BitVec.ofBool (BitVec.carry i x y ci)) := by
    intro i hi
    rw [(hrow (lv N) (Nat.le_refl _) i hi).1, Core.skl_carry_clog2 _ _ _ hi, Lib.rippleCarry_bv]
  have hxbit : ∀ i, i < N →
      ux.extract i 1 = LVec.ofBitVec (BitVec.ofBool (x.getLsbD i ^^ y.getLsbD i)) := by
    intro i hi
    obtain ⟨j, hj⟩ := get_of_mem hp (mem_in (N := N) hi (p := xP i) (by simp))
    obtain ⟨old, hold, hext⟩ :=
      CombEqs.extract_slice heqs hj (eval_xor (eval_bit ha hi) (eval_bit hb hi))
    rw [hux, Option.some.injEq] at hold
    subst hold
    rw [hext, res1]
  -- the sum, from its 1-bit windows
  rw [dw_s hd, Option.some.injEq] at hsw
  have hS : us = LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N) := by
    apply LVec.eq_ofBitVec_of_extract_one hsw.symm
    intro i hi
    obtain ⟨j, hj⟩ := get_of_mem hp (mem_s (N := N) hi)
    obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs hj
      (eval_xor (eval_win hux (hxbit i hi)) (eval_win hug (hcarry i (by omega))))
    rw [hus, Option.some.injEq] at hold
    subst hold
    rw [hext, res1, BitVec.getLsbD_add_add_bool hi, Bool.xor_assoc]
  -- the carry out: `g[L][N]` is the final carry
  obtain ⟨jc, hjc⟩ := get_of_mem hp (mem_cout (N := N))
  have hco := CombEqs.lookup_ident hcomb heqs hs hjc (eval_win hug (hcarry N (Nat.le_refl N)))
    (dw_cout hd)
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.carry_width] at hco
  exact ⟨hS ▸ hus, hco⟩


/-! ## From the settled state to the task's function -/

theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

theorem sum_eq_ofNat {N : Nat} (hN : 1 ≤ N) (x y : BitVec N) (ci : Bool) :
    x + y + (BitVec.ofBool ci).setWidth N =
      BitVec.ofNat N (x.toNat + y.toNat + (BitVec.ofBool ci).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
  have hc : ci.toNat < 2 ^ N := by have := Bool.toNat_le ci; omega
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hc, Nat.mod_add_mod]

theorem carry_eq_ofNat {N : Nat} (t : Nat) (ht : t < 2 * 2 ^ N) :
    BitVec.ofBool (decide (2 ^ N ≤ t)) = BitVec.ofNat 1 (t / 2 ^ N) := by
  by_cases h : 2 ^ N ≤ t
  · have hq : t / 2 ^ N = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [h, hq]
  · have hq : t / 2 ^ N = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, hq]

theorem add_interface (N : Nat) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  simp [CombTask.Interface, inputPorts, outputPorts, sem_decls N hN hN', sklDecls, sklDeclsRaw,
    SvGolf.Tasks.Add.task]

/-- **The Sklansky adder meets the `add` statement**, for every `N` in the task's range. -/
theorem solution : Goal := by
  intro N hN
  obtain ⟨hN1, hN2⟩ := hN
  refine CombTask.satisfiedAt_of_comb (add_interface N hN1 hN2)
    (skl_comb hN1 (sem_processes N hN1 hN2) (sem_decls N hN1 hN2))
    (skl_acyclic (sem_processes N hN1 hN2) (sem_decls N hN1 hN2)) ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨ha, hb, hc⟩ := hv
  obtain ⟨hs', hco⟩ := skl_settled hN1 hN2 heqs hs ha hb hc
  have ht : x.toNat + y.toNat + c0.toNat < 2 * 2 ^ N := by
    have : x.toNat < 2 ^ N := x.isLt
    have : y.toNat < 2 ^ N := y.isLt
    have := Bool.toNat_le c0
    have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN1
    omega
  refine ⟨?_, ?_⟩
  · rw [hs', sum_eq_ofNat hN1]
  · rw [hco, carry_eq_ofNat _ ht, BitVec.toNat_ofBool]

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission

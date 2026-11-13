import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2
import LeanModels.Sv.Lib.Prefix

/-!
# Task `add`: the Kogge-Stone parallel-prefix adder `add_n_kogge_stone.sv`, proved by hand

The design, as written: positions `0 … N` (position `0` is `cin` with propagate `0`, position `k + 1` is bit `k`),
`L = $clog2(N + 1)` levels of a 2-D array pair `g, p : [L:0][N:0]`, level `l + 1` combining position `i` with
position `i - (1 << l)` when `i >= (1 << l)` (a conditional generate inside the nested level/node loops) and
passing it through otherwise; `s[i] = x[i] ^ g[L][i]`, `cout = g[L][N]`.

The `sv_comb` tactics refuse the design (a conditional generate inside an inner generate loop), so this file is
the by-hand route of `tasks/add/reference/add_n_byhand.lean`, for every `N` with `1 ≤ N < 2^31`:

1. **The design at symbolic `N`** (`ks_instantiate2`): the parameter stage by `rfl` (the `int` localparam `L` is
   bound as the 32-bit squash of `$clog2(N + 1)`, equal to `clog2 (N + 1)` below `2^31`, `ksLv_eq`), the
   declarations and element widths by `simp`, the four generate items by the `Gen2` lemmas (the node's
   generate-if through `GenItem.expand2_genIf_of_ne`/`_of_eq`, the 2-D cells through `arrayElemWindow_desc0_2`).
2. **The comb profile and acyclicity** (`ksM_comb`, `ksM_acyclic`): every process writes one bit (or the whole
   1-bit `cout`); the windows are pairwise disjoint (`ws_pairwise`); the rank of a pair of level `l` is `l + 1`.
   `design.sem N` is then the instantiated design (`ks_sem_eq`, `PDesign.instantiateGD2_of_combDesign`).
3. **The arithmetic** (`ksRec_block`): after level `l` position `k` holds the generate/propagate pair of the
   block `[k + 1 - 2^l, k]` of the adder's positions (`LeanModels.Sv.Lib.pgBlock`, natural subtraction), so at
   level `L` it holds the carry into bit `k` (`ks_carry`).
4. **The settled state** (`ks_settled`): by induction on the level, every window of `g` and `p` holds the
   recurrence; the sum bits and the carry out follow (`BitVec.getLsbD_add_add_bool`, `BitVec.carry_width`), and
   `CombTask.satisfiedAt_of_comb` gives the statement (`solution`).

No `sorry`, `native_decide` or `bv_decide`; the axioms are pinned at the end.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-! ## 1a. The envelope's shape (pinned by `rfl`) -/

/-- `assign x[i] = a[i] ^ b[i];` -/
def xT : PProcess :=
  .assignL (.bitSel "x" (.genvarRef "i"))
    (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "i")) (.bitSel (.ident "b") (.genvarRef "i")))

/-- `assign g[0][i+1] = a[i] & b[i];` -/
def g0T : PProcess :=
  .assignL (.arrayElem "g" [.int 0, .binary (.m0 .add) (.genvarRef "i") (.int 1)])
    (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "i")) (.bitSel (.ident "b") (.genvarRef "i")))

/-- `assign p[0][i+1] = a[i] ^ b[i];` -/
def p0T : PProcess :=
  .assignL (.arrayElem "p" [.int 0, .binary (.m0 .add) (.genvarRef "i") (.int 1)])
    (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "i")) (.bitSel (.ident "b") (.genvarRef "i")))

/-- The shift `1 << l`. -/
def shT : PExpr := .binary .shl (.int 1) (.genvarRef "l")

/-- The partner index `i - (1 << l)`. -/
def ptT : PExpr := .binary (.m0 .sub) (.genvarRef "i") shT

/-- `l + 1`. -/
def l1T : PExpr := .binary (.m0 .add) (.genvarRef "l") (.int 1)

/-- `assign g[l+1][i] = g[l][i] | (p[l][i] & g[l][i - (1 << l)]);` -/
def gOpT : PProcess :=
  .assignL (.arrayElem "g" [l1T, .genvarRef "i"])
    (.binary (.m0 .or) (.arrayElem "g" [.genvarRef "l", .genvarRef "i"])
      (.binary (.m0 .and) (.arrayElem "p" [.genvarRef "l", .genvarRef "i"])
        (.arrayElem "g" [.genvarRef "l", ptT])))

/-- `assign p[l+1][i] = p[l][i] & p[l][i - (1 << l)];` -/
def pOpT : PProcess :=
  .assignL (.arrayElem "p" [l1T, .genvarRef "i"])
    (.binary (.m0 .and) (.arrayElem "p" [.genvarRef "l", .genvarRef "i"])
      (.arrayElem "p" [.genvarRef "l", ptT]))

/-- `assign g[l+1][i] = g[l][i];` -/
def gPassT : PProcess :=
  .assignL (.arrayElem "g" [l1T, .genvarRef "i"]) (.arrayElem "g" [.genvarRef "l", .genvarRef "i"])

/-- `assign p[l+1][i] = p[l][i];` -/
def pPassT : PProcess :=
  .assignL (.arrayElem "p" [l1T, .genvarRef "i"]) (.arrayElem "p" [.genvarRef "l", .genvarRef "i"])

/-- `assign s[i] = x[i] ^ g[L][i];` -/
def sT : PProcess :=
  .assignL (.bitSel "s" (.genvarRef "i"))
    (.binary (.m0 .xor) (.bitSel (.ident "x") (.genvarRef "i"))
      (.arrayElem "g" [.paramRef "L" none, .genvarRef "i"]))

/-- The guard `i >= (1 << l)`. -/
def guardT : PExpr := .binary .sge (.genvarRef "i") shT

/-- The conditional generate of one node. -/
def nodeGen : GenItem :=
  .genIf guardT ([gOpT, pOpT].map GenItem.process) ([gPassT, pPassT].map GenItem.process)

/-- `for (i = 0; i < N + 1; i++) <nodeGen>` -/
def nodeLoop : GenItem :=
  .genFor (some "g_node") "i" (.int 0)
    (.binary .slt (.genvarRef "i") (.binary (.m0 .add) (.paramRef "N" none) (.int 1)))
    (.unary .inc (.genvarRef "i")) (some 17) [nodeGen]

/-- `for (i = 0; i < N; i++)` over `x`, `g[0]`, `p[0]`. -/
def inGen : GenItem :=
  .genFor (some "g_in") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 16) ([xT, g0T, p0T].map GenItem.process)

/-- `for (l = 0; l < L; l++) <nodeLoop>` -/
def lvlGen : GenItem :=
  .genFor (some "g_lvl") "l" (.int 0) (.binary .slt (.genvarRef "l") (.paramRef "L" none))
    (.unary .inc (.genvarRef "l")) (some 5) [nodeLoop]

/-- `for (i = 0; i < N; i++) <sT>` -/
def sumGen : GenItem :=
  .genFor (some "g_sum") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 16) ([sT].map GenItem.process)

theorem ks_generates : design.pdesign.generates = [inGen, lvlGen, sumGen] := rfl

/-- `g[0][0] = cin`, `p[0][0] = 1'b0`, `cout = g[L][N]`. -/
def g00T : PProcess := .assignL (.arrayElem "g" [.int 0, .int 0]) (.ident "cin")
def p00T : PProcess := .assignL (.arrayElem "p" [.int 0, .int 0]) (.lit { bits := #[Logic.l0] })
def coutT : PProcess := .assign "cout" (.arrayElem "g" [.paramRef "L" none, .paramRef "N" none])

theorem ks_static_source : design.pdesign.processes = [g00T, p00T, coutT] := rfl

theorem ks_others : design.pdesign.others = [] := rfl

/-! ## 1b. The instantiated vocabulary -/

/-- The one-bit literal `1'b0`. -/
def lit0 : LVec := { bits := #[Logic.l0] }

def g00P : Process2 := .assign (.slice "g" 0 1) (.ident "cin")
def p00P : Process2 := .assign (.slice "p" 0 1) (.lit lit0)
def coutP (N L : Nat) : Process2 := .assign (.ident "cout") (.slice (.ident "g") (L * (N + 1) + N) 1)

def xP (i : Nat) : Process2 :=
  .assign (.slice "x" i 1) (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
def g0P (i : Nat) : Process2 :=
  .assign (.slice "g" (i + 1) 1) (.binary .and (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
def p0P (i : Nat) : Process2 :=
  .assign (.slice "p" (i + 1) 1) (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))

def gOpP (N l i : Nat) : Process2 :=
  .assign (.slice "g" ((l + 1) * (N + 1) + i) 1)
    (.binary .or (.slice (.ident "g") (l * (N + 1) + i) 1)
      (.binary .and (.slice (.ident "p") (l * (N + 1) + i) 1)
        (.slice (.ident "g") (l * (N + 1) + (i - 2 ^ l)) 1)))
def pOpP (N l i : Nat) : Process2 :=
  .assign (.slice "p" ((l + 1) * (N + 1) + i) 1)
    (.binary .and (.slice (.ident "p") (l * (N + 1) + i) 1)
      (.slice (.ident "p") (l * (N + 1) + (i - 2 ^ l)) 1))
def gPassP (N l i : Nat) : Process2 :=
  .assign (.slice "g" ((l + 1) * (N + 1) + i) 1) (.slice (.ident "g") (l * (N + 1) + i) 1)
def pPassP (N l i : Nat) : Process2 :=
  .assign (.slice "p" ((l + 1) * (N + 1) + i) 1) (.slice (.ident "p") (l * (N + 1) + i) 1)

def sP (N L i : Nat) : Process2 :=
  .assign (.slice "s" i 1) (.binary .xor (.slice (.ident "x") i 1) (.slice (.ident "g") (L * (N + 1) + i) 1))

/-- One node of level `l` at position `i`: the combining pair or the passing pair. -/
def nodeP (N l i : Nat) : List Process2 :=
  if 2 ^ l ≤ i then [gOpP N l i, pOpP N l i] else [gPassP N l i, pPassP N l i]

/-- The generate expansion. -/
def ksGens (N L : Nat) : List Process2 :=
  ((List.range N).flatMap fun i => [xP i, g0P i, p0P i]) ++
    (((List.range L).flatMap fun l => (List.range (N + 1)).flatMap fun i => nodeP N l i) ++
      (List.range N).map (sP N L))

/-! ## 1c. Template instantiation in any environment that binds `N`, `L` and the two arrays -/

/-- What the templates read from an environment. -/
structure KsEnv (E : IEnv) (N L : Nat) : Prop where
  hN : E.vals.lookup "N" = some (N : Int)
  hL : E.vals.lookup "L" = some (L : Int)
  hg : E.dims.lookup "g" = some [((L : Int), 0), ((N : Int), 0)]
  hp : E.dims.lookup "p" = some [((L : Int), 0), ((N : Int), 0)]

/-- What the templates read from the element widths. -/
structure KsElems (elems : List (String × Nat)) : Prop where
  ha : elems.lookup "a" = some 1
  hb : elems.lookup "b" = some 1
  hx : elems.lookup "x" = some 1
  hs : elems.lookup "s" = some 1

theorem KsEnv.bind {E : IEnv} {N L : Nat} (h : KsEnv E N L) (g : String) (hgN : g ≠ "N")
    (hgL : g ≠ "L") (v : Int) : KsEnv (E.bindVal g v) N L where
  hN := by rw [vals_lookup_bindVal_ne v (Ne.symm hgN)]; exact h.hN
  hL := by rw [vals_lookup_bindVal_ne v (Ne.symm hgL)]; exact h.hL
  hg := by simpa using h.hg
  hp := by simpa using h.hp

theorem KsEnv.withDecls {E : IEnv} {N L : Nat} (h : KsEnv E N L) (decls : List Decl) :
    KsEnv (E.withDecls decls) N L where
  hN := by simpa using h.hN
  hL := by simpa using h.hL
  hg := by simpa using h.hg
  hp := by simpa using h.hp

/-- A 2-D cell `n[r][c]` of a `[L:0][N:0]` array at in-range labels: the 1-bit window at `r * (N + 1) + c`. -/
theorem ks_win {E : IEnv} {n : String} {N L r c : Nat} {ie je : PExpr}
    (hd : E.dims.lookup n = some [((L : Int), 0), ((N : Int), 0)])
    (hi : evalInt E ie = .ok (r : Int)) (hr : r ≤ L)
    (hj : evalInt E je = .ok (c : Int)) (hc : c ≤ N) :
    arrayElemWindow E n [ie, je] = .ok (((r * (N + 1) + c : Nat) : Int), 1, true) := by
  rw [arrayElemWindow_desc0_2 hd (by omega) (by omega) hi (by omega) (by omega) hj (by omega)
    (by omega)]
  push_cast
  rfl

theorem ks_read {E : IEnv} {elems : List (String × Nat)} {n : String} {N L r c : Nat} {ie je : PExpr}
    (hd : E.dims.lookup n = some [((L : Int), 0), ((N : Int), 0)])
    (hi : evalInt E ie = .ok (r : Int)) (hr : r ≤ L)
    (hj : evalInt E je = .ok (c : Int)) (hc : c ≤ N) :
    fitExpr2 E elems (some 1) (.arrayElem n [ie, je]) = .slice (.ident n) (r * (N + 1) + c) 1 := by
  have hw := ks_win hd hi hr hj hc
  rw [fitExpr2_arrayElem_of hw, arrayElemRead_of_inRange hw, Int.toNat_natCast]

theorem ks_tgt {E : IEnv} {elems : List (String × Nat)} {n : String} {N L r c : Nat} {ie je : PExpr}
    (hd : E.dims.lookup n = some [((L : Int), 0), ((N : Int), 0)])
    (hi : evalInt E ie = .ok (r : Int)) (hr : r ≤ L)
    (hj : evalInt E je = .ok (c : Int)) (hc : c ≤ N) :
    instLhs2 E elems (.arrayElem n [ie, je]) = .ok (.slice n (r * (N + 1) + c) 1, 1) := by
  rw [instLhs2_arrayElem, arrayElemTarget_of_inRange (ks_win hd hi hr hj hc), Int.toNat_natCast]

/-- The environment of one node: `l` then `i` bound. -/
abbrev nodeEnv (E : IEnv) (l i : Nat) : IEnv := (E.bindVal "l" (l : Int)).bindVal "i" (i : Int)

theorem node_i (E : IEnv) (l i : Nat) : evalInt (nodeEnv E l i) (.genvarRef "i") = .ok (i : Int) :=
  evalInt_genvarRef_of (by simp)

theorem node_l (E : IEnv) (l i : Nat) : evalInt (nodeEnv E l i) (.genvarRef "l") = .ok (l : Int) :=
  evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])

theorem node_l1 (E : IEnv) (l i : Nat) : evalInt (nodeEnv E l i) l1T = .ok ((l + 1 : Nat) : Int) := by
  rw [l1T, evalInt_add_of rfl rfl (node_l E l i) (evalInt_int 1)]
  push_cast
  rfl

theorem node_sh (E : IEnv) (l i : Nat) : evalInt (nodeEnv E l i) shT = .ok ((2 ^ l : Nat) : Int) := by
  simp only [shT, evalInt, PExpr.isInt, Bool.and_self, if_true, Gen2.except_ok_bind]
  simp only [Int.one_mul]
  push_cast
  rfl

theorem node_pt (E : IEnv) (l i : Nat) (hg : 2 ^ l ≤ i) :
    evalInt (nodeEnv E l i) ptT = .ok ((i - 2 ^ l : Nat) : Int) := by
  rw [ptT, evalInt_sub_of rfl rfl (node_i E l i) (node_sh E l i)]
  rw [Int.ofNat_sub hg]

theorem node_guard (E : IEnv) (l i : Nat) :
    evalGenGuard (nodeEnv E l i) guardT = .ok (if 2 ^ l ≤ i then 1 else 0) := by
  have hi : (nodeEnv E l i).vals.lookup "i" = some (i : Int) := by simp
  have hl : (nodeEnv E l i).vals.lookup "l" = some (l : Int) := by simp [IEnv.bindVal, List.lookup]
  have h0 : ¬ ((l : Int) < 0) := by omega
  simp only [guardT, shT, evalGenGuard, hi, hl, h0, if_false, Gen2.except_ok_bind,
    Int.toNat_natCast, Int.one_mul]
  by_cases h : 2 ^ l ≤ i
  · have h' : (i : Int) ≥ (2 : Int) ^ l := by exact_mod_cast h
    simp [h, h']
    rfl
  · have h' : ¬ ((i : Int) ≥ (2 : Int) ^ l) := by exact_mod_cast h
    simp [h, h']
    rfl

section templates

variable {E : IEnv} {elems : List (String × Nat)} {N L : Nat} (hE : KsEnv E N L)
include hE

theorem gOp_inst {l i : Nat} (hl : l < L) (hi : i ≤ N) (hg : 2 ^ l ≤ i) :
    instProcess2 (nodeEnv E l i) elems gOpT = gOpP N l i := by
  have hE' := (hE.bind "l" (by decide) (by decide) l).bind "i" (by decide) (by decide) i
  rw [gOpT, instProcess2_assignL _ (ks_tgt hE'.hg (node_l1 E l i) (by omega) (node_i E l i) hi),
    fitExpr2_binary, instExpr2_or, ks_read hE'.hg (node_l E l i) (by omega) (node_i E l i) hi,
    fitExpr2_binary, instExpr2_and, ks_read hE'.hp (node_l E l i) (by omega) (node_i E l i) hi,
    ks_read hE'.hg (node_l E l i) (by omega) (node_pt E l i hg) (Nat.le_trans (Nat.sub_le _ _) hi)]
  rfl

theorem pOp_inst {l i : Nat} (hl : l < L) (hi : i ≤ N) (hg : 2 ^ l ≤ i) :
    instProcess2 (nodeEnv E l i) elems pOpT = pOpP N l i := by
  have hE' := (hE.bind "l" (by decide) (by decide) l).bind "i" (by decide) (by decide) i
  rw [pOpT, instProcess2_assignL _ (ks_tgt hE'.hp (node_l1 E l i) (by omega) (node_i E l i) hi),
    fitExpr2_binary, instExpr2_and, ks_read hE'.hp (node_l E l i) (by omega) (node_i E l i) hi,
    ks_read hE'.hp (node_l E l i) (by omega) (node_pt E l i hg) (Nat.le_trans (Nat.sub_le _ _) hi)]
  rfl

theorem gPass_inst {l i : Nat} (hl : l < L) (hi : i ≤ N) :
    instProcess2 (nodeEnv E l i) elems gPassT = gPassP N l i := by
  have hE' := (hE.bind "l" (by decide) (by decide) l).bind "i" (by decide) (by decide) i
  rw [gPassT, instProcess2_assignL _ (ks_tgt hE'.hg (node_l1 E l i) (by omega) (node_i E l i) hi),
    ks_read hE'.hg (node_l E l i) (by omega) (node_i E l i) hi]
  rfl

theorem pPass_inst {l i : Nat} (hl : l < L) (hi : i ≤ N) :
    instProcess2 (nodeEnv E l i) elems pPassT = pPassP N l i := by
  have hE' := (hE.bind "l" (by decide) (by decide) l).bind "i" (by decide) (by decide) i
  rw [pPassT, instProcess2_assignL _ (ks_tgt hE'.hp (node_l1 E l i) (by omega) (node_i E l i) hi),
    ks_read hE'.hp (node_l E l i) (by omega) (node_i E l i) hi]
  rfl

end templates

/-! ## 1d. The other templates -/

/-- The environment of one bit of the input and sum loops: `i` bound. -/
abbrev bitEnv (E : IEnv) (i : Nat) : IEnv := E.bindVal "i" (i : Int)

theorem bit_i (E : IEnv) (i : Nat) : evalInt (bitEnv E i) (.genvarRef "i") = .ok (i : Int) :=
  evalInt_genvarRef_of (by simp)

theorem bit_i1 (E : IEnv) (i : Nat) :
    evalInt (bitEnv E i) (.binary (.m0 .add) (.genvarRef "i") (.int 1)) = .ok ((i + 1 : Nat) : Int) := by
  rw [evalInt_add_of rfl rfl (bit_i E i) (evalInt_int 1)]
  push_cast
  rfl

section templates2

variable {E : IEnv} {elems : List (String × Nat)} {N L : Nat} (hE : KsEnv E N L) (hel : KsElems elems)
include hE hel

omit hE in
theorem x_inst (i : Nat) : instProcess2 (bitEnv E i) elems xT = xP i := by
  rw [xT, instProcess2_assignL _ (instLhs2_bitSel hel.hx (bit_i E i) (by omega)), fitExpr2_binary,
    instExpr2_xor, fitExpr2_bitSel_ident hel.ha (bit_i E i) (by omega),
    fitExpr2_bitSel_ident hel.hb (bit_i E i) (by omega)]
  simp [xP]

theorem g0_inst {i : Nat} (hi : i < N) : instProcess2 (bitEnv E i) elems g0T = g0P i := by
  have hE' := hE.bind "i" (by decide) (by decide) i
  rw [g0T, instProcess2_assignL _ (ks_tgt (r := 0) hE'.hg (evalInt_int 0) (by omega) (bit_i1 E i) hi),
    fitExpr2_binary, instExpr2_and, fitExpr2_bitSel_ident hel.ha (bit_i E i) (by omega),
    fitExpr2_bitSel_ident hel.hb (bit_i E i) (by omega)]
  simp [g0P]

theorem p0_inst {i : Nat} (hi : i < N) : instProcess2 (bitEnv E i) elems p0T = p0P i := by
  have hE' := hE.bind "i" (by decide) (by decide) i
  rw [p0T, instProcess2_assignL _ (ks_tgt (r := 0) hE'.hp (evalInt_int 0) (by omega) (bit_i1 E i) hi),
    fitExpr2_binary, instExpr2_xor, fitExpr2_bitSel_ident hel.ha (bit_i E i) (by omega),
    fitExpr2_bitSel_ident hel.hb (bit_i E i) (by omega)]
  simp [p0P]

theorem s_inst {i : Nat} (hi : i ≤ N) : instProcess2 (bitEnv E i) elems sT = sP N L i := by
  have hE' := hE.bind "i" (by decide) (by decide) i
  rw [sT, instProcess2_assignL _ (instLhs2_bitSel hel.hs (bit_i E i) (by omega)), fitExpr2_binary,
    instExpr2_xor, fitExpr2_bitSel_ident hel.hx (bit_i E i) (by omega),
    ks_read hE'.hg (evalInt_paramRef_of hE'.hL) (Nat.le_refl L) (bit_i E i) hi]
  simp [sP]

end templates2

/-! ## 1e. The generate items -/

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

section expand

variable {E : IEnv} {elems : List (String × Nat)} {N L F : Nat} (hE : KsEnv E N L) (hel : KsElems elems)
include hE hel

theorem in_expand (hF : N < F) :
    inGen.expand2 E elems F = .ok ((List.range N).flatMap fun i => [xP i, g0P i, p0P i]) := by
  have hb : ∀ v : Int, KsEnv (E.bindVal "i" v) N L := fun v => hE.bind "i" (by decide) (by decide) v
  rw [inGen, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
    (fun v => isInt_paramRef_of (hb v).hN) (fun v => evalInt_paramRef_of (hb v).hN) (by simpa using hF)]
  simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast]
  congr 1
  apply flatMap_congr'
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [List.map_cons, List.map_nil]
  rw [x_inst hel, g0_inst hE hel hi', p0_inst hE hel hi']

theorem sum_expand (hF : N < F) :
    sumGen.expand2 E elems F = .ok ((List.range N).map (sP N L)) := by
  have hb : ∀ v : Int, KsEnv (E.bindVal "i" v) N L := fun v => hE.bind "i" (by decide) (by decide) v
  rw [sumGen, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
    (fun v => isInt_paramRef_of (hb v).hN) (fun v => evalInt_paramRef_of (hb v).hN) (by simpa using hF)]
  simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast]
  congr 1
  rw [List.map_eq_flatMap]
  apply flatMap_congr'
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [List.map_cons, List.map_nil]
  rw [s_inst hE hel (by omega)]

omit hel in
theorem node_expand {l i : Nat} (hl : l < L) (hi : i ≤ N) :
    expandList2 (nodeEnv E l i) elems F [nodeGen] = .ok (nodeP N l i) := by
  apply expandList2_singleton_ok
  rw [nodeGen]
  by_cases hg : 2 ^ l ≤ i
  · rw [GenItem.expand2_genIf_of_ne (node_guard E l i) (by simp [hg]), expandList2_processes]
    simp only [List.map_cons, List.map_nil, nodeP, if_pos hg]
    rw [gOp_inst hE hl hi hg, pOp_inst hE hl hi hg]
  · rw [GenItem.expand2_genIf_of_eq (by rw [node_guard E l i, if_neg hg]), expandList2_processes]
    simp only [List.map_cons, List.map_nil, nodeP, if_neg hg]
    rw [gPass_inst hE hl hi, pPass_inst hE hl hi]

omit hel in
theorem lvl_expand (hF : N + 1 < F) (hLF : L < F) :
    lvlGen.expand2 E elems F =
      .ok ((List.range L).flatMap fun l => (List.range (N + 1)).flatMap fun i => nodeP N l i) := by
  have hb : ∀ v : Int, KsEnv (E.bindVal "l" v) N L := fun v => hE.bind "l" (by decide) (by decide) v
  rw [lvlGen, GenItem.expand2_genFor_ascending_flatMap (N := (L : Int))
    (f := fun v => (List.range (N + 1)).flatMap fun i => nodeP N v.toNat i) (evalInt_int 0)
    (fun v => isInt_paramRef_of (hb v).hL) (fun v => evalInt_paramRef_of (hb v).hL) (by simpa using hLF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast]
  · intro v hv0 hvL
    obtain ⟨l, rfl⟩ : ∃ l : Nat, v = (l : Int) := ⟨v.toNat, by omega⟩
    have hl : l < L := by omega
    simp only [Int.toNat_natCast]
    apply expandList2_singleton_ok
    have hb' : ∀ w : Int, KsEnv ((E.bindVal "l" (l : Int)).bindVal "i" w) N L :=
      fun w => (hb l).bind "i" (by decide) (by decide) w
    have hN1 : ∀ w : Int, evalInt ((E.bindVal "l" (l : Int)).bindVal "i" w)
        (.binary (.m0 .add) (.paramRef "N" none) (.int 1)) = .ok ((N + 1 : Nat) : Int) := by
      intro w
      rw [evalInt_add_of (isInt_paramRef_of (hb' w).hN) rfl (evalInt_paramRef_of (hb' w).hN)
        (evalInt_int 1)]
      push_cast
      rfl
    rw [nodeLoop, GenItem.expand2_genFor_ascending_flatMap (N := ((N + 1 : Nat) : Int))
      (f := fun w => nodeP N l w.toNat) (evalInt_int 0)
      (fun w => isInt_binary_of rfl (isInt_paramRef_of (hb' w).hN) rfl) hN1 (by simpa using hF)]
    · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast]
    · intro w hw0 hwN
      obtain ⟨i, rfl⟩ : ∃ i : Nat, w = (i : Int) := ⟨w.toNat, by omega⟩
      simp only [Int.toNat_natCast]
      exact node_expand hE hl (by omega)

theorem gens_expand (hF : N + 1 < F) (hLF : L < F) :
    expandList2 E elems F [inGen, lvlGen, sumGen] = .ok (ksGens N L) :=
  expandList2_cons_ok (in_expand hE hel (by omega))
    (expandList2_cons_ok (lvl_expand hE hF hLF) (expandList2_singleton_ok (sum_expand hE hel (by omega))))

end expand

/-! ## 1f. The static processes -/

theorem ks_static {E : IEnv} {elems : List (String × Nat)} {N L : Nat} (hE : KsEnv E N L)
    (decls : List Decl) (hcin : (decls.map fun dc => (dc.name, dc.width)).lookup "cin" = some 1)
    (hcout : (decls.map fun dc => (dc.name, dc.width)).lookup "cout" = some 1) :
    design.pdesign.processes.map (instProcess2 (E.withDecls decls) elems) = [g00P, p00P, coutP N L] := by
  have hE' := hE.withDecls decls
  rw [ks_static_source]
  simp only [List.map_cons, List.map_nil]
  rw [g00T, instProcess2_assignL _ (ks_tgt (r := 0) (c := 0) hE'.hg (evalInt_int 0) (Nat.zero_le _)
      (evalInt_int 0) (Nat.zero_le _)),
    fitExpr2_ident (by simpa using hcin),
    p00T, instProcess2_assignL _ (ks_tgt (r := 0) (c := 0) hE'.hp (evalInt_int 0) (Nat.zero_le _)
      (evalInt_int 0) (Nat.zero_le _)),
    fitExpr2_lit, coutT, instProcess2_assign _ (by simpa using hcout),
    ks_read hE'.hg (evalInt_paramRef_of hE'.hL) (Nat.le_refl L) (evalInt_paramRef_of hE'.hN)
      (Nat.le_refl N)]
  simp [g00P, p00P, coutP]
  rfl

/-! ## 1g. The parameter environment, the declarations, the element widths -/

/-- `L = $clog2(N + 1)`, the number of levels. -/
def KL (N : Nat) : Nat := clog2 (N + 1)

/-- The localparam as the parameter stage binds it: the 2-state `int` squash of `$clog2(N + 1)`. -/
def ksLv (N : Nat) : Int := canonInt 32 true ((clog2 (((N : Int) + 1).toNat) : Nat) : Int)

def ksScope (N : Nat) : IEnv :=
  { vals := [("L", ksLv N), ("N", (N : Int))], pwidths := [("N", 32), ("L", 32)] }

def ksEnv (N : Nat) : IEnv := { ksScope N with dims := dimTable (ksScope N) design.pdesign.decls }

/-- The parameter stage at symbolic `N` (by `rfl`). -/
theorem ks_paramEnv (N : Nat) : design.pdesign.paramEnv2 [(N : Int)] = .ok (ksEnv N) := rfl

theorem clog2_le' (n : Nat) : clog2 n ≤ n := by
  unfold clog2
  split
  · omega
  · have := (Nat.log2_lt (n := n - 1) (k := n - 1) (by omega)).mpr Nat.lt_two_pow_self
    omega

theorem le_two_pow_clog2' (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · simp only [Nat.pow_zero]; omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

theorem KL_le31 {N : Nat} (h : N < 2 ^ 31) : KL N ≤ 31 := by
  unfold KL clog2
  split
  · omega
  · have := (Nat.log2_lt (n := N + 1 - 1) (k := 31) (by omega)).mpr (by omega)
    omega

theorem ksLv_eq {N : Nat} (h : N < 2 ^ 31) : ksLv N = (KL N : Int) := by
  have h31 := KL_le31 h
  have hc : clog2 (((N : Int) + 1).toNat) = KL N := by
    rw [KL]; congr 1
  have e1 : (2 : Int) ^ 32 = 4294967296 := by decide
  have hm : (KL N : Int).emod ((2 : Int) ^ 32) = (KL N : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  unfold ksLv canonInt
  rw [hc, hm]
  have e2 : ¬ ((2 : Int) ^ (32 - 1) ≤ (KL N : Int)) := by
    have : (2 : Int) ^ (32 - 1) = 2147483648 := by decide
    omega
  simp
  omega

/-- The instantiated declarations, for `1 ≤ N < 2^31`. -/
def ksDecls (N : Nat) : List Decl :=
  [{ name := "a", width := N, isInput := true },
   { name := "b", width := N, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := N, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "g", width := (KL N + 1) * (N + 1) },
   { name := "p", width := (KL N + 1) * (N + 1) },
   { name := "x", width := N }]

theorem ks_decls {N : Nat} (hN : 1 ≤ N) (h31 : N < 2 ^ 31) :
    buildDecls (ksEnv N) design.pdesign.decls = .ok (ksDecls N) := by
  have hv : ((N : Int) - 1).natAbs + 1 = N := by omega
  have hL : (ksLv N).natAbs = KL N := by rw [ksLv_eq h31]; rfl
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt, ksEnv,
    ksScope, List.lookup, Gen2.except_ok_bind, ksDecls, hv, hL]

def ksElemsL (N : Nat) : List (String × Nat) :=
  [("a", 1), ("b", 1), ("cin", 1), ("s", 1), ("cout", 1), ("g", N + 1), ("p", N + 1), ("x", 1)]

theorem ks_elems (N : Nat) : buildElems (ksEnv N) design.pdesign.decls = .ok (ksElemsL N) := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, ksEnv, ksScope,
    List.lookup, ksElemsL, Gen2.except_ok_bind, Gen2.except_pure, PType.elemWidth]

theorem ksElemsOk (N : Nat) : KsElems (ksElemsL N) :=
  ⟨by simp [ksElemsL], by simp [ksElemsL, List.lookup], by simp [ksElemsL, List.lookup],
    by simp [ksElemsL, List.lookup]⟩

theorem ksEnvOk {N : Nat} (h31 : N < 2 ^ 31) : KsEnv (ksEnv N) N (KL N) where
  hN := by simp [ksEnv, ksScope, List.lookup]
  hL := by simp [ksEnv, ksScope, ksLv_eq h31]
  hg := PDesign.dimTable_lookup_of (env := ksScope N)
    (rfl : design.pdesign.packedDims.lookup "g" =
      some [{ msb := .paramRef "L" none, lsb := .int 0 }, { msb := .paramRef "N" none, lsb := .int 0 }])
    (fun ws => evalDims_cons_of (evalInt_paramRef_of (by simp [ksScope, ksLv_eq h31])) (evalInt_int 0)
      (evalDims_cons_of (evalInt_paramRef_of (by simp [ksScope, List.lookup])) (evalInt_int 0) evalDims_nil))
  hp := PDesign.dimTable_lookup_of (env := ksScope N)
    (rfl : design.pdesign.packedDims.lookup "p" =
      some [{ msb := .paramRef "L" none, lsb := .int 0 }, { msb := .paramRef "N" none, lsb := .int 0 }])
    (fun ws => evalDims_cons_of (evalInt_paramRef_of (by simp [ksScope, ksLv_eq h31])) (evalInt_int 0)
      (evalDims_cons_of (evalInt_paramRef_of (by simp [ksScope, List.lookup])) (evalInt_int 0) evalDims_nil))

/-! ## 1h. `instantiate2` at symbolic `N` -/

/-- The instantiated design. -/
def ksM (N : Nat) : Design2 :=
  design.pdesign.assemble2 (ksEnv N) (ksDecls N) (ksElemsL N) (ksGens N (KL N))

theorem ks_instantiate2 {N : Nat} (hN : 1 ≤ N) (h31 : N < 2 ^ 31) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) = .ok (ksM N) := by
  have hF1 : N + 1 < PDesign.surfaceFuel [(N : Int)] := by
    have := Nat.le_mul_self (N + 2)
    simp [PDesign.surfaceFuel]
    omega
  have hF2 : KL N < PDesign.surfaceFuel [(N : Int)] := by
    have := KL_le31 h31
    simp [PDesign.surfaceFuel]
    omega
  exact PDesign.instantiate2_of_ok rfl (ks_paramEnv N) (ks_decls hN h31) (ks_elems N)
    (by rw [ks_generates]; exact gens_expand ((ksEnvOk h31).withDecls _) (ksElemsOk N) hF1 hF2)

/-- The process list, in `instantiate2`'s order. -/
def ksProcs (N : Nat) : List Process2 := [g00P, p00P, coutP N (KL N)] ++ ksGens N (KL N)

theorem ksM_processes {N : Nat} (h31 : N < 2 ^ 31) : (ksM N).processes.toList = ksProcs N := by
  rw [ksM, PDesign.assemble2_processes,
    ks_static (ksEnvOk h31) (ksDecls N) (by simp [ksDecls, List.lookup])
      (by simp [ksDecls, List.lookup]), ks_others]
  simp [ksProcs]

theorem ksM_decls (N : Nat) : (ksM N).decls.toList = ksDecls N := PDesign.assemble2_decls ..

/-! # Part 2. The comb profile and acyclicity

## 2a. Every process, by kind -/

theorem mem_nodeP {N l i : Nat} {p : Process2} (h : p ∈ nodeP N l i) :
    (2 ^ l ≤ i ∧ (p = gOpP N l i ∨ p = pOpP N l i)) ∨
      (i < 2 ^ l ∧ (p = gPassP N l i ∨ p = pPassP N l i)) := by
  unfold nodeP at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact Or.inl ⟨by assumption, h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact Or.inr ⟨by omega, h⟩

/-- **Every process of the adder**, by kind. -/
theorem ksProcs_forall {N : Nat} {P : Process2 → Prop}
    (h1 : P g00P) (h2 : P p00P) (h3 : P (coutP N (KL N)))
    (hx : ∀ i, i < N → P (xP i)) (hg0 : ∀ i, i < N → P (g0P i)) (hp0 : ∀ i, i < N → P (p0P i))
    (hgo : ∀ l i, l < KL N → i ≤ N → 2 ^ l ≤ i → P (gOpP N l i))
    (hpo : ∀ l i, l < KL N → i ≤ N → 2 ^ l ≤ i → P (pOpP N l i))
    (hgp : ∀ l i, l < KL N → i ≤ N → i < 2 ^ l → P (gPassP N l i))
    (hpp : ∀ l i, l < KL N → i ≤ N → i < 2 ^ l → P (pPassP N l i))
    (hs : ∀ i, i < N → P (sP N (KL N) i)) :
    ∀ p ∈ ksProcs N, P p := by
  intro p hp
  simp only [ksProcs, ksGens, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.mem_map, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl) | ⟨i, hi, rfl | rfl | rfl⟩ | ⟨l, hl, i, hi, hm⟩ | ⟨i, hi, rfl⟩
  · exact h1
  · exact h2
  · exact h3
  · exact hx i hi
  · exact hg0 i hi
  · exact hp0 i hi
  · rcases mem_nodeP hm with ⟨hg, rfl | rfl⟩ | ⟨hg, rfl | rfl⟩
    · exact hgo l i hl (by omega) hg
    · exact hpo l i hl (by omega) hg
    · exact hgp l i hl (by omega) hg
    · exact hpp l i hl (by omega) hg
  · exact hs i hi

/-- The write window of a process (`cout` is the whole one-bit signal). -/
def winOf : Process2 → Win
  | .assign (.slice n lo w) _ => (n, lo, w)
  | .assign (.ident n) _ => (n, 0, 1)
  | _ => ("", 0, 0)

/-- The right-hand side of an assign. -/
def rhsOf : Process2 → Expr2
  | .assign _ e => e
  | _ => .lit ⟨#[]⟩

/-- Every process is an assign to a one-bit slice of `g`, `p`, `x` or `s`, or to the whole `cout`. -/
theorem ksProcs_shape {N : Nat} : ∀ p ∈ ksProcs N,
    (∃ n lo e, p = .assign (.slice n lo 1) e ∧ n ∈ ["g", "p", "x", "s"]) ∨
      ∃ e, p = .assign (.ident "cout") e := by
  refine ksProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    first | exact Or.inl ⟨_, _, _, rfl, by decide⟩ | exact Or.inr ⟨_, rfl⟩

/-! ## 2b. Declarations of the instantiated design -/

theorem ksM_declWidth (N : Nat) (n : String) :
    (ksM N).declWidth n = ((ksDecls N).find? fun dc => dc.name == n).map Decl.width := by
  simp only [Design2.declWidth, ksM_decls]

theorem ksM_declWidth_cout (N : Nat) : (ksM N).declWidth "cout" = some 1 := by
  simp [ksM_declWidth, ksDecls]
theorem ksM_declWidth_g (N : Nat) : (ksM N).declWidth "g" = some ((KL N + 1) * (N + 1)) := by
  simp [ksM_declWidth, ksDecls]
theorem ksM_declWidth_p (N : Nat) : (ksM N).declWidth "p" = some ((KL N + 1) * (N + 1)) := by
  simp [ksM_declWidth, ksDecls]
theorem ksM_declWidth_x (N : Nat) : (ksM N).declWidth "x" = some N := by
  simp [ksM_declWidth, ksDecls]
theorem ksM_declWidth_s (N : Nat) : (ksM N).declWidth "s" = some N := by
  simp [ksM_declWidth, ksDecls]

theorem ksM_inputNames (N : Nat) : (ksM N).inputNames.toList = ["a", "b", "cin"] := by
  simp [Design2.inputNames, ksM_decls, ksDecls]

/-- The target of every process has exactly its `winOf` window. -/
theorem ksProcs_wins {N : Nat} : ∀ p ∈ ksProcs N, ∀ t e, p = .assign t e →
    t.windows? (ksM N) = some [winOf p] ∧ t.wins (ksM N) = [winOf p] := by
  intro p hp t e hpe
  rcases ksProcs_shape p hp with ⟨n, lo, e', rfl, -⟩ | ⟨e', rfl⟩
  · simp only [Process2.assign.injEq] at hpe
    obtain ⟨rfl, -⟩ := hpe
    exact ⟨rfl, by simp [winOf]⟩
  · simp only [Process2.assign.injEq] at hpe
    obtain ⟨rfl, -⟩ := hpe
    have hw : (Lhs2.ident "cout").window? (ksM N) = some ("cout", 0, 1) := by
      simp [Lhs2.window?, ksM_declWidth_cout]
    exact ⟨Lhs2.windows?_of_window? hw, Lhs2.wins_of_window? hw⟩

/-! ## 2c. The window list, and one driver per bit -/

def wsS : List Win := [("g", 0, 1), ("p", 0, 1), ("cout", 0, 1)]
def wsA (N : Nat) : List Win :=
  (List.range N).flatMap fun i => [("x", i, 1), ("g", i + 1, 1), ("p", i + 1, 1)]
def wsNode (N l i : Nat) : List Win :=
  [("g", (l + 1) * (N + 1) + i, 1), ("p", (l + 1) * (N + 1) + i, 1)]
def wsB (N K : Nat) : List Win := (List.range K).flatMap fun l => (List.range (N + 1)).flatMap (wsNode N l)
def wsC (N : Nat) : List Win := (List.range N).map fun i => ("s", i, 1)

theorem nodeP_winOf (N l i : Nat) : (nodeP N l i).map winOf = wsNode N l i := by
  unfold nodeP
  split <;> rfl

theorem ksProcs_winOf (N : Nat) : (ksProcs N).map winOf = wsS ++ (wsA N ++ (wsB N (KL N) ++ wsC N)) := by
  simp only [ksProcs, ksGens, List.map_append, List.map_cons, List.map_nil, List.map_flatMap,
    nodeP_winOf, List.map_map]
  rfl

theorem mem_wsA {N : Nat} {w : Win} : w ∈ wsA N ↔
    ∃ i, i < N ∧ (w = ("x", i, 1) ∨ w = ("g", i + 1, 1) ∨ w = ("p", i + 1, 1)) := by
  simp [wsA]

theorem mem_wsB {N K : Nat} {w : Win} : w ∈ wsB N K ↔
    ∃ l, l < K ∧ ∃ i, i < N + 1 ∧
      (w = ("g", (l + 1) * (N + 1) + i, 1) ∨ w = ("p", (l + 1) * (N + 1) + i, 1)) := by
  simp [wsB, wsNode]

theorem mem_wsC {N : Nat} {w : Win} : w ∈ wsC N ↔ ∃ i, i < N ∧ w = ("s", i, 1) := by
  simp [wsC, eq_comm]

/-- Row-major offsets: row `l` ends where a later row can begin. -/
theorem rowMajor_le' {K i i' : Nat} (h : i < i') : i * K + K ≤ i' * K := by
  have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt h)
  rwa [Nat.succ_mul] at this

/-- A level row starts at or after `N + 1`. -/
theorem row_ge (N l : Nat) : N + 1 ≤ (l + 1) * (N + 1) := by
  have := Nat.mul_le_mul_right (N + 1) (Nat.succ_le_succ (Nat.zero_le l))
  simpa using this

macro "ov_close" : tactic =>
  `(tactic| (rw [Win.overlaps_eq_false]; first | (left; decide) | (right; left; omega) | (right; right; omega)))

theorem wsB_pairwise (N K : Nat) : (wsB N K).Pairwise fun a b => Win.overlaps a b = false := by
  apply pairwise_flatMap_range
  · intro l _
    apply pairwise_flatMap_range
    · intro i _
      simp [wsNode, Win.overlaps_eq_false]
    · intro i i' hii' _ a ha b hb
      simp only [wsNode, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> ov_close
  · intro l l' hll' _ a ha b hb
    simp only [List.mem_flatMap, List.mem_range, wsNode, List.mem_cons, List.not_mem_nil,
      or_false] at ha hb
    obtain ⟨i, hi, ha⟩ := ha
    obtain ⟨i', hi', hb⟩ := hb
    have hr := rowMajor_le' (K := N + 1) (show l + 1 < l' + 1 by omega)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> ov_close

theorem ws_pairwise (N K : Nat) :
    (wsS ++ (wsA N ++ (wsB N K ++ wsC N))).Pairwise fun a b => Win.overlaps a b = false := by
  simp only [List.pairwise_append]
  refine ⟨?_, ⟨?_, ⟨wsB_pairwise N K, ?_, ?_⟩, ?_⟩, ?_⟩
  · simp [wsS, Win.overlaps_eq_false]
  · apply pairwise_flatMap_range
    · intro i _
      simp [Win.overlaps_eq_false]
    · intro i i' hii' _ a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> ov_close
  · -- `wsC` pairwise
    simp only [wsC]
    rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun {i j} _ _ hij => by ov_close) List.pairwise_lt_range
  · intro a ha b hb
    obtain ⟨l, -, i, -, rfl | rfl⟩ := mem_wsB.mp ha <;> obtain ⟨j, -, rfl⟩ := mem_wsC.mp hb <;> ov_close
  · intro a ha b hb
    obtain ⟨i, hi, rfl | rfl | rfl⟩ := mem_wsA.mp ha <;>
    simp only [List.mem_append] at hb <;>
    rcases hb with hb | hb <;>
    first
      | (obtain ⟨l, -, j, -, rfl | rfl⟩ := mem_wsB.mp hb <;>
          (have := row_ge N l; ov_close))
      | (obtain ⟨j, -, rfl⟩ := mem_wsC.mp hb; ov_close)
  · intro a ha b hb
    simp only [wsS, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb
    · obtain ⟨i, -, rfl | rfl | rfl⟩ := mem_wsA.mp hb <;> rcases ha with rfl | rfl | rfl <;> ov_close
    · obtain ⟨l, -, j, -, rfl | rfl⟩ := mem_wsB.mp hb <;> rcases ha with rfl | rfl | rfl <;>
        (have := row_ge N l; ov_close)
    · obtain ⟨j, -, rfl⟩ := mem_wsC.mp hb <;> rcases ha with rfl | rfl | rfl <;> ov_close

/-! ## 2d. The comb profile of the instantiated design -/

section comb

variable {N : Nat} (h31 : N < 2 ^ 31)
include h31

theorem ksM_getElem?_of_mem {p : Process2} (h : p ∈ ksProcs N) :
    ∃ k : Nat, (ksM N).processes[k]? = some p := by
  rw [← ksM_processes h31, List.mem_iff_getElem?] at h
  obtain ⟨k, hk⟩ := h
  rw [Array.getElem?_toList] at hk
  exact ⟨k, hk⟩

theorem ksM_mem_of_getElem? {k : Nat} {p : Process2} (h : (ksM N).processes[k]? = some p) :
    p ∈ ksProcs N := by
  rw [← ksM_processes h31, List.mem_iff_getElem?]
  exact ⟨k, by rw [Array.getElem?_toList]; exact h⟩

omit h31 in
/-- Every window is a one-bit window of a driven signal. -/
theorem ksProcs_winForm : ∀ p ∈ ksProcs N,
    ∃ n lo, winOf p = (n, lo, 1) ∧ n ∈ ["g", "p", "x", "s", "cout"] := by
  intro p hp
  rcases ksProcs_shape p hp with ⟨n, lo, e, rfl, hn⟩ | ⟨e, rfl⟩
  · refine ⟨n, lo, rfl, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    rcases hn with rfl | rfl | rfl | rfl <;> simp
  · exact ⟨"cout", 0, rfl, by simp⟩

/-- What process `j` writes: exactly its `winOf` window. -/
theorem ksM_writes {j : Nat} {w : Win} (h : (ksM N).Writes j w) :
    ∃ p, (ksM N).processes[j]? = some p ∧ p ∈ ksProcs N ∧ w = winOf p := by
  obtain ⟨t, e, hp, hw⟩ := h
  have hm := ksM_mem_of_getElem? h31 hp
  obtain ⟨-, hws⟩ := ksProcs_wins _ hm t e rfl
  rw [hws, List.mem_singleton] at hw
  exact ⟨_, hp, hm, hw⟩

omit h31 in
theorem ksProcs_pairwise :
    (ksProcs N).Pairwise fun p q => Win.overlaps (winOf p) (winOf q) = false := by
  have h := ws_pairwise N (KL N)
  rw [← ksProcs_winOf, List.pairwise_map] at h
  exact h

theorem ksM_disjoint : ∀ i j wi wj, i ≠ j → (ksM N).Writes i wi → (ksM N).Writes j wj →
    Win.overlaps wi wj = false := by
  intro i j wi wj hij hi hj
  obtain ⟨p, hp, -, rfl⟩ := ksM_writes h31 hi
  obtain ⟨q, hq, -, rfl⟩ := ksM_writes h31 hj
  have hpw := ksProcs_pairwise (N := N)
  rw [← ksM_processes h31, List.pairwise_iff_getElem] at hpw
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

omit h31 in
theorem ksProcs_inWidth : ∀ p ∈ ksProcs N,
    ∃ dw, (ksM N).declWidth (winOf p).1 = some dw ∧ (winOf p).2.1 + (winOf p).2.2 ≤ dw := by
  have hK : N + 1 ≤ (KL N + 1) * (N + 1) := row_ge N (KL N)
  refine ksProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨_, ksM_declWidth_g N, by simp [winOf, g00P]; omega⟩
  · exact ⟨_, ksM_declWidth_p N, by simp [winOf, p00P]; omega⟩
  · exact ⟨_, ksM_declWidth_cout N, by simp [winOf, coutP]⟩
  · intro i hi; exact ⟨_, ksM_declWidth_x N, by simp [winOf, xP]; omega⟩
  · intro i hi; exact ⟨_, ksM_declWidth_g N, by simp [winOf, g0P]; omega⟩
  · intro i hi; exact ⟨_, ksM_declWidth_p N, by simp [winOf, p0P]; omega⟩
  · intro l i hl hi _
    have := rowMajor_le' (K := N + 1) (show l + 1 < KL N + 1 by omega)
    exact ⟨_, ksM_declWidth_g N, by simp [winOf, gOpP]; omega⟩
  · intro l i hl hi _
    have := rowMajor_le' (K := N + 1) (show l + 1 < KL N + 1 by omega)
    exact ⟨_, ksM_declWidth_p N, by simp [winOf, pOpP]; omega⟩
  · intro l i hl hi _
    have := rowMajor_le' (K := N + 1) (show l + 1 < KL N + 1 by omega)
    exact ⟨_, ksM_declWidth_g N, by simp [winOf, gPassP]; omega⟩
  · intro l i hl hi _
    have := rowMajor_le' (K := N + 1) (show l + 1 < KL N + 1 by omega)
    exact ⟨_, ksM_declWidth_p N, by simp [winOf, pPassP]; omega⟩
  · intro i hi; exact ⟨_, ksM_declWidth_s N, by simp [winOf, sP]; omega⟩

omit h31 in
theorem ksProcs_rhsFree : ∀ p ∈ ksProcs N, (rhsOf p).unsupportedFree = true := by
  refine ksProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

/-- Every declared name. -/
def ksNames : List String := ["a", "b", "cin", "s", "cout", "g", "p", "x"]

omit h31 in
theorem ksProcs_rhsDeclared : ∀ p ∈ ksProcs N, ((rhsOf p).idents.all fun x => x ∈ ksNames) = true := by
  refine ksProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

theorem ksM_comb : CombDesign (ksM N) where
  nodup := by
    rw [ksM_decls]
    simp only [ksDecls, List.map_cons, List.map_nil]
    decide
  assign := by
    intro j p hp
    have hm := ksM_mem_of_getElem? h31 hp
    rcases ksProcs_shape p hm with ⟨n, lo, e, rfl, -⟩ | ⟨e, rfl⟩
    · exact ⟨_, _, _, rfl, (ksProcs_wins _ hm _ _ rfl).1⟩
    · exact ⟨_, _, _, rfl, (ksProcs_wins _ hm _ _ rfl).1⟩
  inWidth := by
    intro j n lo w h
    obtain ⟨p, -, hm, hw⟩ := ksM_writes h31 h
    obtain ⟨dw, hdw, hle⟩ := ksProcs_inWidth p hm
    rw [← hw] at hdw hle
    exact ⟨dw, hdw, hle⟩
  notInput := by
    rintro n ⟨j, lo, w, h⟩
    obtain ⟨p, -, hm, hw⟩ := ksM_writes h31 h
    obtain ⟨n', lo', hwf, hn'⟩ := ksProcs_winForm p hm
    rw [hwf] at hw
    simp only [Prod.mk.injEq] at hw
    obtain ⟨rfl, -, -⟩ := hw
    rw [ksM_inputNames]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn' ⊢
    rcases hn' with rfl | rfl | rfl | rfl | rfl <;> decide
  disjoint := ksM_disjoint h31
  selfDisjoint := by
    intro j t e hp
    rcases ksProcs_shape _ (ksM_mem_of_getElem? h31 hp) with ⟨n, lo, e', h, -⟩ | ⟨e', h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
      exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro j t e hp
    exact ksProcs_rhsFree _ (ksM_mem_of_getElem? h31 hp)
  rhsDeclared := by
    intro j t e hp x hx
    have h := List.all_eq_true.mp (ksProcs_rhsDeclared _ (ksM_mem_of_getElem? h31 hp)) x hx
    rw [ksM_decls]
    simpa [ksNames, ksDecls] using h
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [ksM_decls] at hdc
    simp [ksDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [ksM_decls] at hdc
    simp [ksDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end comb

/-! ## 2e. Acyclicity: the level is the rank -/

/-- The rank of a written window: a pair of level `l` (offset `l * (N + 1) + k`) ranks `l + 1`, `x` ranks `0`,
the sum and the carry out rank `K + 2`. -/
def rkW (N K : Nat) (w : Win) : Nat :=
  if w.1 = "g" ∨ w.1 = "p" then w.2.1 / (N + 1) + 1 else if w.1 = "x" then 0 else K + 2

/-- The rank certificate: the rank of the process's write window. -/
def ksRank (N : Nat) (k : Nat) : Nat :=
  match (ksM N).processes[k]? with
  | some p => rkW N (KL N) (winOf p)
  | none => 0

theorem rowdiv {M l i : Nat} (hi : i < M) : (l * M + i) / M = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < M), Nat.div_eq_of_lt hi, Nat.zero_add]

/-- A one-bit read of a signal outside the driven list overlaps no driven window. -/
theorem read_undriven {n n' : String} {k lo : Nat} (hn' : n' ∈ ["g", "p", "x", "s", "cout"])
    (hn : n ∉ ["g", "p", "x", "s", "cout"]) : (ReadWin.win n k 1).overlaps (n', lo, 1) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [ReadWin.overlaps_win_one] at h
  obtain ⟨rfl, -, -⟩ := h
  exact hn hn'

/-- A one-bit read that overlaps a one-bit window is that window. -/
theorem read_hit {n n' : String} {k lo : Nat} (h : (ReadWin.win n k 1).overlaps (n', lo, 1) = true) :
    n' = n ∧ lo = k := by
  rw [ReadWin.overlaps_win_one] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, by omega⟩

macro "rd_undriven" : tactic =>
  `(tactic| (rw [read_undriven (by assumption) (by decide)] at *; contradiction))

/-- **Every read is of a strictly lower rank** (reader by reader). -/
theorem ksProcs_reads {N : Nat} : ∀ p ∈ ksProcs N, ∀ r ∈ (rhsOf p).reads, ∀ n' lo',
    n' ∈ ["g", "p", "x", "s", "cout"] → r.overlaps (n', lo', 1) = true →
      rkW N (KL N) (n', lo', 1) < rkW N (KL N) (winOf p) := by
  refine ksProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr n' lo' hn' hov
    simp [rhsOf, g00P, Expr2.reads] at hr
    subst hr
    simp only [ReadWin.overlaps, beq_iff_eq] at hov
    subst hov
    simp at hn'
  · intro r hr
    simp [rhsOf, p00P, Expr2.reads] at hr
  · intro r hr n' lo' hn' hov
    simp [rhsOf, coutP, Expr2.reads, Expr2.sliceReads] at hr
    subst hr
    obtain ⟨rfl, rfl⟩ := read_hit hov
    simp [rkW, winOf, coutP, rowdiv (show N < N + 1 by omega)]
  · intro i _ r hr n' lo' hn' hov
    simp [rhsOf, xP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;> rd_undriven
  · intro i _ r hr n' lo' hn' hov
    simp [rhsOf, g0P, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;> rd_undriven
  · intro i _ r hr n' lo' hn' hov
    simp [rhsOf, p0P, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;> rd_undriven
  · intro l i hl hi hg r hr n' lo' hn' hov
    simp [rhsOf, gOpP, Expr2.reads, Expr2.sliceReads] at hr
    have h1 := rowdiv (M := N + 1) (l := l + 1) (show i < N + 1 by omega)
    rcases hr with rfl | rfl | rfl <;> obtain ⟨rfl, rfl⟩ := read_hit hov <;>
      simp [rkW, winOf, gOpP, h1, rowdiv (M := N + 1) (l := l) (show i < N + 1 by omega),
        rowdiv (M := N + 1) (l := l) (Nat.lt_succ_of_le (Nat.le_trans (Nat.sub_le i (2 ^ l)) hi))]
  · intro l i hl hi hg r hr n' lo' hn' hov
    simp [rhsOf, pOpP, Expr2.reads, Expr2.sliceReads] at hr
    have h1 := rowdiv (M := N + 1) (l := l + 1) (show i < N + 1 by omega)
    rcases hr with rfl | rfl <;> obtain ⟨rfl, rfl⟩ := read_hit hov <;>
      simp [rkW, winOf, pOpP, h1, rowdiv (M := N + 1) (l := l) (show i < N + 1 by omega),
        rowdiv (M := N + 1) (l := l) (Nat.lt_succ_of_le (Nat.le_trans (Nat.sub_le i (2 ^ l)) hi))]
  · intro l i hl hi hg r hr n' lo' hn' hov
    simp [rhsOf, gPassP, Expr2.reads, Expr2.sliceReads] at hr
    have h1 := rowdiv (M := N + 1) (l := l + 1) (show i < N + 1 by omega)
    subst hr
    obtain ⟨rfl, rfl⟩ := read_hit hov
    simp [rkW, winOf, gPassP, h1, rowdiv (M := N + 1) (l := l) (show i < N + 1 by omega)]
  · intro l i hl hi hg r hr n' lo' hn' hov
    simp [rhsOf, pPassP, Expr2.reads, Expr2.sliceReads] at hr
    have h1 := rowdiv (M := N + 1) (l := l + 1) (show i < N + 1 by omega)
    subst hr
    obtain ⟨rfl, rfl⟩ := read_hit hov
    simp [rkW, winOf, pPassP, h1, rowdiv (M := N + 1) (l := l) (show i < N + 1 by omega)]
  · intro i hi r hr n' lo' hn' hov
    simp [rhsOf, sP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;> obtain ⟨rfl, rfl⟩ := read_hit hov
    · simp [rkW, winOf, sP]
    · simp [rkW, winOf, sP, rowdiv (M := N + 1) (l := KL N) (show i < N + 1 by omega)]

theorem ksM_acyclic {N : Nat} (h31 : N < 2 ^ 31) : Acyclic (ksM N) := by
  refine ⟨ksRank N, ?_⟩
  intro i j ti ei tj ej wj hi hj hwj ⟨r, hr, hov⟩
  have hmi := ksM_mem_of_getElem? h31 hi
  have hmj := ksM_mem_of_getElem? h31 hj
  obtain ⟨-, hws⟩ := ksProcs_wins _ hmj tj ej rfl
  rw [hws, List.mem_singleton] at hwj
  subst hwj
  obtain ⟨n', lo', hwf, hn'⟩ := ksProcs_winForm _ hmj
  have hlt := ksProcs_reads _ hmi r hr n' lo' hn' (by rw [← hwf]; exact hov)
  rw [← hwf] at hlt
  simp only [ksRank, hi, hj]
  exact hlt

/-! ## 2f. `design.sem N` is the instantiated design -/

theorem ks_sem_eq {N : Nat} (hN : 1 ≤ N) (h31 : N < 2 ^ 31) : design.sem N = ksM N := by
  show design.pdesign.instantiateGD2 [(N : Int)] = ksM N
  refine PDesign.instantiateGD2_of_combDesign (ks_instantiate2 hN h31) (ksM_comb h31) ?_
  intro i n lo w h
  obtain ⟨p, -, hm, hw⟩ := ksM_writes h31 h
  obtain ⟨n', lo', hwf, -⟩ := ksProcs_winForm p hm
  rw [hwf] at hw
  simp only [Prod.mk.injEq] at hw
  obtain ⟨-, -, rfl⟩ := hw
  exact Nat.one_pos

/-! # Part 3. The arithmetic, the settled state and the statement

## 3a. The Kogge-Stone recurrence and its block invariant (plain `Bool`/`Nat`) -/

section KsCore

open LeanModels.Sv.Lib

/-- **The Kogge-Stone recurrence**, as the source denotes it: level `0` is the positions `pos`; level `l + 1`
at position `k` combines `(l, k)` with `(l, k - 2^l)` when `k ≥ 2^l`, and is `(l, k)` otherwise. -/
def ksRec (pos : Nat → Bool × Bool) : Nat → Nat → Bool × Bool
  | 0, k => pos k
  | l + 1, k => if 2 ^ l ≤ k then pgOp (ksRec pos l k) (ksRec pos l (k - 2 ^ l)) else ksRec pos l k

theorem ksRec_zero (pos : Nat → Bool × Bool) (k : Nat) : ksRec pos 0 k = pos k := rfl

theorem ksRec_succ (pos : Nat → Bool × Bool) (l k : Nat) :
    ksRec pos (l + 1) k =
      if 2 ^ l ≤ k then pgOp (ksRec pos l k) (ksRec pos l (k - 2 ^ l)) else ksRec pos l k := rfl

/-- **The block invariant.** After level `l`, position `k` holds the pair of the block of the last
`min (2^l) (k + 1)` positions ending at `k`: the block `[k + 1 - 2^l, k]` (natural subtraction). -/
theorem ksRec_block (pos : Nat → Bool × Bool) : ∀ l k, ksRec pos l k = pgBlock pos (k + 1 - 2 ^ l) k
  | 0, k => by rw [ksRec_zero, Nat.pow_zero, Nat.add_sub_cancel, pgBlock_self]
  | l + 1, k => by
    rw [ksRec_succ]
    have hP : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases h : 2 ^ l ≤ k
    · rw [if_pos h, ksRec_block pos l k, ksRec_block pos l (k - 2 ^ l), hP]
      generalize 2 ^ l = P at *
      have hc := pgBlock_combine pos (j := k + 1 - 2 * P) (m := k - P) (k := k) (by omega) (by omega)
      rw [show k - P + 1 = k + 1 - P by omega] at hc
      rw [show k - P + 1 - P = k + 1 - 2 * P by omega]
      exact hc
    · rw [if_neg h, ksRec_block pos l k, hP]
      generalize 2 ^ l = P at *
      rw [show k + 1 - P = 0 by omega, show k + 1 - 2 * P = 0 by omega]

/-- Once `k < 2^L`, position `k` holds the carry into bit `k` (and propagates nothing). -/
theorem ks_carry (a b : Nat → Bool) (cin : Bool) {L k : Nat} (hk : k < 2 ^ L) :
    ksRec (addPos a b cin) L k = (rippleCarry a b cin k, false) := by
  rw [ksRec_block]
  generalize hP : 2 ^ L = P at hk
  rw [show k + 1 - P = 0 by omega, pgBlock_addPos_zero]

end KsCore

/-! ## 3b. Gate algebra on known one-bit values -/

section Gates

variable {st : SvState}

theorem eval_bit {n : String} {w : Nat} {x : BitVec w} {i : Nat}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) (hi : i < w) :
    evalPure2 st (.slice (.ident n) i 1) = .ok (LVec.ofBitVec (BitVec.ofBool (x.getLsbD i))) :=
  evalPure2_bit_ofBitVec (evalPure2_ident_ofBitVec h) hi

theorem eval_win {n : String} {u : LVec} {k : Nat} {b : Bool}
    (h : SvState.lookup st n = some u) (hk : u.extract k 1 = LVec.ofBitVec (BitVec.ofBool b)) :
    evalPure2 st (.slice (.ident n) k 1) = .ok (LVec.ofBitVec (BitVec.ofBool b)) := by
  simp only [evalPure2_slice, evalPure2_ident_of_lookup h, Pure2.res_ok_bind, Pure2.res_pure_eq, hk]

theorem eval_lit0 : evalPure2 st (.lit lit0) = .ok (LVec.ofBitVec (BitVec.ofBool false)) := by
  simp only [evalPure2_lit]
  rfl

theorem eval_and2 {l r : Expr2} {p q : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool q))) :
    evalPure2 st (.binary .and l r) = .ok (LVec.ofBitVec (BitVec.ofBool (p && q))) := by
  rw [evalPure2_and_ofBitVec hl hr, BitVec.ofBool_and_ofBool]

theorem eval_xor2 {l r : Expr2} {p q : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool q))) :
    evalPure2 st (.binary .xor l r) = .ok (LVec.ofBitVec (BitVec.ofBool (p ^^ q))) := by
  rw [evalPure2_xor_ofBitVec hl hr, BitVec.ofBool_xor_ofBool]

theorem eval_or_and {l m r : Expr2} {p q b : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hm : evalPure2 st m = .ok (LVec.ofBitVec (BitVec.ofBool q)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    evalPure2 st (.binary .or l (.binary .and m r)) =
      .ok (LVec.ofBitVec (BitVec.ofBool (p || (q && b)))) := by
  rw [evalPure2_or_ofBitVec hl (evalPure2_and_ofBitVec hm hr), BitVec.ofBool_and_ofBool,
    BitVec.ofBool_or_ofBool]

end Gates

/-- A one-bit slice assign, read back on a state solving the equations. -/
theorem readback1 {d : Design2} {st : SvState} (heqs : CombEqs d st) {k : Nat} {n : String}
    {lo : Nat} {e : Expr2} (hk : d.processes[k]? = some (.assign (.slice n lo 1) e))
    {u : LVec} (hu : SvState.lookup st n = some u) {b : Bool}
    (he : evalPure2 st e = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    u.extract lo 1 = LVec.ofBitVec (BitVec.ofBool b) := by
  obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs hk he
  rw [hu, Option.some.injEq] at hold
  subst hold
  rw [hext, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

/-! ## 3c. Membership of each cell -/

section Mem

variable {N : Nat}

theorem mem_g00P : g00P ∈ ksProcs N := by simp [ksProcs]
theorem mem_p00P : p00P ∈ ksProcs N := by simp [ksProcs]
theorem mem_coutP : coutP N (KL N) ∈ ksProcs N := by simp [ksProcs]

theorem mem_inCell {i : Nat} (hi : i < N) {p : Process2} (hp : p ∈ [xP i, g0P i, p0P i]) :
    p ∈ ksProcs N :=
  List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hp⟩))

theorem mem_node {l i : Nat} (hl : l < KL N) (hi : i ≤ N) {p : Process2} (hp : p ∈ nodeP N l i) :
    p ∈ ksProcs N :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl,
      List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (by omega), hp⟩⟩)))

theorem mem_sP {i : Nat} (hi : i < N) : sP N (KL N) i ∈ ksProcs N :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))

end Mem

/-! ## 3d. The settled state -/

open LeanModels.Sv.Lib in
/-- **The Kogge-Stone adder, one settled state.** In any state that solves the design's equations and has the
comb shape, known inputs `x y : BitVec N`, `ci : Bool` on `a b cin` give `x + y + ci` (mod `2^N`) on `s` and the
carry out `2^N ≤ x + y + ci` on `cout`. -/
theorem ks_settled {N : Nat} (hN : 1 ≤ N) (h31 : N < 2 ^ 31) {st : SvState}
    (heqs : CombEqs (ksM N) st) (hs : StateShape (ksM N) st)
    {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
      SvState.lookup st "cout" =
        some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  obtain ⟨jg, hjg⟩ := ksM_getElem?_of_mem h31 (mem_g00P (N := N))
  obtain ⟨jp, hjp⟩ := ksM_getElem?_of_mem h31 (mem_p00P (N := N))
  obtain ⟨jx, hjx⟩ := ksM_getElem?_of_mem h31 (mem_inCell (N := N) (i := 0) hN (p := xP 0) (by simp))
  obtain ⟨ug, hug, -⟩ := hs.driven "g" ⟨jg, _, _, Design2.writes_of_window? hjg rfl⟩
  obtain ⟨up, hup, -⟩ := hs.driven "p" ⟨jp, _, _, Design2.writes_of_window? hjp rfl⟩
  obtain ⟨ux, hux, -⟩ := hs.driven "x" ⟨jx, _, _, Design2.writes_of_window? hjx rfl⟩
  -- the levels, by induction: every pair holds the recurrence
  have hlev : ∀ l, l ≤ KL N → ∀ k, k ≤ N →
      ug.extract (l * (N + 1) + k) 1 =
          LVec.ofBitVec (BitVec.ofBool (ksRec (addPos x.getLsbD y.getLsbD ci) l k).1) ∧
        up.extract (l * (N + 1) + k) 1 =
          LVec.ofBitVec (BitVec.ofBool (ksRec (addPos x.getLsbD y.getLsbD ci) l k).2) := by
    intro l
    induction l with
    | zero =>
      intro _ k hk
      rw [Nat.zero_mul, Nat.zero_add]
      rcases k with _ | i
      · exact ⟨readback1 heqs hjg hug (evalPure2_ident_ofBitVec hc),
          readback1 heqs hjp hup eval_lit0⟩
      · obtain ⟨j1, hj1⟩ := ksM_getElem?_of_mem h31 (mem_inCell (i := i) (by omega) (p := g0P i) (by simp))
        obtain ⟨j2, hj2⟩ := ksM_getElem?_of_mem h31 (mem_inCell (i := i) (by omega) (p := p0P i) (by simp))
        exact ⟨readback1 heqs hj1 hug (eval_and2 (eval_bit ha (by omega)) (eval_bit hb (by omega))),
          readback1 heqs hj2 hup (eval_xor2 (eval_bit ha (by omega)) (eval_bit hb (by omega)))⟩
    | succ l ih =>
      intro hl k hk
      have hlK : l < KL N := by omega
      have ihk := ih (by omega) k hk
      rw [ksRec_succ]
      by_cases hg : 2 ^ l ≤ k
      · have ihq := ih (by omega) (k - 2 ^ l) (Nat.le_trans (Nat.sub_le k (2 ^ l)) hk)
        obtain ⟨j1, hj1⟩ := ksM_getElem?_of_mem h31
          (mem_node hlK hk (p := gOpP N l k) (by simp [nodeP, hg]))
        obtain ⟨j2, hj2⟩ := ksM_getElem?_of_mem h31
          (mem_node hlK hk (p := pOpP N l k) (by simp [nodeP, hg]))
        rw [if_pos hg]
        exact ⟨readback1 heqs hj1 hug (eval_or_and (eval_win hug ihk.1) (eval_win hup ihk.2)
            (eval_win hug ihq.1)),
          readback1 heqs hj2 hup (eval_and2 (eval_win hup ihk.2) (eval_win hup ihq.2))⟩
      · obtain ⟨j1, hj1⟩ := ksM_getElem?_of_mem h31
          (mem_node hlK hk (p := gPassP N l k) (by simp [nodeP, hg]))
        obtain ⟨j2, hj2⟩ := ksM_getElem?_of_mem h31
          (mem_node hlK hk (p := pPassP N l k) (by simp [nodeP, hg]))
        rw [if_neg hg]
        exact ⟨readback1 heqs hj1 hug (eval_win hug ihk.1), readback1 heqs hj2 hup (eval_win hup ihk.2)⟩
  -- the last level: the carries
  have hcarry : ∀ k, k ≤ N →
      ug.extract (KL N * (N + 1) + k) 1 = LVec.ofBitVec (BitVec.ofBool (BitVec.carry k x y ci)) := by
    intro k hk
    have hk2 : k < 2 ^ KL N := Nat.lt_of_lt_of_le (by omega) (le_two_pow_clog2' (N + 1))
    rw [(hlev (KL N) (Nat.le_refl _) k hk).1, ks_carry _ _ _ hk2, rippleCarry_bv]
  -- the sum, from its one-bit windows
  obtain ⟨js, hjs⟩ := ksM_getElem?_of_mem h31 (mem_sP (N := N) (i := 0) hN)
  obtain ⟨sv, hsv, hsw⟩ := hs.driven "s" ⟨js, _, _, Design2.writes_of_window? hjs rfl⟩
  rw [ksM_declWidth_s, Option.some.injEq] at hsw
  have hS : sv = LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N) := by
    apply LVec.eq_ofBitVec_of_extract_one hsw.symm
    intro i hi
    obtain ⟨j1, hj1⟩ := ksM_getElem?_of_mem h31 (mem_inCell hi (p := xP i) (by simp))
    have hxw : ux.extract i 1 = LVec.ofBitVec (BitVec.ofBool (x.getLsbD i ^^ y.getLsbD i)) :=
      readback1 heqs hj1 hux (eval_xor2 (eval_bit ha hi) (eval_bit hb hi))
    obtain ⟨j2, hj2⟩ := ksM_getElem?_of_mem h31 (mem_sP hi)
    rw [readback1 heqs hj2 hsv (eval_xor2 (eval_win hux hxw) (eval_win hug (hcarry i (by omega)))),
      BitVec.getLsbD_add_add_bool hi, Bool.xor_assoc]
  -- the carry out: `g[L][N]` is the final carry
  obtain ⟨jc, hjc⟩ := ksM_getElem?_of_mem h31 (mem_coutP (N := N))
  have hco := CombEqs.lookup_ident (ksM_comb h31) heqs hs hjc
    (eval_win hug (hcarry N (Nat.le_refl N))) (ksM_declWidth_cout N)
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.carry_width] at hco
  exact ⟨hS ▸ hsv, hco⟩

/-! ## 3e. From the settled state to the task's function -/

/-- A 1-bit vector is the `ofBool` of its only bit. -/
theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-- The sum the adder computes is the task's `s`: `(x + y + ci) mod 2^N`. -/
theorem sum_eq_ofNat {N : Nat} (hN : 1 ≤ N) (x y : BitVec N) (ci : Bool) :
    x + y + (BitVec.ofBool ci).setWidth N =
      BitVec.ofNat N (x.toNat + y.toNat + (BitVec.ofBool ci).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
  have hc : ci.toNat < 2 ^ N := by have := Bool.toNat_le ci; omega
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hc, Nat.mod_add_mod]

/-- The carry out the adder computes is the task's `cout`: `t / 2^N`, for any `t < 2 · 2^N`. -/
theorem carry_eq_ofNat {N : Nat} (t : Nat) (ht : t < 2 * 2 ^ N) :
    BitVec.ofBool (decide (2 ^ N ≤ t)) = BitVec.ofNat 1 (t / 2 ^ N) := by
  by_cases h : 2 ^ N ≤ t
  · have hq : t / 2 ^ N = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [h, hq]
  · have hq : t / 2 ^ N = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, hq]

/-- The interface: inputs `a b : N`, `cin : 1`; outputs `s : N`, `cout : 1`. -/
theorem ks_interface (N : Nat) : SvGolf.Tasks.Add.task.Interface N (ksM N) := by
  simp [CombTask.Interface, inputPorts, outputPorts, ksM_decls, ksDecls, SvGolf.Tasks.Add.task]

/-- **The Kogge-Stone adder meets the `add` statement, for every `N` in the task's range.** -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  have h31 : N < 2 ^ 31 := hN.2
  rw [ks_sem_eq hN' h31]
  refine CombTask.satisfiedAt_of_comb (ks_interface N) (ksM_comb h31) (ksM_acyclic h31) ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨ha, hb, hc⟩ := hv
  obtain ⟨hs', hco⟩ := ks_settled hN' h31 heqs hs ha hb hc
  have ht : x.toNat + y.toNat + c0.toNat < 2 * 2 ^ N := by
    have : x.toNat < 2 ^ N := x.isLt
    have : y.toNat < 2 ^ N := y.isLt
    have := Bool.toNat_le c0
    have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN'
    omega
  refine ⟨?_, ?_⟩
  · rw [hs', sum_eq_ofNat hN']
  · rw [hco, carry_eq_ofNat _ ht, BitVec.toNat_ofBool]

/-! ## Axioms -/

/-- info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission

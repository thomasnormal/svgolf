import LeanModels.Sv.CombProcEq

/-!
B2 spike, part 2b (scratch, no tree edit): a MINIATURE of the extended skeleton, over the CONTEXT-determined
family {lit, leaf, `Resize` marker, `+`, `-`, `& | ^`, `~`, `?:`}, against the real library (`leaf_eq`, `instExpr2_add`,
`ie_bnot_some`, ...). It exists to size the generalisation of `skT_shape` (the five facts) and `low_xf_gen`.
-/


/-! ## The glue of part 3 (plain Lean) -/

namespace LeanModels.Sv
namespace XF

/-- Zero extension of a bit function from `n` bits (what `Expr2.xfBits (.resize ..)` computes). -/
def zext (n : Nat) (f : Nat → Bool) : Nat → Bool := fun j => decide (j < n) && f j

theorem val_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ j, j < n → f j = g j) → val f n = val g n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [val]
      rw [val_congr (fun j hj => h j (by omega)), h n (by omega)]

theorem val_zext (n : Nat) (f : Nat → Bool) : ∀ m, n ≤ m → val (zext n f) m = val f n
  | 0, h => by
      obtain rfl : n = 0 := by omega
      rfl
  | m + 1, h => by
      by_cases hn : n ≤ m
      · simp only [val]
        rw [val_zext n f m hn]
        have : zext n f m = false := by simp [zext]; omega
        simp [this]
      · obtain rfl : n = m + 1 := by omega
        simp only [val]
        rw [val_congr (f := zext (m + 1) f) (g := f) (fun j hj => by simp [zext]; omega)]
        simp [zext]

theorem val_testBit (x : Nat) : ∀ n, val x.testBit n = x % 2 ^ n
  | 0 => by simp [val, Nat.mod_one]
  | n + 1 => by
      simp only [val, val_testBit x n]
      rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
      have h2 : x / 2 ^ n % 2 = 0 ∨ x / 2 ^ n % 2 = 1 := by omega
      rcases h2 with h | h <;> simp [h]

theorem toNat_bv (w : Nat) (f : Nat → Bool) : (bv w f).toNat = val f w := by
  unfold bv
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (val_lt f w)]

theorem bv_congr {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) : bv w f = bv w g := by
  unfold bv; rw [val_congr h]

/-- `zext` then `bv`: the `setWidth` of the narrow vector. -/
theorem bv_zext {n m : Nat} (f : Nat → Bool) (h : n ≤ m) : bv m (zext n f) = (bv n f).setWidth m := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bv, val_zext n f m h, BitVec.toNat_setWidth, toNat_bv, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le (val_lt f n) (Nat.pow_le_pow_right (by omega) h)

/-- **Addition glue.** The bit equations of a sum are `BitVec` addition. -/
theorem bv_addBits {w : Nat} {g f f' : Nat → Bool} (h : ∀ k, k < w → g k = addBits w f w f' k) :
    bv w g = bv w f + bv w f' := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bv, val_congr (g := (val f w + val f' w).testBit) h, val_testBit, BitVec.toNat_add,
    toNat_bv, toNat_bv]

/-- **Subtraction glue.** -/
theorem bv_subBits {w : Nat} {g f f' : Nat → Bool} (h : ∀ k, k < w → g k = subBits w f w f' k) :
    bv w g = bv w f - bv w f' := by
  apply BitVec.eq_of_toNat_eq
  have e : subBits w f w f' = (val f w + (2 ^ w - val f' w)).testBit := by
    funext k; simp [subBits]
  rw [toNat_bv, val_congr (g := (val f w + (2 ^ w - val f' w)).testBit) (fun k hk => by rw [h k hk, e]),
    val_testBit, BitVec.toNat_sub, toNat_bv, toNat_bv]
  congr 1
  omega

end XF
end LeanModels.Sv


namespace LeanModels.Sv.B2
open LeanModels.Sv CombView CombEq

/-! ## The skeleton -/

inductive ASk where
  | lit (v : LVec)
  | rd (a : Acc)
  /-- a `Resize` marker over a literal or an access: zero extension to the CONTEXT width -/
  | ext (a : ASk)
  | add (l r : ASk)
  | sub (l r : ASk)
  | gate (g : Gate) (l r : ASk)
  | bnot (a : ASk)
  | tern (c a b : ASk)

def ASk.isExt : ASk → Bool
  | .ext _ => true
  | _ => false

/-- a payload of a marker: a literal or an access -/
def ASk.Payload : ASk → Prop
  | .lit _ => True
  | .rd _ => True
  | _ => False

/-- no marker anywhere: a skeleton in a self-determined position -/
def ASk.NoExt : ASk → Prop
  | .lit _ => True
  | .rd _ => True
  | .ext _ => False
  | .add l r => l.NoExt ∧ r.NoExt
  | .sub l r => l.NoExt ∧ r.NoExt
  | .gate _ l r => l.NoExt ∧ r.NoExt
  | .bnot a => a.NoExt
  | .tern c a b => c.NoExt ∧ a.NoExt ∧ b.NoExt

/-- the NATURAL (self-determined) width: what `selfWidth2` / `rigidMax2` of the expression say -/
def ASk.width (σ : String → Int) (dw : String → Nat) : ASk → Nat
  | .lit v => v.width
  | .rd a => (a.win σ dw).2.2
  | .ext a => a.width σ dw
  | .add l r => max (l.width σ dw) (r.width σ dw)
  | .sub l r => max (l.width σ dw) (r.width σ dw)
  | .gate _ l r => max (l.width σ dw) (r.width σ dw)
  | .bnot a => a.width σ dw
  | .tern _ a b => max (a.width σ dw) (b.width σ dw)

/-- every operand fits the context `tw`: a bare leaf EXACTLY, a marker at most, the condition is a one-bit
marker-free skeleton -/
def ASk.WidthOk (σ : String → Int) (dw : String → Nat) : Nat → ASk → Prop
  | tw, .lit v => v.width = tw
  | tw, .rd a => (a.win σ dw).2.2 = tw
  | tw, .ext a => a.Payload ∧ a.width σ dw ≤ tw
  | tw, .add l r => l.WidthOk σ dw tw ∧ r.WidthOk σ dw tw
  | tw, .sub l r => l.WidthOk σ dw tw ∧ r.WidthOk σ dw tw
  | tw, .gate _ l r => l.WidthOk σ dw tw ∧ r.WidthOk σ dw tw
  | tw, .bnot a => a.WidthOk σ dw tw
  | tw, .tern c a b => c.NoExt ∧ c.WidthOk σ dw 1 ∧ c.width σ dw = 1 ∧ a.WidthOk σ dw tw ∧ b.WidthOk σ dw tw

/-- The expression `instantiate2` builds at the context width `tw`. A marker reads `tw`; the payload and the
condition (marker-free) do not. -/
def ASk.low (σ : String → Int) (tw : Nat) : ASk → Expr2
  | .lit v => .lit v
  | .rd a => accExpr σ a
  | .ext a => .resize tw (a.low σ 0)
  | .add l r => .binary .add (l.low σ tw) (r.low σ tw)
  | .sub l r => .binary .sub (l.low σ tw) (r.low σ tw)
  | .gate g l r => .binary g.op (l.low σ tw) (r.low σ tw)
  | .bnot a => .unary .bnot (a.low σ tw)
  | .tern c a b => .ternary (c.low σ 0) (a.low σ tw) (b.low σ tw)

/-- Bit `k` at context width `tw`: `tw` is read by `+ -` (the carry survives up to `tw`) only. -/
def ASk.bit (σ : String → Int) (dw : String → Nat) (tw : Nat) (rd : String → Nat → Bool) :
    ASk → Nat → Bool
  | .lit v, k => v.boolAt k
  | .rd a, k => accBit σ rd a k
  | .ext a, k => XF.zext (a.width σ dw) (a.bit σ dw (a.width σ dw) rd) k
  | .add l r, k => XF.addBits tw (l.bit σ dw tw rd) tw (r.bit σ dw tw rd) k
  | .sub l r, k => XF.subBits tw (l.bit σ dw tw rd) tw (r.bit σ dw tw rd) k
  | .gate .and l r, k => l.bit σ dw tw rd k && r.bit σ dw tw rd k
  | .gate .or l r, k => l.bit σ dw tw rd k || r.bit σ dw tw rd k
  | .gate .xor l r, k => l.bit σ dw tw rd k ^^ r.bit σ dw tw rd k
  | .bnot a, k => !(a.bit σ dw tw rd k)
  | .tern c a b, k =>
      if c.bit σ dw 1 rd 0 then a.bit σ dw tw rd k else b.bit σ dw tw rd k

def ASk.leaves : ASk → List Acc
  | .lit _ => []
  | .rd a => [a]
  | .ext a => a.leaves
  | .add l r => l.leaves ++ r.leaves
  | .sub l r => l.leaves ++ r.leaves
  | .gate _ l r => l.leaves ++ r.leaves
  | .bnot a => a.leaves
  | .tern c a b => c.leaves ++ a.leaves ++ b.leaves

def ASk.knownB : ASk → Bool
  | .lit v => v.knownB
  | .rd _ => true
  | .ext a => a.knownB
  | .add l r => l.knownB && r.knownB
  | .sub l r => l.knownB && r.knownB
  | .gate _ l r => l.knownB && r.knownB
  | .bnot a => a.knownB
  | .tern c a b => c.knownB && a.knownB && b.knownB

/-! ## The recognizer and the template side -/

def abinOk : SymBinOp → Bool
  | .m0 .and | .m0 .or | .m0 .xor | .m0 .add | .m0 .sub => true
  | _ => false

def ardsOf? (ds : List DeclT) : PExpr → Except String (List Acc)
  | .lit _ => .ok []
  | .binary op l r =>
      if abinOk op then
        match ardsOf? ds l with
        | .error e => .error e
        | .ok a =>
            match ardsOf? ds r with
            | .error e => .error e
            | .ok b => .ok (a ++ b)
      else .error "operator outside the fragment"
  | .unary op a =>
      match op with
      | .m0 .bnot => ardsOf? ds a
      | _ => .error "unary operator outside the fragment"
  | .ternary c t e =>
      match ardsOf? ds c with
      | .error m => .error m
      | .ok a =>
          match ardsOf? ds t with
          | .error m => .error m
          | .ok b =>
              match ardsOf? ds e with
              | .error m => .error m
              | .ok d => .ok (a ++ b ++ d)
  | .resize _ e =>
      match e with
      | .lit _ => .ok []
      | e => rdsLeaf? ds e
  | e => rdsLeaf? ds e

def acnt : PExpr → Nat
  | .lit _ => 0
  | .binary _ l r => acnt l + acnt r
  | .unary _ a => acnt a
  | .ternary c t e => acnt c + acnt t + acnt e
  | .resize _ (.lit _) => 0
  | _ => 1

def amk : BinOp → ASk → ASk → ASk
  | .and, l, r => .gate .and l r
  | .or, l, r => .gate .or l r
  | .xor, l, r => .gate .xor l r
  | .add, l, r => .add l r
  | .sub, l, r => .sub l r
  | _, l, _ => l

def askT : PExpr → List Acc → ASk
  | .lit v, _ => .lit v
  | .binary op l r, as =>
      match op with
      | .m0 b => amk b (askT l (as.take (acnt l))) (askT r (as.drop (acnt l)))
      | _ => .lit (LVec.mk #[])
  | .unary _ a, as => .bnot (askT a as)
  | .ternary c t e, as =>
      .tern (askT c (as.take (acnt c))) (askT t ((as.drop (acnt c)).take (acnt t)))
        (askT e ((as.drop (acnt c)).drop (acnt t)))
  | .resize _ (.lit v), _ => .ext (.lit v)
  | .resize _ _, as => .ext (.rd (as.headD (.whole "")))
  | _, as => .rd (as.headD (.whole ""))

def afragG : PExpr → Bool
  | .lit _ => true
  | .binary _ l r => afragG l && afragG r
  | .unary _ a => afragG a
  | .ternary c t e => afragG c && afragG t && afragG e
  | .concat _ => false
  | .fill _ => false
  | _ => true

theorem abinOk_cases {op : SymBinOp} (h : abinOk op = true) :
    op = .m0 .and ∨ op = .m0 .or ∨ op = .m0 .xor ∨ op = .m0 .add ∨ op = .m0 .sub := by
  cases op with
  | m0 b => cases b <;> simp_all [abinOk]
  | _ => simp_all [abinOk]

theorem ardsOf?_binary {ds : List DeclT} {op : SymBinOp} {l r : PExpr} {rs : List Acc}
    (h : ardsOf? ds (.binary op l r) = .ok rs) :
    abinOk op = true ∧ ∃ ra rb, ardsOf? ds l = .ok ra ∧ ardsOf? ds r = .ok rb ∧ rs = ra ++ rb := by
  simp only [ardsOf?] at h
  by_cases hb : abinOk op = true
  · rw [if_pos hb] at h
    rcases hl : ardsOf? ds l with e1 | ra
    · simp [hl] at h
    · rcases hr : ardsOf? ds r with e2 | rb
      · simp [hl, hr] at h
      · simp only [hl, hr, Except.ok.injEq] at h
        exact ⟨hb, ra, rb, rfl, rfl, h.symm⟩
  · rw [if_neg hb] at h
    simp at h

theorem ardsOf?_unary {ds : List DeclT} {op : SymUnaryOp} {a : PExpr} {rs : List Acc}
    (h : ardsOf? ds (.unary op a) = .ok rs) : op = .m0 .bnot ∧ ardsOf? ds a = .ok rs := by
  cases op with
  | m0 u => cases u <;> simp_all [ardsOf?]
  | _ => simp [ardsOf?] at h

theorem ardsOf?_ternary {ds : List DeclT} {c t e : PExpr} {rs : List Acc}
    (h : ardsOf? ds (.ternary c t e) = .ok rs) :
    ∃ rc rt re, ardsOf? ds c = .ok rc ∧ ardsOf? ds t = .ok rt ∧ ardsOf? ds e = .ok re ∧
      rs = rc ++ rt ++ re := by
  simp only [ardsOf?] at h
  rcases hc : ardsOf? ds c with e1 | rc
  · simp [hc] at h
  · rcases ht : ardsOf? ds t with e2 | rt
    · simp [hc, ht] at h
    · rcases he : ardsOf? ds e with e3 | re
      · simp [hc, ht, he] at h
      · simp only [hc, ht, he, Except.ok.injEq] at h
        exact ⟨rc, rt, re, rfl, rfl, rfl, h.symm⟩

/-- a marker accepts a literal (no read) or one access -/
theorem ardsOf?_resize {ds : List DeclT} {m : Nat} {e : PExpr} {rs : List Acc}
    (h : ardsOf? ds (.resize m e) = .ok rs) :
    (∃ v, e = .lit v ∧ rs = []) ∨ ((∀ v, e ≠ .lit v) ∧ ∃ a, leafRd? ds e = .ok a ∧ rs = [a]) := by
  by_cases hl : ∃ v, e = .lit v
  · obtain ⟨v, rfl⟩ := hl
    left; simp [ardsOf?] at h; exact ⟨v, rfl, h⟩
  · have hn : ∀ v, e ≠ .lit v := fun v h => hl ⟨v, h⟩
    right
    refine ⟨hn, ?_⟩
    have h' : rdsLeaf? ds e = .ok rs := by
      cases e <;> first | exact absurd rfl (hn _) | simpa [ardsOf?] using h
    exact rdsLeaf_cases h'

theorem ardsOf?_len {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), ardsOf? ds v = .ok rs → afragG v = true → rs.length = acnt v
  | .lit _, rs, h, _ => by simp [ardsOf?] at h; subst h; simp [acnt]
  | .binary op l r, rs, h, hf => by
      simp only [afragG, Bool.and_eq_true] at hf
      obtain ⟨-, ra, rb, hl, hr, rfl⟩ := ardsOf?_binary h
      simp [acnt, ardsOf?_len l ra hl hf.1, ardsOf?_len r rb hr hf.2]
  | .unary op a, rs, h, hf => by
      obtain ⟨-, ha⟩ := ardsOf?_unary h
      simp only [afragG] at hf
      simp [acnt, ardsOf?_len a rs ha hf]
  | .ternary c t e, rs, h, hf => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := ardsOf?_ternary h
      simp only [afragG, Bool.and_eq_true] at hf
      simp [acnt, ardsOf?_len c rc hc hf.1.1, ardsOf?_len t rt ht hf.1.2, ardsOf?_len e re he hf.2,
        Nat.add_assoc]
  | .resize m e, rs, h, _ => by
      rcases ardsOf?_resize h with ⟨v, rfl, rfl⟩ | ⟨hn, a, -, rfl⟩
      · simp [acnt]
      · cases e <;> first | exact absurd rfl (hn _) | simp [acnt]
  | .ident n, rs, h, _ => by simp [ardsOf?, rdsLeaf?, leafRd?] at h; subst h; simp [acnt]
  | .bitSel b i, rs, h, _ => by
      obtain ⟨a, -, rfl⟩ := rdsLeaf_cases (by simpa [ardsOf?] using h)
      simp [acnt]
  | .arrayElem n is, rs, h, _ => by
      obtain ⟨a, -, rfl⟩ := rdsLeaf_cases (by simpa [ardsOf?] using h)
      simp [acnt]
  | .arrayPart n is m a b, rs, h, _ => by
      obtain ⟨a', -, rfl⟩ := rdsLeaf_cases (by simpa [ardsOf?] using h)
      simp [acnt]
  | .concat _, _, _, hf => by simp [afragG] at hf
  | .fill _, _, _, hf => by simp [afragG] at hf
  | .paramRef .., rs, h, _ | .genvarRef .., rs, h, _ | .enumRef .., rs, h, _
  | .int .., rs, h, _ | .signedResize .., rs, h, _ | .squash2 .., rs, h, _
  | .sysCall .., rs, h, _ | .partSel .., rs, h, _ | .repl .., rs, h, _
  | .reduce .., rs, h, _
  | .cast .., rs, h, _ | .unsupported .., rs, h, _ => by
      simp [ardsOf?, rdsLeaf?, leafRd?] at h


/-! ## What the equation prints: the `ASk.bit` of `t = a + b + cin` (the note's `addw`, context `N + 1`), unfolded by
the recipe `sv_equations` uses (`Sk.bit`, `accBit`, the accessors) -/

section print
open CombView in
example (st : SvState) (N k : Nat) : True := by
  have : ∃ b : Bool,
      (ASk.add (.add (.ext (.rd (.whole "a"))) (.ext (.rd (.whole "b")))) (.ext (.rd (.whole "cin")))).bit
        (fun _ => 0) (fun n => if n = "cin" then 1 else N) (N + 1) st.boolAt k = b := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ := this
  simp only [ASk.bit, accBit, ASk.width, Acc.lo, Acc.win, Nat.zero_add, ite_true, String.reduceEq] at hb
  trace_state
  trivial
end print

end LeanModels.Sv.B2

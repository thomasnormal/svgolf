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


/-! ## Width facts -/

section widths
variable {σ : String → Int} {dw : String → Nat}

theorem ASk.width_le : ∀ (sk : ASk) (tw : Nat), sk.WidthOk σ dw tw → sk.width σ dw ≤ tw
  | .lit _, tw, h => by simp only [ASk.WidthOk] at h; simp [ASk.width, h]
  | .rd _, tw, h => by simp only [ASk.WidthOk] at h; simp [ASk.width, h]
  | .ext _, tw, h => by simpa [ASk.width, ASk.WidthOk] using h.2
  | .add l r, tw, h => by
      have := ASk.width_le l tw h.1; have := ASk.width_le r tw h.2; simp [ASk.width]; omega
  | .sub l r, tw, h => by
      have := ASk.width_le l tw h.1; have := ASk.width_le r tw h.2; simp [ASk.width]; omega
  | .gate g l r, tw, h => by
      have := ASk.width_le l tw h.1; have := ASk.width_le r tw h.2; simp [ASk.width]; omega
  | .bnot a, tw, h => by simpa [ASk.width] using ASk.width_le a tw h
  | .tern c a b, tw, h => by
      have := ASk.width_le a tw h.2.2.2.1; have := ASk.width_le b tw h.2.2.2.2
      simp [ASk.width]; omega

/-- the natural width is as good as the context, down to the skeleton's own width -/
theorem ASk.WidthOk.mono : ∀ (sk : ASk) (tw W : Nat), sk.WidthOk σ dw tw →
    sk.width σ dw ≤ W → W ≤ tw → sk.WidthOk σ dw W
  | .lit _, tw, W, h, h1, h2 => by simp only [ASk.WidthOk, ASk.width] at h h1 ⊢; omega
  | .rd _, tw, W, h, h1, h2 => by simp only [ASk.WidthOk, ASk.width] at h h1 ⊢; omega
  | .ext _, tw, W, h, h1, h2 => by simp only [ASk.WidthOk, ASk.width] at h h1 ⊢; exact ⟨h.1, h1⟩
  | .add l r, tw, W, h, h1, h2 => by
      simp only [ASk.width, Nat.max_le] at h1
      exact ⟨ASk.WidthOk.mono l tw W h.1 h1.1 h2, ASk.WidthOk.mono r tw W h.2 h1.2 h2⟩
  | .sub l r, tw, W, h, h1, h2 => by
      simp only [ASk.width, Nat.max_le] at h1
      exact ⟨ASk.WidthOk.mono l tw W h.1 h1.1 h2, ASk.WidthOk.mono r tw W h.2 h1.2 h2⟩
  | .gate g l r, tw, W, h, h1, h2 => by
      simp only [ASk.width, Nat.max_le] at h1
      exact ⟨ASk.WidthOk.mono l tw W h.1 h1.1 h2, ASk.WidthOk.mono r tw W h.2 h1.2 h2⟩
  | .bnot a, tw, W, h, h1, h2 => ASk.WidthOk.mono a tw W h h1 h2
  | .tern c a b, tw, W, h, h1, h2 => by
      simp only [ASk.width, Nat.max_le] at h1
      exact ⟨h.1, h.2.1, h.2.2.1, ASk.WidthOk.mono a tw W h.2.2.2.1 h1.1 h2,
        ASk.WidthOk.mono b tw W h.2.2.2.2 h1.2 h2⟩

/-- a marker-free skeleton is lowered at any width alike -/
theorem ASk.low_irrel : ∀ (sk : ASk), sk.NoExt → ∀ t1 t2, sk.low σ t1 = sk.low σ t2
  | .lit _, _, _, _ => rfl
  | .rd _, _, _, _ => rfl
  | .ext _, h, _, _ => by simp [ASk.NoExt] at h
  | .add l r, h, t1, t2 => by
      simp only [ASk.low, ASk.low_irrel l h.1 t1 t2, ASk.low_irrel r h.2 t1 t2]
  | .sub l r, h, t1, t2 => by
      simp only [ASk.low, ASk.low_irrel l h.1 t1 t2, ASk.low_irrel r h.2 t1 t2]
  | .gate g l r, h, t1, t2 => by
      simp only [ASk.low, ASk.low_irrel l h.1 t1 t2, ASk.low_irrel r h.2 t1 t2]
  | .bnot a, h, t1, t2 => by simp only [ASk.low, ASk.low_irrel a h t1 t2]
  | .tern c a b, h, t1, t2 => by
      simp only [ASk.low, ASk.low_irrel a h.2.1 t1 t2, ASk.low_irrel b h.2.2 t1 t2]

end widths

/-! ## The instance facts -/

section shape
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- the flags `instExpr2`'s `.resize` arm reads, for a leaf -/
theorem leaf_flags {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a) :
    e.ctxPropagates = false ∧ e.constLeaf = false ∧
      ∀ (env : IEnv) (m w : Nat), (PExpr.resize m e).negGenvarWidened env w = none := by
  cases e <;> simp [leafRd?] at h <;>
    first
    | exact ⟨rfl, rfl, fun _ _ _ => rfl⟩
    | (split at h <;> simp_all)
    | skip

/-- **The instance fact for a marker over a leaf**, at every context width, whatever the leaf's width. -/
theorem ie_resize_leaf (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a)
    (m cw : Nat) :
    instExpr2 E elems (some cw) (.resize m e) = .resize cw (accExpr σ a) := by
  obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw h ha
  obtain ⟨hcp, hcl, hng⟩ := leaf_flags h
  simp [instExpr2, hsw, hcp, hcl, hng, hin]

/-- … and over a literal -/
theorem ie_resize_lit (m cw : Nat) (v : LVec) :
    instExpr2 E elems (some cw) (.resize m (.lit v)) = .resize cw (.lit v) := by
  simp [instExpr2, PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, selfWidth2]

theorem ie_bin_none (b : BinOp) (hb : b = .and ∨ b = .or ∨ b = .xor ∨ b = .add ∨ b = .sub)
    (l r : PExpr) {a c : Nat} (hl : selfWidth2 E elems l = some a) (hr : selfWidth2 E elems r = some c) :
    instExpr2 E elems none (.binary (.m0 b) l r) =
      .binary b (fitExpr2 E elems (some (max a c)) l) (fitExpr2 E elems (some (max a c)) r) := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [instExpr2, hl, hr]

theorem ie_ternary_none' (c t e : PExpr) {a b : Nat} (ht : selfWidth2 E elems t = some a)
    (he : selfWidth2 E elems e = some b) :
    instExpr2 E elems none (.ternary c t e) =
      .ternary (instExpr2 E elems none c) (fitExpr2 E elems (some (max a b)) t)
        (fitExpr2 E elems (some (max a b)) e) := by
  simp [instExpr2, ht, he]

/-- **The generalised shape theorem** (the five facts of `skT_shape`, with the NATURAL width `W` for the
self-determined reading and the context `tw` for the context-determined ones):
`selfWidth2 = rigidMax2 = W`; at no context (unless the root is a marker) the lowering is `low W`; at the
context `tw` and under `fitExpr2` it is `low tw`. -/
theorem ashape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), ardsOf? ds v = .ok rs → afragG v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ∀ tw, (askT v rs).WidthOk σ dw tw →
        selfWidth2 E elems v = some ((askT v rs).width σ dw) ∧
        rigidMax2 E elems v = some ((askT v rs).width σ dw) ∧
        ((askT v rs).isExt = false →
          instExpr2 E elems none v = (askT v rs).low σ ((askT v rs).width σ dw)) ∧
        instExpr2 E elems (some tw) v = (askT v rs).low σ tw ∧
        fitExpr2 E elems (some tw) v = (askT v rs).low σ tw
  | .lit lv, rs, h, _, _, tw, hw => by
      simp only [ardsOf?, Except.ok.injEq] at h
      subst h
      simp only [askT, ASk.WidthOk] at hw
      refine ⟨by simp [askT, ASk.width, selfWidth2], by simp [askT, ASk.width, rigidMax2, selfWidth2],
        fun _ => by simp [askT, ASk.low, instExpr2], by simp [askT, ASk.low, instExpr2], ?_⟩
      rw [fitExpr2_lit, if_pos hw]
      simp [askT, ASk.low]
  | .binary op l r, rs, h, hf, hacc, tw, hw => by
      simp only [afragG, Bool.and_eq_true] at hf
      obtain ⟨hb, ra, rb, hl, hr, rfl⟩ := ardsOf?_binary h
      have hla := ardsOf?_len l ra hl hf.1
      have e1 : (ra ++ rb).take (acnt l) = ra := List.take_left' hla
      have e2 : (ra ++ rb).drop (acnt l) = rb := List.drop_left' hla
      have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
      have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
      have ihl := ashape C hdw l ra hl hf.1 hacl
      have ihr := ashape C hdw r rb hr hf.2 hacr
      -- the node is `amk b sl sr` for some `b` of the five
      obtain ⟨b, rfl, hbb⟩ : ∃ b, op = .m0 b ∧ (b = .and ∨ b = .or ∨ b = .xor ∨ b = .add ∨ b = .sub) := by
        rcases abinOk_cases hb with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, by simp⟩
      have hsk : askT (.binary (.m0 b) l r) (ra ++ rb) = amk b (askT l ra) (askT r rb) := by
        simp [askT, e1, e2]
      rw [hsk] at hw ⊢
      -- the widths of the two operands and the shape of the node
      have hwk : (askT l ra).WidthOk σ dw tw ∧ (askT r rb).WidthOk σ dw tw := by
        rcases hbb with rfl | rfl | rfl | rfl | rfl <;> exact hw
      obtain ⟨Sl, Rl, I0l, I1l, Fl⟩ := ihl tw hwk.1
      obtain ⟨Sr, Rr, I0r, I1r, Fr⟩ := ihr tw hwk.2
      have hlw := ASk.width_le _ _ hwk.1
      have hrw := ASk.width_le _ _ hwk.2
      -- the children at their own (natural) widths
      have hWl := ASk.WidthOk.mono _ _ (max ((askT l ra).width σ dw) ((askT r rb).width σ dw)) hwk.1
        (Nat.le_max_left _ _) (by omega)
      have hWr := ASk.WidthOk.mono _ _ (max ((askT l ra).width σ dw) ((askT r rb).width σ dw)) hwk.2
        (Nat.le_max_right _ _) (by omega)
      obtain ⟨-, -, -, -, FlW⟩ := ihl _ hWl
      obtain ⟨-, -, -, -, FrW⟩ := ihr _ hWr
      have hS : selfWidth2 E elems (.binary (.m0 b) l r) =
          some (max ((askT l ra).width σ dw) ((askT r rb).width σ dw)) := by
        rcases hbb with rfl | rfl | rfl | rfl | rfl <;> simp [selfWidth2, Sl, Sr]
      have hR : rigidMax2 E elems (.binary (.m0 b) l r) =
          some (max ((askT l ra).width σ dw) ((askT r rb).width σ dw)) := by
        rcases hbb with rfl | rfl | rfl | rfl | rfl <;> simp [rigidMax2, Rl, Rr]
      have hI0 := ie_bin_none b hbb l r Sl Sr
      have hI1 : instExpr2 E elems (some tw) (.binary (.m0 b) l r) =
          .binary b (fitExpr2 E elems (some tw) l) (fitExpr2 E elems (some tw) r) := by
        rcases hbb with rfl | rfl | rfl | rfl | rfl
        · simp [instExpr2]
        · simp [instExpr2]
        · simp [instExpr2]
        · exact instExpr2_add tw l r (by simp [ctxOpWidth2, Rl, Rr]; omega)
        · exact instExpr2_sub tw l r (by simp [ctxOpWidth2, Rl, Rr]; omega)
      rw [Fl, Fr] at hI1
      rw [FlW, FrW] at hI0
      rcases hbb with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨hS, hR, fun _ => hI0, hI1, by rw [fitExpr2_binary]; exact hI1⟩
  | .unary op a, rs, h, hf, hacc, tw, hw => by
      obtain ⟨rfl, ha⟩ := ardsOf?_unary h
      simp only [afragG] at hf
      have hsk : askT (.unary (.m0 .bnot) a) rs = .bnot (askT a rs) := by simp [askT]
      rw [hsk] at hw ⊢
      simp only [ASk.WidthOk] at hw
      obtain ⟨Sa, Ra, I0a, I1a, Fa⟩ := ashape C hdw a rs ha hf hacc tw hw
      have hle := ASk.width_le _ _ hw
      have hrm : (rigidMax2 E elems a).getD tw ≤ tw := by rw [Ra]; simpa using hle
      have I1 : instExpr2 E elems (some tw) (.unary (.m0 .bnot) a) =
          (ASk.bnot (askT a rs)).low σ tw := by
        rw [ie_bnot_some tw a hrm, Fa]; rfl
      have hW := ASk.WidthOk.mono _ _ ((askT a rs).width σ dw) hw (Nat.le_refl _) hle
      obtain ⟨-, -, -, I1aW, -⟩ := ashape C hdw a rs ha hf hacc _ hW
      refine ⟨by rw [sw_bnot]; exact Sa, by rw [rm_bnot]; exact Ra, fun _ => ?_, I1, ?_⟩
      · rw [ie_bnot_none, Sa, I1aW]; rfl
      · rw [fitExpr2_of_not_rigid tw (rigidExpr_unary _ _)]; exact I1
  | .ternary c t f, rs, h, hf, hacc, tw, hw => by
      obtain ⟨rc, rt, rf, hc, ht, hfe, rfl⟩ := ardsOf?_ternary h
      simp only [afragG, Bool.and_eq_true] at hf
      have hc' := ardsOf?_len c rc hc hf.1.1
      have ht' := ardsOf?_len t rt ht hf.1.2
      have e1 : (rc ++ rt ++ rf).take (acnt c) = rc := by
        rw [List.append_assoc]; exact List.take_left' hc'
      have e2 : (rc ++ rt ++ rf).drop (acnt c) = rt ++ rf := by
        rw [List.append_assoc]; exact List.drop_left' hc'
      have e3 : (rt ++ rf).take (acnt t) = rt := List.take_left' ht'
      have e4 : (rt ++ rf).drop (acnt t) = rf := List.drop_left' ht'
      have hsk : askT (.ternary c t f) (rc ++ rt ++ rf) = .tern (askT c rc) (askT t rt) (askT f rf) := by
        simp only [askT, e1, e2, e3, e4]
      rw [hsk] at hw ⊢
      obtain ⟨hnc, hwc, hwc1, hwt, hwf⟩ := hw
      have hcext : (askT c rc).isExt = false := by
        cases hcc : askT c rc <;> simp_all [ASk.NoExt, ASk.isExt]
      obtain ⟨-, -, I0c, -, -⟩ := ashape C hdw c rc hc hf.1.1
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_left _ hx))) 1 hwc
      have I0c' := I0c hcext
      rw [hwc1] at I0c'
      obtain ⟨St, Rt, I0t, I1t, Ft⟩ := ashape C hdw t rt ht hf.1.2
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx))) tw hwt
      obtain ⟨Sf, Rf, I0f, I1f, Ff⟩ := ashape C hdw f rf hfe hf.2
        (fun x hx => hacc x (List.mem_append_right _ hx)) tw hwf
      have hlt := ASk.width_le _ _ hwt
      have hlf := ASk.width_le _ _ hwf
      have hWt := ASk.WidthOk.mono _ _ (max ((askT t rt).width σ dw) ((askT f rf).width σ dw)) hwt
        (Nat.le_max_left _ _) (by omega)
      have hWf := ASk.WidthOk.mono _ _ (max ((askT t rt).width σ dw) ((askT f rf).width σ dw)) hwf
        (Nat.le_max_right _ _) (by omega)
      obtain ⟨-, -, -, -, FtW⟩ := ashape C hdw t rt ht hf.1.2
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx))) _ hWt
      obtain ⟨-, -, -, -, FfW⟩ := ashape C hdw f rf hfe hf.2
        (fun x hx => hacc x (List.mem_append_right _ hx)) _ hWf
      have I1 : instExpr2 E elems (some tw) (.ternary c t f) =
          (ASk.tern (askT c rc) (askT t rt) (askT f rf)).low σ tw := by
        rw [ie_ternary_some, I0c', Ft, Ff]
        simp only [ASk.low, ASk.low_irrel _ hnc 1 0]
      refine ⟨by simp [selfWidth2, St, Sf, ASk.width], by simp [rigidMax2, Rt, Rf, ASk.width],
        fun _ => ?_, I1, ?_⟩
      · rw [ie_ternary_none' c t f St Sf, I0c', FtW, FfW]
        simp only [ASk.low, ASk.width, ASk.low_irrel _ hnc 1 0]
      · rw [fitExpr2_of_not_rigid tw (rigidExpr_ternary _ _ _)]; exact I1
  | .resize m e, rs, h, _, hacc, tw, hw => by
      rcases ardsOf?_resize h with ⟨v, rfl, rfl⟩ | ⟨hn, a, hl, rfl⟩
      · simp only [askT, ASk.WidthOk, ASk.width, ASk.Payload] at hw ⊢
        refine ⟨by simp [selfWidth2], by simp [rigidMax2, selfWidth2], fun h => by simp [ASk.isExt] at h,
          ?_, ?_⟩
        · rw [ie_resize_lit]; simp [ASk.low]
        · rw [fitExpr2_of_not_rigid tw rfl, ie_resize_lit]; simp [ASk.low]
      · have hsk : askT (.resize m e) [a] = .ext (.rd a) := by
          cases e <;> first | exact absurd rfl (hn _) | rfl
        rw [hsk] at hw ⊢
        obtain ⟨hsw, -, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
        have I1 : instExpr2 E elems (some tw) (.resize m e) = (ASk.ext (.rd a)).low σ tw := by
          rw [ie_resize_leaf C hdw hl (hacc a (by simp)) m tw]; rfl
        refine ⟨by simp [selfWidth2, hsw, ASk.width], by simp [rigidMax2, ASk.width, rm_leaf hl, hsw],
          fun h => by simp [ASk.isExt] at h, I1, ?_⟩
        rw [fitExpr2_of_not_rigid tw rfl]; exact I1
  | .ident n, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [ardsOf?] using h)
      simp only [askT, List.headD_cons, ASk.WidthOk, ASk.low, ASk.width] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨hsw, by rw [rm_leaf hl, hsw], fun _ => hin none, hin _,
        leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .bitSel b i, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [ardsOf?] using h)
      simp only [askT, List.headD_cons, ASk.WidthOk, ASk.low, ASk.width] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨hsw, by rw [rm_leaf hl, hsw], fun _ => hin none, hin _,
        leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .arrayElem n is, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [ardsOf?] using h)
      simp only [askT, List.headD_cons, ASk.WidthOk, ASk.low, ASk.width] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨hsw, by rw [rm_leaf hl, hsw], fun _ => hin none, hin _,
        leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .arrayPart n is m a b, rs, h, _, hacc, tw, hw => by
      obtain ⟨a', hl, rfl⟩ := rdsLeaf_cases (by simpa [ardsOf?] using h)
      simp only [askT, List.headD_cons, ASk.WidthOk, ASk.low, ASk.width] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a' (by simp))
      exact ⟨hsw, by rw [rm_leaf hl, hsw], fun _ => hin none, hin _,
        leaf_fit C hdw hl (hacc a' (by simp)) hw⟩
  | .concat _, _, _, hf, _, _, _ => by simp [afragG] at hf
  | .fill _, _, _, hf, _, _, _ => by simp [afragG] at hf
  | .paramRef .., rs, h, _, _, _, _ | .genvarRef .., rs, h, _, _, _, _
  | .enumRef .., rs, h, _, _, _, _
  | .int .., rs, h, _, _, _, _
  | .signedResize .., rs, h, _, _, _, _
  | .squash2 .., rs, h, _, _, _, _
  | .sysCall .., rs, h, _, _, _, _ | .partSel .., rs, h, _, _, _, _ | .repl .., rs, h, _, _, _, _
  | .reduce .., rs, h, _, _, _, _
  | .cast .., rs, h, _, _, _, _
  | .unsupported .., rs, h, _, _, _, _ => by
      simp [ardsOf?, rdsLeaf?, leafRd?] at h

end shape

/-! ## The x-free reading: width and Boolean bits of the lowered expression -/

section xf
variable {m : Design2} {σ : String → Int} {dw : String → Nat}

theorem addBits_congr {w : Nat} {f f' g g' : Nat → Bool} (hf : ∀ j, j < w → f j = f' j)
    (hg : ∀ j, j < w → g j = g' j) (k : Nat) : XF.addBits w f w g k = XF.addBits w f' w g' k := by
  simp only [XF.addBits, XF.val_congr hf, XF.val_congr hg]

theorem subBits_congr {w : Nat} {f f' g g' : Nat → Bool} (hf : ∀ j, j < w → f j = f' j)
    (hg : ∀ j, j < w → g j = g' j) (k : Nat) : XF.subBits w f w g k = XF.subBits w f' w g' k := by
  simp only [XF.subBits, XF.val_congr hf, XF.val_congr hg]

/-- the payload of a marker (a literal or an access) at its own width, for every bit -/
theorem payload_xf : ∀ (a : ASk), a.Payload → a.knownB = true → (∀ x ∈ a.leaves, LeafOk m σ dw x) →
    ∀ env : String → Nat → Bool,
    (a.low σ 0).xfWidth m = some (a.width σ dw) ∧
      ∀ k, (a.low σ 0).xfBits m env k = a.bit σ dw (a.width σ dw) env k
  | .lit v, _, hk, _, env => by
      simp only [ASk.knownB] at hk
      exact ⟨by simp [ASk.low, ASk.width, Expr2.xfWidth, hk], fun k => by simp [ASk.low, ASk.bit, Expr2.xfBits]⟩
  | .rd a, _, _, hL, env =>
      ⟨by rw [ASk.low, expr_xfWidth (hL a (by simp [ASk.leaves])), ASk.width],
       fun k => by simp [ASk.low, ASk.bit, expr_xfBits]⟩
  | .ext _, h, _, _, _ => by simp [ASk.Payload] at h
  | .add _ _, h, _, _, _ => by simp [ASk.Payload] at h
  | .sub _ _, h, _, _, _ => by simp [ASk.Payload] at h
  | .gate _ _ _, h, _, _, _ => by simp [ASk.Payload] at h
  | .bnot _, h, _, _, _ => by simp [ASk.Payload] at h
  | .tern _ _ _, h, _, _, _ => by simp [ASk.Payload] at h

/-- **The lowered expression is in the x-free fragment at the context width, and its Boolean bits are the
skeleton's** (markers: zero extension; `+ -`: `XF.addBits tw`, `XF.subBits tw`). -/
theorem alow_xf_gen :
    ∀ (sk : ASk) (tw : Nat), sk.knownB = true → sk.WidthOk σ dw tw →
      (∀ a ∈ sk.leaves, LeafOk m σ dw a) → ∀ env : String → Nat → Bool,
      (sk.low σ tw).xfWidth m = some tw ∧
        ∀ k, k < tw → (sk.low σ tw).xfBits m env k = sk.bit σ dw tw env k
  | .lit v, tw, hk, hw, _, env => by
      simp only [ASk.knownB] at hk
      simp only [ASk.WidthOk] at hw
      exact ⟨by simp [ASk.low, Expr2.xfWidth, hk, hw], fun k _ => by simp [ASk.low, ASk.bit, Expr2.xfBits]⟩
  | .rd a, tw, _, hw, hL, env => by
      simp only [ASk.WidthOk] at hw
      exact ⟨by rw [ASk.low, expr_xfWidth (hL a (by simp [ASk.leaves])), hw],
        fun k _ => by simp [ASk.low, ASk.bit, expr_xfBits]⟩
  | .ext a, tw, hk, hw, hL, env => by
      simp only [ASk.knownB] at hk
      simp only [ASk.WidthOk] at hw
      obtain ⟨h1, h2⟩ := payload_xf a hw.1 hk hL env
      refine ⟨by simp [ASk.low, Expr2.xfWidth, h1], fun k _ => ?_⟩
      simp [ASk.low, ASk.bit, Expr2.xfBits, h1, h2, XF.zext]
  | .add l r, tw, hk, hw, hL, env => by
      simp only [ASk.knownB, Bool.and_eq_true] at hk
      simp only [ASk.WidthOk] at hw
      obtain ⟨h1, b1⟩ := alow_xf_gen l tw hk.1 hw.1 (fun a ha => hL a (by simp [ASk.leaves, ha])) env
      obtain ⟨h2, b2⟩ := alow_xf_gen r tw hk.2 hw.2 (fun a ha => hL a (by simp [ASk.leaves, ha])) env
      refine ⟨by simp [ASk.low, Expr2.xfWidth, h1, h2, XF.comb], fun k _ => ?_⟩
      simp only [ASk.low, ASk.bit, Expr2.xfBits, h1, h2, Option.getD_some]
      exact addBits_congr b1 b2 k
  | .sub l r, tw, hk, hw, hL, env => by
      simp only [ASk.knownB, Bool.and_eq_true] at hk
      simp only [ASk.WidthOk] at hw
      obtain ⟨h1, b1⟩ := alow_xf_gen l tw hk.1 hw.1 (fun a ha => hL a (by simp [ASk.leaves, ha])) env
      obtain ⟨h2, b2⟩ := alow_xf_gen r tw hk.2 hw.2 (fun a ha => hL a (by simp [ASk.leaves, ha])) env
      refine ⟨by simp [ASk.low, Expr2.xfWidth, h1, h2, XF.comb], fun k _ => ?_⟩
      simp only [ASk.low, ASk.bit, Expr2.xfBits, h1, h2, Option.getD_some]
      exact subBits_congr b1 b2 k
  | .gate g l r, tw, hk, hw, hL, env => by
      simp only [ASk.knownB, Bool.and_eq_true] at hk
      simp only [ASk.WidthOk] at hw
      obtain ⟨h1, b1⟩ := alow_xf_gen l tw hk.1 hw.1 (fun a ha => hL a (by simp [ASk.leaves, ha])) env
      obtain ⟨h2, b2⟩ := alow_xf_gen r tw hk.2 hw.2 (fun a ha => hL a (by simp [ASk.leaves, ha])) env
      refine ⟨by cases g <;> simp [ASk.low, Gate.op, Expr2.xfWidth, h1, h2, XF.same], fun k hk' => ?_⟩
      cases g <;> simp [ASk.low, ASk.bit, Gate.op, Expr2.xfBits, b1 k hk', b2 k hk']
  | .bnot a, tw, hk, hw, hL, env => by
      simp only [ASk.knownB] at hk
      simp only [ASk.WidthOk] at hw
      obtain ⟨h1, b1⟩ := alow_xf_gen a tw hk hw (fun x hx => hL x (by simpa [ASk.leaves] using hx)) env
      exact ⟨by simp [ASk.low, Expr2.xfWidth, h1], fun k hk' => by
        simp [ASk.low, ASk.bit, Expr2.xfBits, b1 k hk']⟩
  | .tern c a b, tw, hk, hw, hL, env => by
      simp only [ASk.knownB, Bool.and_eq_true] at hk
      obtain ⟨hnc, hwc, hwc1, hwa, hwb⟩ := hw
      obtain ⟨h1, b1⟩ := alow_xf_gen c 1 hk.1.1 hwc (fun x hx => hL x (by simp [ASk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := alow_xf_gen a tw hk.1.2 hwa (fun x hx => hL x (by simp [ASk.leaves, hx])) env
      obtain ⟨h3, b3⟩ := alow_xf_gen b tw hk.2 hwb (fun x hx => hL x (by simp [ASk.leaves, hx])) env
      rw [ASk.low_irrel c hnc 1 0] at h1 b1
      refine ⟨xf_tern h1 h2 h3, fun k hk' => ?_⟩
      simp only [ASk.low, ASk.bit]
      rw [xfb_tern h1, b1 0 (by omega), b2 k hk', b3 k hk']

end xf

/-! ## The reads of the new nodes (`inst_rd`'s arms): `RdOK` at EVERY context -/

section rd
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}

theorem ie_addsub_cases (b : BinOp) (hb : b = .add ∨ b = .sub) (ctx : Option Nat) (l r : PExpr) :
    (∃ c, instExpr2 E elems ctx (.binary (.m0 b) l r) =
      .binary b (fitExpr2 E elems c l) (fitExpr2 E elems c r)) ∨
    (∃ w c, instExpr2 E elems ctx (.binary (.m0 b) l r) =
      .resize w (.binary b (fitExpr2 E elems c l) (fitExpr2 E elems c r))) := by
  cases ctx with
  | none =>
      refine Or.inl ?_
      rcases hb with rfl | rfl <;> (unfold instExpr2; exact ⟨_, rfl⟩)
  | some w =>
      by_cases h : (ctxOpWidth2 E elems l r).getD w ≤ w
      · exact Or.inl ⟨some w, by rcases hb with rfl | rfl <;> simp [instExpr2, h]⟩
      · exact Or.inr ⟨w, some ((ctxOpWidth2 E elems l r).getD w),
          by rcases hb with rfl | rfl <;> simp [instExpr2, h]⟩

/-- a marker over a non-propagating, non-constant operand is always `resize` over an instantiation of it -/
theorem ie_resize_cases {e : PExpr} (hcp : e.ctxPropagates = false) (hcl : e.constLeaf = false)
    (hng : ∀ (env : IEnv) (m w : Nat), (PExpr.resize m e).negGenvarWidened env w = none)
    (ctx : Option Nat) (m : Nat) :
    ∃ x c, instExpr2 E elems ctx (.resize m e) = .resize x (instExpr2 E elems c e) := by
  cases ctx with
  | none => exact ⟨m, selfWidth2 E elems e, by simp [instExpr2]⟩
  | some cw =>
      rcases hs : selfWidth2 E elems e with _ | sw
      · exact ⟨cw, none, by simp [instExpr2, hs]⟩
      · by_cases h : sw < cw
        · exact ⟨cw, some sw, by simp [instExpr2, hs, h, hcp, hng]⟩
        · exact ⟨cw, some sw, by simp [instExpr2, hs, h, hcl]⟩

end rd

/-! ## The truncation marker `Resize3[(a + b)]` (envelope of `addw3.sv`): an arithmetic node under a marker WIDER
than the context is lowered at its OWN width and then truncated -/

section trunc
variable {E : IEnv} {elems : List (String × Nat)}

theorem ie_resize_trunc {e : PExpr} (hcl : e.constLeaf = false) {W cw : Nat}
    (hs : selfWidth2 E elems e = some W) (h : ¬ W < cw) (m : Nat) :
    instExpr2 E elems (some cw) (.resize m e) = .resize cw (instExpr2 E elems (some W) e) := by
  simp [instExpr2, hs, h, hcl]

/-- … and the same marker with the context WIDER than the node (a design whose widths coincide with the
default point only at the default point): the marker is transparent, the carry survives -/
theorem ie_resize_widen {e : PExpr} (hcp : e.ctxPropagates = true) {W cw : Nat}
    (hs : selfWidth2 E elems e = some W) (h : W < cw) (m : Nat) :
    instExpr2 E elems (some cw) (.resize m e) = instExpr2 E elems (some cw) e := by
  simp [instExpr2, hs, h, hcp]

end trunc

#print axioms ashape
#print axioms ie_resize_leaf

end LeanModels.Sv.B2

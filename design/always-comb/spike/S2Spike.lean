import LeanModels.Sv.CombProcEq

/-!
S2.0 spike (WP-G step 2, gate 1a). Scratch file, compiled against the BUILT oleans of the worktree; no tree edit.

A. the per-constructor `instExpr2` / `selfWidth2` / `rigidMax2` equation lemmas the combined shape theorem
   `skT_shape` will rest on (`bnot`, `lnot`, `?:`, `&&`/`||`, reductions);
B. the S2 arms over LEAF operands, against the real library (`leaf_eq`, `leaf_fit`);
C. the two ingredients that are new for operands that are gate TREES: `rigidMax2 v = some w` (fact R) and the
   general-width `instExpr2 none v = low` (fact I0, `cond_shape` with `1` replaced by `w`), plus the
   dummy-width mechanism `Sk.low sigma t1 = Sk.low sigma t2` on fill-free skeletons;
D. two composite arms: `~(gate tree)` and `c ? t : e` over gate trees, through the real `gate_shape`/`cond_shape`.
-/

namespace LeanModels.Sv
open CombView CombEq

/-! ## A. equation lemmas -/

section eqns
variable {env : IEnv} {elems : List (String × Nat)}

theorem ie_lnot (ctx : Option Nat) (a : PExpr) :
    instExpr2 env elems ctx (.unary (.m0 .lnot) a) = .unary .lnot (instExpr2 env elems none a) := by
  simp [instExpr2]

theorem ie_bnot_some (w : Nat) (a : PExpr) (h : (rigidMax2 env elems a).getD w ≤ w) :
    instExpr2 env elems (some w) (.unary (.m0 .bnot) a) =
      .unary .bnot (fitExpr2 env elems (some w) a) := by
  simp [instExpr2, h]

theorem ie_bnot_none (a : PExpr) :
    instExpr2 env elems none (.unary (.m0 .bnot) a) =
      .unary .bnot (instExpr2 env elems (selfWidth2 env elems a) a) := by
  simp [instExpr2]

theorem ie_ternary_some (w : Nat) (c t e : PExpr) :
    instExpr2 env elems (some w) (.ternary c t e) =
      .ternary (instExpr2 env elems none c) (fitExpr2 env elems (some w) t)
        (fitExpr2 env elems (some w) e) := by
  simp [instExpr2]

theorem ie_ternary_none (w : Nat) (c t e : PExpr)
    (ht : selfWidth2 env elems t = some w) (he : selfWidth2 env elems e = some w) :
    instExpr2 env elems none (.ternary c t e) =
      .ternary (instExpr2 env elems none c) (fitExpr2 env elems (some w) t)
        (fitExpr2 env elems (some w) e) := by
  simp [instExpr2, ht, he]

theorem ie_land (ctx : Option Nat) (l r : PExpr) :
    instExpr2 env elems ctx (.binary .land l r) =
      .logical true (instExpr2 env elems (selfWidth2 env elems l) l)
        (instExpr2 env elems (selfWidth2 env elems r) r) := by
  simp [instExpr2] <;> rfl

theorem ie_lor (ctx : Option Nat) (l r : PExpr) :
    instExpr2 env elems ctx (.binary .lor l r) =
      .logical false (instExpr2 env elems (selfWidth2 env elems l) l)
        (instExpr2 env elems (selfWidth2 env elems r) r) := by
  simp [instExpr2] <;> rfl

theorem ie_reduce (ctx : Option Nat) (op : RedOp) (a : PExpr) :
    instExpr2 env elems ctx (.reduce op a) =
      .reduce op (instExpr2 env elems (selfWidth2 env elems a) a) := by
  simp [instExpr2]

theorem sw_lnot (a : PExpr) : selfWidth2 env elems (.unary (.m0 .lnot) a) = some 1 := by
  simp [selfWidth2]

theorem sw_bnot (a : PExpr) :
    selfWidth2 env elems (.unary (.m0 .bnot) a) = selfWidth2 env elems a := by
  simp [selfWidth2]

theorem sw_land (l r : PExpr) : selfWidth2 env elems (.binary .land l r) = some 1 := by
  simp [selfWidth2]

theorem sw_lor (l r : PExpr) : selfWidth2 env elems (.binary .lor l r) = some 1 := by
  simp [selfWidth2]

theorem sw_reduce (op : RedOp) (a : PExpr) : selfWidth2 env elems (.reduce op a) = some 1 := by
  simp [selfWidth2]

theorem sw_ternary (w : Nat) (c t e : PExpr)
    (ht : selfWidth2 env elems t = some w) (he : selfWidth2 env elems e = some w) :
    selfWidth2 env elems (.ternary c t e) = some w := by
  simp [selfWidth2, ht, he]

theorem rm_bnot (a : PExpr) :
    rigidMax2 env elems (.unary (.m0 .bnot) a) = rigidMax2 env elems a := by
  simp [rigidMax2]

theorem rm_lnot (a : PExpr) : rigidMax2 env elems (.unary (.m0 .lnot) a) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_land (l r : PExpr) : rigidMax2 env elems (.binary .land l r) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_lor (l r : PExpr) : rigidMax2 env elems (.binary .lor l r) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_reduce (op : RedOp) (a : PExpr) : rigidMax2 env elems (.reduce op a) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_ternary (w : Nat) (c t e : PExpr)
    (ht : rigidMax2 env elems t = some w) (he : rigidMax2 env elems e = some w) :
    rigidMax2 env elems (.ternary c t e) = some w := by
  simp [rigidMax2, ht, he]

end eqns

/-! ## B. the arms over leaf operands -/

section leaf
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

theorem rm_leaf {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a) :
    rigidMax2 E elems e = selfWidth2 E elems e := by
  cases e <;> simp [leafRd?, rigidMax2] at h ⊢

theorem bnot_leaf (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a) {w : Nat}
    (hw : (a.win σ dw).2.2 = w) :
    fitExpr2 E elems (some w) (.unary (.m0 .bnot) e) = .unary .bnot (accExpr σ a) := by
  obtain ⟨hsw, hin, hrig⟩ := leaf_eq C hdw h ha
  rw [fitExpr2_of_not_rigid w rfl, ie_bnot_some w e (by rw [rm_leaf h, hsw, hw]; simp),
    leaf_fit C hdw h ha hw]

theorem lnot_leaf (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a) (ctx : Option Nat) :
    instExpr2 E elems ctx (.unary (.m0 .lnot) e) = .unary .lnot (accExpr σ a) := by
  rw [ie_lnot, (leaf_eq C hdw h ha).2.1 none]

theorem tern_leaves (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {c t f : PExpr}
    {ac aa ab : Acc} (hc : leafRd? ds c = .ok ac) (ht : leafRd? ds t = .ok aa)
    (hf : leafRd? ds f = .ok ab) (hac : AccOK σ DW DG EW ns ac) (haa : AccOK σ DW DG EW ns aa)
    (hab : AccOK σ DW DG EW ns ab) {w : Nat} (hwt : (aa.win σ dw).2.2 = w)
    (hwf : (ab.win σ dw).2.2 = w) :
    fitExpr2 E elems (some w) (.ternary c t f) =
      .ternary (accExpr σ ac) (accExpr σ aa) (accExpr σ ab) := by
  rw [fitExpr2_of_not_rigid w rfl, ie_ternary_some, (leaf_eq C hdw hc hac).2.1 none,
    leaf_fit C hdw ht haa hwt, leaf_fit C hdw hf hab hwf]

theorem land_leaves (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {l r : PExpr}
    {aa ab : Acc} (hl : leafRd? ds l = .ok aa) (hr : leafRd? ds r = .ok ab)
    (haa : AccOK σ DW DG EW ns aa) (hab : AccOK σ DW DG EW ns ab) (ctx : Option Nat) :
    instExpr2 E elems ctx (.binary .land l r) = .logical true (accExpr σ aa) (accExpr σ ab) := by
  rw [ie_land, (leaf_eq C hdw hl haa).2.1, (leaf_eq C hdw hr hab).2.1]

theorem red_leaf (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a) (op : RedOp) :
    fitExpr2 E elems (some 1) (.reduce op e) = .reduce op (accExpr σ a) := by
  rw [fitExpr2_of_rigid_eq (rigidExpr_reduce op e) (sw_reduce op e), ie_reduce,
    (leaf_eq C hdw h ha).2.1]

/-! ## C. new ingredients for operands that are gate trees -/

/-- (R) `rigidMax2` of a gate tree whose skeleton fits width `tw` is `tw`. -/
theorem rm_gate (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ∀ tw, (skT v rs).WidthOk σ dw tw →
        rigidMax2 E elems v = some tw
  | .lit lv, rs, h, _, _, tw, hw => by
      simp only [rdsOf?, Except.ok.injEq] at h
      subst h
      simp only [skT, Sk.WidthOk] at hw
      simp [rigidMax2, hw]
  | .binary op l r, rs, h, hf, hacc, tw, hw => by
      simp only [fragG, Bool.and_eq_true] at hf
      simp only [rdsOf?] at h
      rcases hg : gateOf op with _ | b
      · simp [hg] at h
      · rcases hl : rdsOf? ds l with e1 | ra
        · simp [hg, hl] at h
        · rcases hr : rdsOf? ds r with e2 | rb
          · simp [hg, hl, hr] at h
          · simp only [hg, hl, hr, Except.ok.injEq] at h
            subst h
            obtain ⟨rfl, hb⟩ := gateOf_cases hg
            have hla := rdsOf?_len l ra hl hf.1
            have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
            have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
            have ihl := rm_gate C hdw l ra hl hf.1
              (fun a ha => hacc a (List.mem_append_left _ ha)) tw
            have ihr := rm_gate C hdw r rb hr hf.2
              (fun a ha => hacc a (List.mem_append_right _ ha)) tw
            rcases hb with rfl | rfl | rfl <;>
              simp only [skT, hg, e1, e2, mkGate, Sk.WidthOk] at hw <;>
              simp [rigidMax2, ihl hw.1, ihr hw.2]
  | .ident n, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk] at hw
      rw [rm_leaf hl, (leaf_eq C hdw hl (hacc a (by simp))).1, hw]
  | .bitSel b i, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk] at hw
      rw [rm_leaf hl, (leaf_eq C hdw hl (hacc a (by simp))).1, hw]
  | .arrayElem n is, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk] at hw
      rw [rm_leaf hl, (leaf_eq C hdw hl (hacc a (by simp))).1, hw]
  | .arrayPart n is m a b, rs, h, _, hacc, tw, hw => by
      obtain ⟨a', hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk] at hw
      rw [rm_leaf hl, (leaf_eq C hdw hl (hacc a' (by simp))).1, hw]
  | .concat _, _, _, hf, _, _, _ => by simp [fragG] at hf
  | .fill _, _, _, hf, _, _, _ => by simp [fragG] at hf
  | .paramRef .., rs, h, _, _, _, _ | .genvarRef .., rs, h, _, _, _, _
  | .enumRef .., rs, h, _, _, _, _
  | .int .., rs, h, _, _, _, _ | .unary .., rs, h, _, _, _, _ | .ternary .., rs, h, _, _, _, _
  | .resize .., rs, h, _, _, _, _ | .signedResize .., rs, h, _, _, _, _
  | .squash2 .., rs, h, _, _, _, _
  | .sysCall .., rs, h, _, _, _, _ | .partSel .., rs, h, _, _, _, _ | .repl .., rs, h, _, _, _, _
  | .reduce .., rs, h, _, _, _, _ | .cast .., rs, h, _, _, _, _
  | .unsupported .., rs, h, _, _, _, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

/-- (I0, general width) `cond_shape` with `1` replaced by the operand's own width `tw`. -/
theorem cond_shape_w (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ∀ tw, (skT v rs).WidthOk σ dw tw →
        instExpr2 E elems none v = (skT v rs).low σ tw
  | .lit lv, rs, h, _, _, tw, hw => by
      simp only [rdsOf?, Except.ok.injEq] at h
      subst h
      simp [skT, Sk.low]
  | .binary op l r, rs, h, hf, hacc, tw, hw => by
      simp only [fragG, Bool.and_eq_true] at hf
      simp only [rdsOf?] at h
      rcases hg : gateOf op with _ | b
      · simp [hg] at h
      · rcases hl : rdsOf? ds l with e1 | ra
        · simp [hg, hl] at h
        · rcases hr : rdsOf? ds r with e2 | rb
          · simp [hg, hl, hr] at h
          · simp only [hg, hl, hr, Except.ok.injEq] at h
            subst h
            obtain ⟨rfl, hb⟩ := gateOf_cases hg
            have hla := rdsOf?_len l ra hl hf.1
            have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
            have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
            have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a :=
              fun a ha => hacc a (List.mem_append_left _ ha)
            have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a :=
              fun a ha => hacc a (List.mem_append_right _ ha)
            have hw' : (skT l ra).WidthOk σ dw tw ∧ (skT r rb).WidthOk σ dw tw := by
              rcases hb with rfl | rfl | rfl <;>
                simpa only [skT, hg, e1, e2, mkGate, Sk.WidthOk] using hw
            have hsl := skT_selfWidth C hdw l ra hl hf.1 hacl tw hw'.1
            have hsr := skT_selfWidth C hdw r rb hr hf.2 hacr tw hw'.2
            have ihl := gate_shape C hdw l ra hl hf.1 hacl tw hw'.1
            have ihr := gate_shape C hdw r rb hr hf.2 hacr tw hw'.2
            rw [instExpr2_gate_none b hb l r tw hsl hsr, ihl, ihr]
            rcases hb with rfl | rfl | rfl <;>
              simp [skT, hg, e1, e2, mkGate, Sk.low, Gate.op]
  | .ident n, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.low]
      exact (leaf_eq C hdw hl (hacc a (by simp))).2.1 none
  | .bitSel b i, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.low]
      exact (leaf_eq C hdw hl (hacc a (by simp))).2.1 none
  | .arrayElem n is, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.low]
      exact (leaf_eq C hdw hl (hacc a (by simp))).2.1 none
  | .arrayPart n is m a b, rs, h, _, hacc, tw, hw => by
      obtain ⟨a', hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.low]
      exact (leaf_eq C hdw hl (hacc a' (by simp))).2.1 none
  | .concat _, _, _, hf, _, _, _ => by simp [fragG] at hf
  | .fill _, _, _, hf, _, _, _ => by simp [fragG] at hf
  | .paramRef .., rs, h, _, _, _, _ | .genvarRef .., rs, h, _, _, _, _
  | .enumRef .., rs, h, _, _, _, _
  | .int .., rs, h, _, _, _, _ | .unary .., rs, h, _, _, _, _ | .ternary .., rs, h, _, _, _, _
  | .resize .., rs, h, _, _, _, _ | .signedResize .., rs, h, _, _, _, _
  | .squash2 .., rs, h, _, _, _, _
  | .sysCall .., rs, h, _, _, _, _ | .partSel .., rs, h, _, _, _, _ | .repl .., rs, h, _, _, _, _
  | .reduce .., rs, h, _, _, _, _ | .cast .., rs, h, _, _, _, _
  | .unsupported .., rs, h, _, _, _, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

/-! ## D. composite arms through the real `gate_shape` / `cond_shape_w` -/

theorem bnot_gate (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {v : PExpr}
    {rs : List Acc} (hrd : rdsOf? ds v = .ok rs) (hf : fragG v = true)
    (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) {tw : Nat} (hw : (skT v rs).WidthOk σ dw tw) :
    fitExpr2 E elems (some tw) (.unary (.m0 .bnot) v) = .unary .bnot ((skT v rs).low σ tw) := by
  rw [fitExpr2_of_not_rigid tw rfl,
    ie_bnot_some tw v (by rw [rm_gate C hdw v rs hrd hf hacc tw hw]; simp),
    gate_shape C hdw v rs hrd hf hacc tw hw]

theorem lnot_gate (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {v : PExpr}
    {rs : List Acc} (hrd : rdsOf? ds v = .ok rs) (hf : fragG v = true)
    (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) {w : Nat} (hw : (skT v rs).WidthOk σ dw w)
    (ctx : Option Nat) :
    instExpr2 E elems ctx (.unary (.m0 .lnot) v) = .unary .lnot ((skT v rs).low σ w) := by
  rw [ie_lnot, cond_shape_w C hdw v rs hrd hf hacc w hw]

theorem tern_gates (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {c t f : PExpr}
    {rc rt rf : List Acc} (hc : rdsOf? ds c = .ok rc) (ht : rdsOf? ds t = .ok rt)
    (hf : rdsOf? ds f = .ok rf) (gc : fragG c = true) (gt : fragG t = true) (gf : fragG f = true)
    (acc : ∀ a ∈ rc, AccOK σ DW DG EW ns a) (act : ∀ a ∈ rt, AccOK σ DW DG EW ns a)
    (acf : ∀ a ∈ rf, AccOK σ DW DG EW ns a) {tw : Nat}
    (wc : (skT c rc).WidthOk σ dw 1) (wt : (skT t rt).WidthOk σ dw tw)
    (wf : (skT f rf).WidthOk σ dw tw) :
    fitExpr2 E elems (some tw) (.ternary c t f) =
      .ternary ((skT c rc).low σ 1) ((skT t rt).low σ tw) ((skT f rf).low σ tw) := by
  rw [fitExpr2_of_not_rigid tw rfl, ie_ternary_some, cond_shape_w C hdw c rc hc gc acc 1 wc,
    gate_shape C hdw t rt ht gt act tw wt, gate_shape C hdw f rf hf gf acf tw wf]

end leaf

/-! ## E. the dummy-width mechanism on the existing `Sk` -/

namespace CombEq

/-- No `.fill` anywhere (the only constructor whose lowering reads the width argument). -/
def Sk.noFill : Sk → Bool
  | .lit _ => true
  | .rd _ => true
  | .gate _ l r => l.noFill && r.noFill
  | .cat _ => true
  | .fill _ => false

theorem Sk.low_irrel (σ : String → Int) :
    ∀ (sk : Sk), sk.noFill = true → ∀ t1 t2, sk.low σ t1 = sk.low σ t2
  | .lit _, _, _, _ => rfl
  | .rd _, _, _, _ => rfl
  | .gate g l r, h, t1, t2 => by
      simp only [Sk.noFill, Bool.and_eq_true] at h
      simp only [Sk.low, Sk.low_irrel σ l h.1 t1 t2, Sk.low_irrel σ r h.2 t1 t2]
  | .cat _, _, _, _ => rfl
  | .fill _, h, _, _ => by simp [Sk.noFill] at h

/-- The skeleton of an accepted gate tree has no `.fill` (the recognizer never produces one). -/
theorem skT_noFill {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true → (skT v rs).noFill = true
  | .lit _, rs, h, _ => by simp [rdsOf?] at h; subst h; simp [skT, Sk.noFill]
  | .binary op l r, rs, h, hf => by
      simp only [fragG, Bool.and_eq_true] at hf
      simp only [rdsOf?] at h
      rcases hg : gateOf op with _ | b
      · simp [hg] at h
      · rcases hl : rdsOf? ds l with e1 | ra
        · simp [hg, hl] at h
        · rcases hr : rdsOf? ds r with e2 | rb
          · simp [hg, hl, hr] at h
          · simp only [hg, hl, hr, Except.ok.injEq] at h
            subst h
            have hla := rdsOf?_len l ra hl hf.1
            obtain ⟨-, hb⟩ := gateOf_cases hg
            have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
            have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
            rcases hb with rfl | rfl | rfl <;>
              simp [skT, hg, e1, e2, mkGate, Sk.noFill, skT_noFill l ra hl hf.1, skT_noFill r rb hr hf.2]
  | .ident n, rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h; subst h; simp [skT, Sk.noFill]
  | .bitSel b i, rs, h, _ => by
      have h' : rdsLeaf? ds (.bitSel b i) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.bitSel b i) with m | a
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [skT, Sk.noFill]
  | .arrayElem n is, rs, h, _ => by
      have h' : rdsLeaf? ds (.arrayElem n is) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.arrayElem n is) with m | a
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [skT, Sk.noFill]
  | .arrayPart n is m a b, rs, h, _ => by
      have h' : rdsLeaf? ds (.arrayPart n is m a b) = .ok rs := by simpa [rdsOf?] using h
      unfold rdsLeaf? at h'
      rcases hl : leafRd? ds (.arrayPart n is m a b) with m' | a'
      · simp [hl] at h'
      · simp only [hl, Except.ok.injEq] at h'; subst h'; simp [skT, Sk.noFill]
  | .concat _, _, _, hf => by simp [fragG] at hf
  | .fill _, _, _, hf => by simp [fragG] at hf
  | .paramRef .., rs, h, _ | .genvarRef .., rs, h, _ | .enumRef .., rs, h, _
  | .int .., rs, h, _ | .unary .., rs, h, _ | .ternary .., rs, h, _
  | .resize .., rs, h, _ | .signedResize .., rs, h, _ | .squash2 .., rs, h, _
  | .sysCall .., rs, h, _ | .partSel .., rs, h, _ | .repl .., rs, h, _
  | .reduce .., rs, h, _ | .cast .., rs, h, _ | .unsupported .., rs, h, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

end CombEq


/-! ## F. the Expr2-level facts (x-free fragment) the `low_xf*` arms need -/

namespace XF

theorem any_one (f : Nat → Bool) : any 1 f = f 0 := by
  simp only [any]
  cases h : f 0 <;> simp [h]

theorem any_congr {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) : any w f = any w g := by
  simp only [any]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨k, hk, hf⟩; exact ⟨k, hk, by rw [← h k hk]; exact hf⟩
  · rintro ⟨k, hk, hf⟩; exact ⟨k, hk, by rw [h k hk]; exact hf⟩

theorem all_congr {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) : all w f = all w g := by
  simp only [all]
  apply decide_eq_decide.mpr
  constructor
  · intro hf k hk; rw [← h k hk]; exact hf k hk
  · intro hf k hk; rw [h k hk]; exact hf k hk

theorem parity_congr {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) :
    parity w f = parity w g := by
  have : (fun i : Fin w => f i.val) = fun i => g i.val := funext fun i => h i.val i.isLt
  simp only [parity, this]

theorem red_congr (op : RedOp) {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) :
    red op w f = red op w g := by
  cases op <;> simp [red, any_congr h, all_congr h, parity_congr h]

end XF

section xf
variable {m : Design2}

theorem xf_lnot {e : Expr2} {w : Nat} (h : e.xfWidth m = some w) :
    (Expr2.unary .lnot e).xfWidth m = some 1 := by
  simp [Expr2.xfWidth, h]

theorem xfb_lnot {e : Expr2} {w : Nat} (h : e.xfWidth m = some w) (env : String → Nat → Bool)
    (k : Nat) : (Expr2.unary .lnot e).xfBits m env k = !XF.any w (e.xfBits m env) := by
  simp [Expr2.xfBits, h]

theorem xf_red {e : Expr2} {w : Nat} (op : RedOp) (h : e.xfWidth m = some w) :
    (Expr2.reduce op e).xfWidth m = some 1 := by
  simp [Expr2.xfWidth, h]

theorem xfb_red {e : Expr2} {w : Nat} (op : RedOp) (h : e.xfWidth m = some w)
    (env : String → Nat → Bool) (k : Nat) :
    (Expr2.reduce op e).xfBits m env k = XF.red op w (e.xfBits m env) := by
  simp [Expr2.xfBits, h]

theorem xf_logical {l r : Expr2} {wl wr : Nat} (b : Bool) (hl : l.xfWidth m = some wl)
    (hr : r.xfWidth m = some wr) : (Expr2.logical b l r).xfWidth m = some 1 := by
  simp [Expr2.xfWidth, hl, hr]

theorem xfb_logical {l r : Expr2} {wl wr : Nat} (b : Bool) (hl : l.xfWidth m = some wl)
    (hr : r.xfWidth m = some wr) (env : String → Nat → Bool) (k : Nat) :
    (Expr2.logical b l r).xfBits m env k =
      if b then (XF.any wl (l.xfBits m env) && XF.any wr (r.xfBits m env))
      else (XF.any wl (l.xfBits m env) || XF.any wr (r.xfBits m env)) := by
  simp [Expr2.xfBits, hl, hr]

theorem xf_tern {c t f : Expr2} {w : Nat} (hc : c.xfWidth m = some 1) (ht : t.xfWidth m = some w)
    (hf : f.xfWidth m = some w) : (Expr2.ternary c t f).xfWidth m = some w := by
  simp [Expr2.xfWidth, hc, ht, hf, XF.same]

theorem xfb_tern {c t f : Expr2} (hc : c.xfWidth m = some 1) (env : String → Nat → Bool) (k : Nat) :
    (Expr2.ternary c t f).xfBits m env k =
      if c.xfBits m env 0 = true then t.xfBits m env k else f.xfBits m env k := by
  simp [Expr2.xfBits, hc, XF.any_one]

theorem xf_bnot {e : Expr2} {w : Nat} (h : e.xfWidth m = some w) :
    (Expr2.unary .bnot e).xfWidth m = some w := by
  simp [Expr2.xfWidth, h]

end xf

/-- info: 'LeanModels.Sv.bnot_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bnot_gate

/-- info: 'LeanModels.Sv.tern_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tern_gates

end LeanModels.Sv

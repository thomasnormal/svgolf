import LeanModels.Sv.CombProcEq

/-!
B2 spike, part 2a (scratch, no tree edit): THE INSTANCE FACT for a `Resize` marker over an access leaf.
`instExpr2` at a context `cw` of `.resize m e` (e a leaf the recognizer accepts) is `.resize cw (accExpr σ a)`,
for every `m` (the envelope's default-point metadata) and EVERY relation between the leaf width and `cw`.
-/

namespace LeanModels.Sv
open CombView CombEq

section ext
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- the flags `instExpr2`'s `.resize` arm reads: a leaf is rigid, not context-propagating, not a constant leaf,
and no negative-genvar guard applies -/
theorem leaf_flags {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a) :
    e.ctxPropagates = false ∧ e.constLeaf = false ∧
      ∀ (env : IEnv) (m w : Nat), (PExpr.resize m e).negGenvarWidened env w = none := by
  cases e <;> simp [leafRd?] at h <;>
    first
    | exact ⟨rfl, rfl, fun _ _ _ => rfl⟩
    | (split at h <;> simp_all)
    | skip

/-- **The instance fact for `Sk.ext` over a leaf.** -/
theorem ie_resize_leaf (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a)
    (m cw : Nat) :
    instExpr2 E elems (some cw) (.resize m e) = .resize cw (accExpr σ a) := by
  obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw h ha
  obtain ⟨hcp, hcl, hng⟩ := leaf_flags h
  simp [instExpr2, hsw, hcp, hcl, hng, hin]

end ext
end LeanModels.Sv

#print axioms LeanModels.Sv.ie_resize_leaf

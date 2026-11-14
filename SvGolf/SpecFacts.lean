import tasks.clmul.Spec
import LeanModels.Sv.XorSum

/-!
# Facts about the tasks' own definitions (untrusted, kernel-checked)

Nothing here is part of the trusted base, and nothing here changes a statement: these are lemmas about the
definitions a task's `Spec.lean` uses to state its function, which every proof of that task needs and each
proof on the board proved for itself. They sit in the task's namespace, next to the definitions they are about.

* `clmul`: `SvGolf.Tasks.Clmul.coeff_eq` (the Spec's double fold `coeff` is the nested XOR sum `XorSum.bx`) and
  `SvGolf.Tasks.Clmul.getLsbD_ofBits` (bit `k` of the Spec's `ofBits n f` is `f k` below `n`, `false` above).
-/

namespace SvGolf.Tasks.Clmul

open LeanModels.Sv.XorSum

/-- The Spec's double sum is the nested XOR sum `bx`. -/
theorem coeff_eq (N : Nat) (a b : BitVec N) (k : Nat) :
    coeff N a b k =
      bx (fun i => bx (fun j => decide (i + j = k) && a.getLsbD i && b.getLsbD j) N) N := by
  unfold coeff
  simp only [foldl_xor]
  simp

/-- Bit `k` of `ofBits n f`. -/
theorem getLsbD_ofBits : ∀ (n : Nat) (f : Nat → Bool) (k : Nat),
    (ofBits n f).getLsbD k = (decide (k < n) && f k)
  | 0, f, k => by simp [ofBits]
  | n + 1, f, k => by
    rw [ofBits, BitVec.getLsbD_append, getLsbD_ofBits n]
    cases k with
    | zero => simp
    | succ k => simp

/-- Bit `k < n` of `ofBits n f` is `f k`. -/
theorem getLsbD_ofBits_lt {n k : Nat} {f : Nat → Bool} (hk : k < n) : (ofBits n f).getLsbD k = f k := by
  rw [getLsbD_ofBits]
  simp [hk]

#print axioms coeff_eq
#print axioms getLsbD_ofBits

end SvGolf.Tasks.Clmul

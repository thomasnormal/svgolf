import spec.IEEE754

/-!
# The format boundary of the parametric `fdiv` task (compiled facts)

`FORMAT.md` states the well-formedness predicate and the quantities a parametric divider may rely on. This file
proves the arithmetic facts that the design and its proof will use, for EVERY `Format` (symbolic in `w` and `p`),
from the structure's own side conditions `Format.hw : 2 ≤ w` and `Format.hp : 2 ≤ p`. Untrusted, kernel-checked;
no `sorry`, no `native_decide`.
-/

namespace SvGolf.FdivParam

open SvGolf.IEEE754

/-- The task's range: exactly the spec's well-formedness, nothing more (no upper bound on `w` or `p`). -/
def FormatOK (w p : Nat) : Prop := 2 ≤ w ∧ 2 ≤ p

instance (w p : Nat) : Decidable (FormatOK w p) := by unfold FormatOK; infer_instance

/-- A `Format` is a pair of well-formed parameters (the converse builds the structure). -/
theorem formatOK_of (f : Format) : FormatOK f.w f.p := ⟨f.hw, f.hp⟩

/-- The storage width is `w + p` (the module's port width `K = W + P`). -/
theorem k_eq (f : Format) : f.k = f.w + f.p := by
  have := f.hp
  simp only [Format.k, Format.t]
  omega

/-- The trailing significand field is non-empty. -/
theorem t_pos (f : Format) : 1 ≤ f.t := by
  have := f.hp
  simp only [Format.t]
  omega

/-- The exponent bias `emax = 2^(w-1) - 1` is at least 1. -/
theorem emax_pos' (f : Format) : 1 ≤ f.emax := by
  have hw := f.hw
  have h : 2 ^ 1 ≤ 2 ^ (f.w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [Format.emax]
  omega

/-- One unit `2^qmin` is a positive number of units: `scale = emax + p - 2 ≥ 1`. -/
theorem scale_pos (f : Format) : 1 ≤ f.scale := by
  have := emax_pos' f
  have := f.hp
  simp only [Format.scale, Format.t]
  omega

/-- The format instances of the existing 16- and 32-bit tasks are well-formed (by `decide`). -/
example : FormatOK 5 11 ∧ FormatOK 8 24 ∧ FormatOK 8 8 := by decide

/-- ... and the smallest legal format `(2, 2)` has a 4-bit pattern. -/
example : (({ w := 2, p := 2 } : Format)).k = 4 := by decide

end SvGolf.FdivParam

/-! WP-H2 gate 0 (compiles, 7 s, no imports): M3d, the rounding CORE of the reference, symbolically, one `omega` per literal shift. No Mathlib:
the 13 shifts are enumerated by `rcases` on an `omega`-proved disjunction. `st0 = true` and `st0 = false` are separate
statements (the sticky bit makes the tie impossible in the first). -/

namespace H2G0C

theorem sh_cases (sh : Nat) (hs : sh ≤ 12) :
    sh = 0 ∨ sh = 1 ∨ sh = 2 ∨ sh = 3 ∨ sh = 4 ∨ sh = 5 ∨ sh = 6 ∨ sh = 7 ∨ sh = 8 ∨ sh = 9 ∨ sh = 10 ∨ sh = 11 ∨
      sh = 12 := by omega

/-- `st0 = true`: the design's `inc = rb`, so `z = (qs + 1) / 2`; `z` is within half a spacing on both sides, strictly
above (the true value is strictly above `qm / 2^sh`). `M = 2^(sh+1)`. -/
theorem core_t (qm sh z : Nat) (h1 : 2048 ≤ qm) (h2 : qm < 4096) (hs : sh ≤ 12)
    (hz : z = (qm / 2 ^ sh + 1) / 2) :
    (z = 0 ∨ (2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm) ∧ 2 * qm + 2 ≤ (2 * z + 1) * 2 ^ (sh + 1) := by
  rcases sh_cases sh hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [Nat.reducePow, Nat.reduceAdd] at hz ⊢) <;> omega

/-- `st0 = false`: `inc = rb ∧ (dropped bits nonzero ∨ qs[1])`; ties (the true value exactly half) round to even. -/
theorem core_f (qm sh z : Nat) (h1 : 2048 ≤ qm) (h2 : qm < 4096) (hs : sh ≤ 12)
    (hz : ((qm / 2 ^ sh % 2 = 1 ∧ (qm / 2 ^ sh * 2 ^ sh % 4096 ≠ qm ∨ qm / 2 ^ sh / 2 % 2 = 1)) ∧
            z = qm / 2 ^ sh / 2 + 1) ∨
          (¬ (qm / 2 ^ sh % 2 = 1 ∧ (qm / 2 ^ sh * 2 ^ sh % 4096 ≠ qm ∨ qm / 2 ^ sh / 2 % 2 = 1)) ∧
            z = qm / 2 ^ sh / 2)) :
    (z = 0 ∨ ((2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm ∧ (z % 2 = 1 → (2 * z - 1) * 2 ^ (sh + 1) < 2 * qm))) ∧
    2 * qm ≤ (2 * z + 1) * 2 ^ (sh + 1) ∧ (z % 2 = 1 → 2 * qm < (2 * z + 1) * 2 ^ (sh + 1)) := by
  rcases sh_cases sh hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [Nat.reducePow, Nat.reduceAdd] at hz ⊢) <;> omega

end H2G0C

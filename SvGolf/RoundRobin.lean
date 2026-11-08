/-!
# Round-robin arbitration facts (untrusted, kernel-checked; svGolf's shared proof library)

Nothing here is part of the trusted base. Word-level facts any round-robin arbiter proof uses, for
every width `w` (structure-preserving: no width is unrolled), stated on `BitVec` only (no task, no
design):

* **The lowest set bit** (`IsLow`, `getLsbD_isolate`, `isolate_eq_twoPow`, `isolate_eq_zero`):
  `s &&& (~~~s + 1)` is the one-hot of the lowest set bit of `s`, and zero exactly when `s` is.
  The carry argument is core's `BitVec.carry_succ_one`.
* **The thermometer above a one-hot** (`getLsbD_thermo`): `~~~((twoPow w k <<< 1) - 1)` has bit `i`
  exactly when `k < i < w` (the clients above the last grant).
* **The mask round-robin** (`pick`, `next`, `Thermo`, `step`): the pick of a request vector `x` under
  a thermometer mask `m` with its edge at `e` (the lowest masked requester, else the lowest
  requester), the next mask, and the one-step theorem: the pick is zero exactly when `x` is, is one
  bit of `x` at most, the next mask is a thermometer again, and a requester that is not picked gets
  strictly closer to the edge in the cyclic distance `dist` (the ranking of a bounded-response
  proof, `SvGolf.React`). `dist_le`: the distance is at most `w - 1`.
-/

namespace SvGolf.RoundRobin

/-! ## Least witnesses (core has no `Nat.find`) -/

/-- A predicate with a witness at or below `n` has a least witness. -/
theorem exists_least {P : Nat → Prop} :
    ∀ n, (∃ j, j ≤ n ∧ P j) → ∃ i, P i ∧ ∀ j, j < i → ¬ P j
  | 0, ⟨j, hj, hp⟩ => ⟨j, hp, fun k hk => absurd hk (by omega)⟩
  | n + 1, ⟨j, hj, hp⟩ => by
    by_cases h : ∃ j, j ≤ n ∧ P j
    · exact exists_least n h
    · exact ⟨j, hp, fun k hk hk' => h ⟨k, by omega, hk'⟩⟩

/-! ## The lowest set bit -/

/-- Bit `i` is the lowest set bit of `s`. -/
def IsLow {w : Nat} (s : BitVec w) (i : Nat) : Prop :=
  s.getLsbD i = true ∧ ∀ j, j < i → s.getLsbD j = false

theorem IsLow.lt {w : Nat} {s : BitVec w} {i : Nat} (h : IsLow s i) : i < w :=
  BitVec.lt_of_getLsbD h.1

theorem IsLow.unique {w : Nat} {s : BitVec w} {i j : Nat} (hi : IsLow s i) (hj : IsLow s j) :
    i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd (hi.1.symm.trans (hj.2 i h)) (by decide)
  · exact h
  · exact absurd (hj.1.symm.trans (hi.2 j h)) (by decide)

/-- A nonzero vector has a lowest set bit. -/
theorem exists_isLow {w : Nat} {s : BitVec w} (h : s ≠ 0#w) : ∃ k, IsLow s k := by
  have hex : ∃ i, s.getLsbD i = true := by
    refine Classical.byContradiction fun hn => h ?_
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [BitVec.getLsbD_zero]
    cases hb : s.getLsbD i
    · rfl
    · exact absurd ⟨i, hb⟩ hn
  obtain ⟨i, hi⟩ := hex
  obtain ⟨k, hk, hmin⟩ :=
    exists_least (P := fun j => s.getLsbD j = true) i ⟨i, Nat.le_refl _, hi⟩
  refine ⟨k, hk, fun j hj => ?_⟩
  cases hb : s.getLsbD j
  · rfl
  · exact absurd hb (hmin j hj)

/-- **`s &&& (~~~s + 1)` isolates the lowest set bit**: its bit `i` is set exactly when bit `i` is
the lowest set bit of `s`. -/
theorem getLsbD_isolate {w : Nat} (s : BitVec w) (i : Nat) :
    (s &&& (~~~s + 1#w)).getLsbD i = true ↔ IsLow s i := by
  rw [BitVec.getLsbD_and, Bool.and_eq_true]
  cases hs : s.getLsbD i with
  | false =>
    exact ⟨fun h => absurd h.1 (by decide), fun h => absurd (h.1.symm.trans hs) (by decide)⟩
  | true =>
    have hi : i < w := BitVec.lt_of_getLsbD hs
    rw [BitVec.getLsbD_add hi]
    cases i with
    | zero =>
      have h1 : (~~~s).getLsbD 0 = false := by rw [BitVec.getLsbD_not, hs]; simp
      have h2 : (1#w).getLsbD 0 = true := by rw [BitVec.getLsbD_one]; simp [hi]
      rw [h1, h2, BitVec.carry_zero]
      exact ⟨fun _ => ⟨hs, fun j hj => absurd hj (Nat.not_lt_zero j)⟩, fun _ => ⟨rfl, rfl⟩⟩
    | succ i =>
      have h1 : (~~~s).getLsbD (i + 1) = false := by rw [BitVec.getLsbD_not, hs]; simp
      have h2 : (1#w).getLsbD (i + 1) = false := by rw [BitVec.getLsbD_one]; simp
      have hc : BitVec.carry (i + 1) (~~~s) (1#w) false = true ↔
          ∀ j, j < i + 1 → s.getLsbD j = false := by
        rw [BitVec.carry_succ_one _ _ (by omega), decide_eq_true_iff]
        constructor
        · intro h j hj
          have hnot := h j (by omega)
          cases hb : s.getLsbD j with
          | false => rfl
          | true => rw [BitVec.getLsbD_not, hb] at hnot; simp at hnot
        · intro h j hj
          rw [BitVec.getLsbD_not, h j (by omega)]
          simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
          omega
      rw [h1, h2, Bool.false_xor, Bool.false_xor, hc]
      exact ⟨fun h => ⟨hs, h.2⟩, fun h => ⟨rfl, h.2⟩⟩

/-- The isolated lowest set bit is a `twoPow`. -/
theorem isolate_eq_twoPow {w : Nat} {s : BitVec w} {k : Nat} (h : IsLow s k) :
    s &&& (~~~s + 1#w) = BitVec.twoPow w k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_twoPow]
  cases hb : (s &&& (~~~s + 1#w)).getLsbD i with
  | true =>
    have hki : k = i := h.unique ((getLsbD_isolate s i).1 hb)
    rw [hki]; simp [hi]
  | false =>
    have hki : k ≠ i := fun hki => by
      rw [← hki, (getLsbD_isolate s k).2 h] at hb
      exact absurd hb (by decide)
    simp [hki]

/-- The isolated lowest set bit is zero exactly when the vector is. -/
theorem isolate_eq_zero {w : Nat} {s : BitVec w} : s &&& (~~~s + 1#w) = 0#w ↔ s = 0#w := by
  constructor
  · intro h
    refine Classical.byContradiction fun hs => ?_
    obtain ⟨k, hk⟩ := exists_isLow hs
    have hb := (getLsbD_isolate s k).2 hk
    rw [h, BitVec.getLsbD_zero] at hb
    exact absurd hb (by decide)
  · rintro rfl
    simp

/-! ## The thermometer above a one-hot -/

theorem toNat_shl_sub_one {w k : Nat} (hk : k < w) :
    ((BitVec.twoPow w k <<< 1) - 1#w).toNat = 2 ^ (k + 1) - 1 := by
  have hw : 0 < w := by omega
  have h1 : (1#w).toNat = 1 := BitVec.toNat_one hw
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_twoPow_of_lt hk, h1, Nat.shiftLeft_eq,
    Nat.pow_one, ← Nat.pow_succ, Nat.succ_eq_add_one]
  have hp : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hpw : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  rcases Nat.lt_or_ge (k + 1) w with hlt | hge
  · have hlt' : 2 ^ (k + 1) < 2 ^ w := Nat.pow_lt_pow_right (by decide) hlt
    rw [Nat.mod_eq_of_lt hlt', show 2 ^ w - 1 + 2 ^ (k + 1) = (2 ^ (k + 1) - 1) + 2 ^ w by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · have he : k + 1 = w := by omega
    rw [he, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]

/-- **The thermometer above bit `k`**: `~~~((twoPow w k <<< 1) - 1)` has bit `i` exactly when
`k < i < w`. -/
theorem getLsbD_thermo {w k : Nat} (hk : k < w) (i : Nat) :
    (~~~((BitVec.twoPow w k <<< 1) - 1#w)).getLsbD i = decide (i < w ∧ k < i) := by
  rw [BitVec.getLsbD_not, ← BitVec.testBit_toNat ((BitVec.twoPow w k <<< 1) - 1#w),
    toNat_shl_sub_one hk, Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < w <;> by_cases h2 : k < i <;> by_cases h3 : i < k + 1 <;>
    simp [h1, h2, h3] <;> omega

/-! ## The mask round-robin -/

/-- `m` is the thermometer code with its edge at `e ≤ w`: bit `i < w` is set iff `e ≤ i`. -/
def Thermo {w : Nat} (m : BitVec w) (e : Nat) : Prop :=
  e ≤ w ∧ ∀ i, i < w → m.getLsbD i = decide (e ≤ i)

/-- All ones is the thermometer with its edge at `0`. -/
theorem thermo_allOnes (w : Nat) : Thermo (BitVec.allOnes w) 0 :=
  ⟨Nat.zero_le _, fun i hi => by simp [hi]⟩

/-- A thermometer has one edge. -/
theorem Thermo.unique {w : Nat} {m : BitVec w} {e e' : Nat} (h : Thermo m e) (h' : Thermo m e') :
    e = e' := by
  rcases Nat.lt_trichotomy e e' with hl | hl | hl
  · have hw : e < w := by have := h'.1; omega
    have h3 : decide (e ≤ e) = decide (e' ≤ e) := (h.2 e hw).symm.trans (h'.2 e hw)
    have h4 : e' ≤ e := of_decide_eq_true (h3.symm.trans (decide_eq_true (Nat.le_refl e)))
    omega
  · exact hl
  · have hw : e' < w := by have := h.1; omega
    have h3 : decide (e' ≤ e') = decide (e ≤ e') := (h'.2 e' hw).symm.trans (h.2 e' hw)
    have h4 : e ≤ e' := of_decide_eq_true (h3.symm.trans (decide_eq_true (Nat.le_refl e')))
    omega

/-- The requests the mask round-robin chooses among: the masked ones, else all of them. -/
def sel {w : Nat} (x m : BitVec w) : BitVec w := if x &&& m = 0#w then x else x &&& m

/-- **The pick of the mask round-robin**: the lowest masked requester, else the lowest requester
(the wrap). The form of `reference/rr_mask.sv`'s `pick`. -/
def pick {w : Nat} (x m : BitVec w) : BitVec w :=
  if x &&& m = 0#w then x &&& (~~~x + 1#w) else (x &&& m) &&& (~~~(x &&& m) + 1#w)

/-- **The next mask**: the thermometer above the pick, or the same mask when nothing is picked. -/
def next {w : Nat} (x m : BitVec w) : BitVec w :=
  if pick x m = 0#w then m else ~~~((pick x m <<< 1) - 1#w)

/-- The cyclic distance of client `i` from the edge `e` (the clients `e, e+1, …, w-1, 0, …` in
order of priority). -/
def dist (w e i : Nat) : Nat := if e ≤ i then i - e else i + w - e

theorem dist_le {w e i : Nat} (he : e ≤ w) (hi : i < w) : dist w e i ≤ w - 1 := by
  unfold dist; split <;> omega

theorem pick_eq_isolate {w : Nat} (x m : BitVec w) :
    pick x m = sel x m &&& (~~~(sel x m) + 1#w) := by
  unfold pick sel
  by_cases h : x &&& m = 0#w
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem sel_eq_zero {w : Nat} {x m : BitVec w} : sel x m = 0#w ↔ x = 0#w := by
  unfold sel
  split
  · exact Iff.rfl
  · next h => exact ⟨fun h' => absurd h' h, fun hx => by subst hx; simp at h⟩

theorem sel_sub {w : Nat} {x m : BitVec w} {i : Nat} (h : (sel x m).getLsbD i = true) :
    x.getLsbD i = true := by
  unfold sel at h
  split at h
  · exact h
  · rw [BitVec.getLsbD_and, Bool.and_eq_true] at h; exact h.1

/-- The pick is zero exactly when nobody requests. -/
theorem pick_eq_zero {w : Nat} {x m : BitVec w} : pick x m = 0#w ↔ x = 0#w := by
  rw [pick_eq_isolate, isolate_eq_zero, sel_eq_zero]

theorem getLsbD_pick {w : Nat} {x m : BitVec w} {i : Nat} :
    (pick x m).getLsbD i = true ↔ IsLow (sel x m) i := by
  rw [pick_eq_isolate]; exact getLsbD_isolate _ i

/-- The pick grants requesters only. -/
theorem pick_sub {w : Nat} {x m : BitVec w} {i : Nat} (h : (pick x m).getLsbD i = true) :
    x.getLsbD i = true :=
  sel_sub (getLsbD_pick.1 h).1

/-- The pick grants at most one client. -/
theorem pick_atMostOne {w : Nat} {x m : BitVec w} {i j : Nat} (hi : (pick x m).getLsbD i = true)
    (hj : (pick x m).getLsbD j = true) : i = j :=
  (getLsbD_pick.1 hi).unique (getLsbD_pick.1 hj)

/-- **One step of the mask round-robin.** From a thermometer mask with its edge at `e`, the next
mask is a thermometer with some edge `e'`, and every requester that is not picked gets strictly
closer to the edge in the cyclic distance. -/
theorem step {w : Nat} {x m : BitVec w} {e : Nat} (hm : Thermo m e) :
    ∃ e', Thermo (next x m) e' ∧ ∀ i, i < w → x.getLsbD i = true → (pick x m).getLsbD i = false →
      dist w e' i < dist w e i := by
  by_cases hx : x = 0#w
  · refine ⟨e, ?_, fun i _ hi _ => ?_⟩
    · have hp : pick x m = 0#w := pick_eq_zero.2 hx
      unfold next; rw [if_pos hp]; exact hm
    · subst hx; rw [BitVec.getLsbD_zero] at hi; exact absurd hi (by decide)
  · have hs : sel x m ≠ 0#w := fun h => hx (sel_eq_zero.1 h)
    obtain ⟨k, hk⟩ := exists_isLow hs
    have hkw : k < w := hk.lt
    have hp : pick x m = BitVec.twoPow w k := by rw [pick_eq_isolate]; exact isolate_eq_twoPow hk
    have hp0 : pick x m ≠ 0#w := fun h => hx (pick_eq_zero.1 h)
    have he := hm.1
    refine ⟨k + 1, ⟨by omega, fun i hi => ?_⟩, fun i hi hxi hpi => ?_⟩
    · unfold next
      rw [if_neg hp0, hp, getLsbD_thermo hkw, decide_eq_decide]
      exact ⟨fun h => by omega, fun h => ⟨hi, by omega⟩⟩
    · have hik : i ≠ k := by
        intro h
        rw [h, hp, BitVec.getLsbD_twoPow] at hpi
        simp [hkw] at hpi
      by_cases hz : x &&& m = 0#w
      · rw [show sel x m = x from if_pos hz] at hk
        have hmi : m.getLsbD i = false := by
          have h0 := congrArg (fun v => v.getLsbD i) hz
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, hxi, Bool.true_and] at h0
          exact h0
        have hei : ¬ e ≤ i := by
          intro h
          rw [hm.2 i hi, decide_eq_true h] at hmi
          exact absurd hmi (by decide)
        have hki : k < i := by
          rcases Nat.lt_or_ge i k with h | h
          · have h0 := hk.2 i h
            rw [hxi] at h0
            exact absurd h0 (by decide)
          · omega
        unfold dist
        rw [if_pos (show k + 1 ≤ i by omega), if_neg hei]
        omega
      · rw [show sel x m = x &&& m from if_neg hz] at hk
        have hmk : m.getLsbD k = true := by
          have h0 := hk.1
          rw [BitVec.getLsbD_and, Bool.and_eq_true] at h0
          exact h0.2
        have hek : e ≤ k := by
          rw [hm.2 k hkw] at hmk
          exact of_decide_eq_true hmk
        by_cases hei : e ≤ i
        · have hki : k < i := by
            rcases Nat.lt_or_ge i k with h | h
            · have h0 := hk.2 i h
              rw [BitVec.getLsbD_and, hxi, hm.2 i hi, decide_eq_true hei] at h0
              exact absurd h0 (by decide)
            · omega
          unfold dist
          rw [if_pos (show k + 1 ≤ i by omega), if_pos hei]
          omega
        · unfold dist
          rw [if_neg (show ¬ (k + 1 ≤ i) by omega), if_neg hei]
          omega

end SvGolf.RoundRobin

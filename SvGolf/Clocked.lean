import LeanModels.Sv.NbaCommit
import LeanModels.Sv.SeqFamily
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2
import LeanModels.Sv.CombViewArith
import LeanModels.Sv.Lib.BitVecArith
import SvGolf.SeqV2

/-!
# Lemmas for clocked proofs (untrusted, kernel-checked)

Nothing here is part of the trusted base. These are the helper lemmas that the clocked proofs on the board
(matmul, sorter, arbiter) stated and proved for themselves, one copy per proof, in nearly the same words: here once,
for every width and size. Each section says which step of a clocked proof (`PROVING.md`, section 19) it serves.

* **The commit, register by register** (step 3): `commitNba2_eq_map` (a state of distinct names commits as
  `nbaFold` per name), `commitNba2_eq_map_of_names` (the same, when every write names one of the registers `regs`:
  the other entries are unchanged), the `nbaFold` rewrites `nbaFold_nil`, `nbaFold_cons_self`, `nbaFold_cons_ne`
  (`@[simp]`), `nbaFold_cons`, `nbaFold_ite`, `nbaFold_of_forall_ne`, `nbaFold_of_names`, the names of a queue
  (`nbaNames_of_all`, `nbaNames_append`, `nbaNames_flatMap`), and a family of window writes as one `map`
  (`flatMap_range_singleton`, `flatMap_range_rowMajor`) whose commit is `LVec.insertEntries`
  (`nbaFold_map_insertEntries`).
* **Register families, window by window** (step 3): `LVec.insertEntries_congr`, `LVec.extract_insertEntries`,
  `LVec.insertEntries_extract_self` and `LVec.eq_ofBitVec_packBV` (a vector known window by window is the packed
  vector of its windows).
* **Disjoint windows** (step 1, the one-driver rule and the FF-only profile): `ProcDisj` (the relation
  `driversOk_of_ff` and `ffDisjB_of_pairwise` take), `DrvWin.overlaps_of_ne`, `DrvWin.overlaps_rowMajor`,
  `ProcDisj.of_names`, `ProcDisj.of_nameLists`, `ProcDisj.of_units`, `ProcDisj.of_lists`, `pairwise_map_range`, `pairwise_rowMajor`, and the
  row-major index facts `rowMajor_lt`, `rowMajor_ne`, `rowMajor_div` (the column is core's `Nat.mul_add_mod_of_lt`).
* **Generate loops** (step 1): `GenItem.expand2_range_flatMap`, `GenItem.expand2_range_map`,
  `GenItem.expand2_range_map₂` (a loop `for (g = 0; g < e; g++)`, one or two deep, over one process template,
  expands to `(List.range M).map f`, or the row-major `flatMap`, from the template's instantiation lemma), and their
  forms for a bound that is a parameter (`GenItem.expand2_param_map`, `GenItem.expand2_param_map₂`).
* **Power-up** (rule 2): the tactic `powerUp_cases h with x₁ … xₙ` takes a `PowerUp d st` hypothesis apart, one
  declaration at a time (`powerUp_cons`), naming the values `x₁ … xₙ` and their width facts `w_x₁ … w_xₙ`.
* **Values**: `LVec.shl_ofBitVec` (the `<<` twin of `LVec.shr_ofBitVec`), `LVec.allKnown_l0`, `LVec.allKnown_l1`
  (the one-bit literals are known), `LVec.sext_of_extract` (the evaluated sign extension
  `{{m{v[lo+W-1]}}, v[lo +: W]}` of a known window), `Lib.setWidth_mul_signExtend` (the signed product truncated).

The names sit in sub-namespaces of `SvGolf` named after the library's own (`SvGolf.LVec`, `SvGolf.GenItem`,
`SvGolf.DrvWin`, `SvGolf.Lib`), so that after `open LeanModels.Sv SvGolf` a proof writes `LVec.shl_ofBitVec` or
`GenItem.expand2_range_map`, the names they would have in `LeanModels.Sv`.
-/

namespace SvGolf

open LeanModels.Sv

set_option autoImplicit false

/-! ## 1. The commit, register by register -/

/-- Committing no write leaves the register. -/
@[simp] theorem nbaFold_nil (n : String) (x : LVec) : nbaFold n [] x = x := rfl

/-- One write, then the rest of the queue. -/
theorem nbaFold_cons (n : String) (u : String × Nat × LVec) (q : NbaQueue2) (x : LVec) :
    nbaFold n (u :: q) x = nbaFold n q (if u.1 = n then x.insertAt u.2.1 u.2.2 else x) := rfl

/-- A write to the register itself. -/
@[simp] theorem nbaFold_cons_self (n : String) (lo : Nat) (v : LVec) (q : NbaQueue2) (x : LVec) :
    nbaFold n ((n, lo, v) :: q) x = nbaFold n q (x.insertAt lo v) := by
  simp [nbaFold]

/-- A write to another register (`simp` decides the names' disequality). -/
@[simp] theorem nbaFold_cons_ne {n m : String} (h : m ≠ n) (lo : Nat) (v : LVec) (q : NbaQueue2) (x : LVec) :
    nbaFold n ((m, lo, v) :: q) x = nbaFold n q x := by
  simp [nbaFold, h]

/-- The commit of a queue chosen by a condition. -/
theorem nbaFold_ite (n : String) (c : Prop) [Decidable c] (q₁ q₂ : NbaQueue2) (x : LVec) :
    nbaFold n (if c then q₁ else q₂) x = if c then nbaFold n q₁ x else nbaFold n q₂ x := by
  split <;> rfl

/-- A queue that writes no `n` leaves `n`. -/
theorem nbaFold_of_forall_ne {n : String} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 ≠ n) → ∀ x, nbaFold n q x = x
  | [], _, _ => rfl
  | u :: q, h, x => by
    rw [nbaFold_cons, if_neg (h u List.mem_cons_self)]
    exact nbaFold_of_forall_ne (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) x

/-- A queue that writes only names in `ns` leaves every other name. -/
theorem nbaFold_of_names {n : String} {ns : List String} {q : NbaQueue2} (hq : ∀ u ∈ q, u.1 ∈ ns) (hn : n ∉ ns)
    (x : LVec) : nbaFold n q x = x :=
  nbaFold_of_forall_ne (n := n) (fun u hu h => hn (h ▸ hq u hu)) x

/-- The names a queue writes, decided: every write's name is in `regs` (for a concrete queue, `simp` evaluates
the `all`). -/
theorem nbaNames_of_all {q : NbaQueue2} {regs : List String} (h : q.all (fun u => regs.contains u.1) = true) :
    ∀ u ∈ q, u.1 ∈ regs :=
  fun u hu => List.contains_iff_mem.mp (List.all_eq_true.mp h u hu)

theorem nbaNames_append {q₁ q₂ : NbaQueue2} {regs : List String} (h₁ : ∀ u ∈ q₁, u.1 ∈ regs)
    (h₂ : ∀ u ∈ q₂, u.1 ∈ regs) : ∀ u ∈ q₁ ++ q₂, u.1 ∈ regs := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact h₁ u hu
  · exact h₂ u hu

theorem nbaNames_flatMap {α : Type} {l : List α} {f : α → NbaQueue2} {regs : List String}
    (h : ∀ a, ∀ u ∈ f a, u.1 ∈ regs) : ∀ u ∈ l.flatMap f, u.1 ∈ regs := by
  intro u hu
  obtain ⟨a, -, ha⟩ := List.mem_flatMap.mp hu
  exact h a u ha

private theorem lookup_none_not_mem : ∀ {st : SvState} {n : String}, SvState.lookup st n = none →
    n ∉ st.map Prod.fst
  | [], _, _ => by simp
  | (k, v) :: rest, n, h => by
    simp only [SvState.lookup] at h
    by_cases hk : k = n
    · subst hk; simp at h
    · have : (k == n) = false := by simp [hk]
      rw [this] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have := lookup_none_not_mem h
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun h' => hk h'.symm, this⟩

private theorem map_ite_eq_self {n : String} (f : LVec → LVec) :
    ∀ (rest : SvState), n ∉ rest.map Prod.fst →
      (rest.map fun p => (p.1, if n = p.1 then f p.2 else p.2)) = rest
  | [], _ => rfl
  | (k, v) :: rest, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.map_cons, if_neg h.1, map_ite_eq_self f rest h.2]

/-- One nonblocking update of a state with distinct names, as a `map`: the entry it names takes the write. -/
theorem nbaStep_eq_map : ∀ (st : SvState) (u : String × Nat × LVec), (st.map Prod.fst).Nodup →
    nbaStep st u = st.map fun p => (p.1, if u.1 = p.1 then p.2.insertAt u.2.1 u.2.2 else p.2)
  | [], u, _ => by simp [nbaStep, SvState.lookup]
  | (k, v) :: rest, u, hnd => by
    have hk : k ∉ rest.map Prod.fst := (List.nodup_cons.mp hnd).1
    have hr : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
    by_cases h : k = u.1
    · subst h
      have hrest := map_ite_eq_self (n := u.1) (fun x => x.insertAt u.2.1 u.2.2) rest hk
      simp [nbaStep, SvState.lookup, SvState.set, hrest]
    · have ih := nbaStep_eq_map rest u hr
      have hb : (k == u.1) = false := by simp [h]
      have h' : ¬ u.1 = k := fun e => h e.symm
      unfold nbaStep at ih ⊢
      simp only [SvState.lookup, hb, Bool.false_eq_true, ↓reduceIte]
      cases hl : SvState.lookup rest u.1 with
      | none =>
        simp only [hl] at ih
        simp only [List.map_cons, if_neg h']
        exact congrArg _ ih
      | some old =>
        simp only [hl] at ih
        simp only [SvState.set, hb, Bool.false_eq_true, ↓reduceIte, List.map_cons, if_neg h']
        exact congrArg _ ih

/-- **The commit of a state with distinct names, register by register**: every entry `(n, x)` becomes
`(n, nbaFold n q x)`. -/
theorem commitNba2_eq_map : ∀ (q : NbaQueue2) (st : SvState), (st.map Prod.fst).Nodup →
    commitNba2 st q = st.map fun p => (p.1, nbaFold p.1 q p.2)
  | [], st, _ => by
    simp only [commitNba2_nil]
    conv => lhs; rw [← List.map_id st]
    rfl
  | u :: q, st, hnd => by
    have hk : ((st.map fun p => (p.1, if u.1 = p.1 then p.2.insertAt u.2.1 u.2.2 else p.2)).map Prod.fst) =
        st.map Prod.fst := by simp [List.map_map, Function.comp_def]
    rw [commitNba2_cons, nbaStep_eq_map st u hnd, commitNba2_eq_map q _ (by rw [hk]; exact hnd), List.map_map]
    rfl

/-- **The commit of a cycle on a state of distinct names, when every write names a register of `regs`**: each
register is its `nbaFold`, every other entry (the inputs) unchanged. On a positional state
(`MS ck r … : SvState`, a literal list), `simp [MS]` proves the names distinct and turns the right side back into
`MS` with one `nbaFold` per register. -/
theorem commitNba2_eq_map_of_names {st : SvState} {q : NbaQueue2} {regs : List String}
    (hnd : (st.map Prod.fst).Nodup) (hq : ∀ u ∈ q, u.1 ∈ regs) :
    commitNba2 st q = st.map fun p => (p.1, if p.1 ∈ regs then nbaFold p.1 q p.2 else p.2) := by
  rw [commitNba2_eq_map q st hnd]
  refine List.map_congr_left fun p _ => ?_
  by_cases h : p.1 ∈ regs
  · rw [if_pos h]
  · rw [if_neg h, nbaFold_of_names hq h]

/-- Committing the writes `(n, r·E, g r)`, `r = 0 … m-1`, in order, to `n` is `LVec.insertEntries`. -/
theorem nbaFold_map_insertEntries (n : String) (E : Nat) (g : Nat → LVec) (m : Nat) (x : LVec) :
    nbaFold n ((List.range m).map fun r => (n, r * E, g r)) x = LVec.insertEntries E g m x := by
  simp only [nbaFold, List.foldl_map]; rfl

/-- A loop of single writes, as one `map`. -/
theorem flatMap_range_singleton {α : Type} {M : Nat} {q : Nat → List α} {f : Nat → α}
    (h : ∀ j, j < M → q j = [f j]) : (List.range M).flatMap q = (List.range M).map f := by
  rw [CombView.flatMap_congr' fun j hj => h j (List.mem_range.mp hj)]
  induction (List.range M) with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

/-- A double loop of single writes in row-major order (`q i j` writes entry `i·M + j`), as one `map`. -/
theorem flatMap_range_rowMajor {α : Type} {R M : Nat} {q : Nat → Nat → List α} (f : Nat → α)
    (h : ∀ i j, i < R → j < M → q i j = [f (i * M + j)]) :
    ((List.range R).flatMap fun i => (List.range M).flatMap (q i)) = (List.range (R * M)).map f := by
  suffices ∀ K, K ≤ R → ((List.range K).flatMap fun i => (List.range M).flatMap (q i)) =
      (List.range (K * M)).map f from this R (Nat.le_refl _)
  intro K; induction K with
  | zero => intro _; simp
  | succ K ih =>
    intro hK
    rw [List.range_succ, List.flatMap_append, ih (by omega), Nat.succ_mul, List.range_add, List.map_append,
      List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [flatMap_range_singleton (f := fun j => f (K * M + j)) fun j hj => h K j (by omega) hj]
    rfl

/-! ## 2. Register families, window by window -/

/-- `insertEntries` reads only the written values below `n`. -/
theorem LVec.insertEntries_congr {E : Nat} {g g' : Nat → LVec} (c : LVec) : ∀ n, (∀ r, r < n → g r = g' r) →
    LVec.insertEntries E g n c = LVec.insertEntries E g' n c
  | 0, _ => rfl
  | n + 1, h => by
    rw [LVec.insertEntries_succ, LVec.insertEntries_succ, LVec.insertEntries_congr c n (fun r hr => h r (by omega)),
      h n (by omega)]

/-- **Window `r` of a written family** is the value written there. -/
theorem LVec.extract_insertEntries {E : Nat} {g : Nat → LVec} (hg : ∀ k, (g k).width = E) (c : LVec) :
    ∀ n, n * E ≤ c.width → ∀ r, r < n → (LVec.insertEntries E g n c).extract (r * E) E = g r
  | 0, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | n + 1, hn, r, hr => by
    have hn' : n * E + E ≤ c.width := by simpa [Nat.succ_mul] using hn
    rw [LVec.insertEntries_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · have := rowMajor_le (K := E) hr
      rw [LVec.extract_insertAt_of_disjoint (.inl this)]
      exact LVec.extract_insertEntries hg c n (by omega) r hr
    · exact LVec.extract_insertAt_self (hg r) (by rw [LVec.width_insertEntries]; exact hn')

/-- Writing every window's own content back changes nothing. -/
theorem LVec.insertEntries_extract_self (E : Nat) (v : LVec) :
    ∀ n, LVec.insertEntries E (fun r => v.extract (r * E) E) n v = v
  | 0 => rfl
  | n + 1 => by rw [LVec.insertEntries_succ, LVec.insertEntries_extract_self E v n, LVec.insertAt_extract_self]

/-- **A vector known window by window** is the packed vector of its windows. -/
theorem LVec.eq_ofBitVec_packBV {E n : Nat} {v : LVec} {f : Nat → BitVec E} (hw : v.width = n * E)
    (h : ∀ r, r < n → v.extract (r * E) E = LVec.ofBitVec (f r)) : v = LVec.ofBitVec (packBV E n f) := by
  rw [← LVec.insertEntries_ofBitVec f v hw, ← LVec.insertEntries_congr v n h, LVec.insertEntries_extract_self]

/-! ## 3. Disjoint windows -/

/-- Two processes drive disjoint windows: the relation of `driversOk_of_ff` and `ffDisjB_of_pairwise`. -/
abbrev ProcDisj (p q : Process2) : Prop := ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false

/-- Windows of different signals never overlap. -/
theorem DrvWin.overlaps_of_ne {n n' : String} (h : n ≠ n') (a b : Option (Nat × Nat)) :
    DrvWin.overlaps (n, a) (n', b) = false := by
  simp [DrvWin.overlaps, h]

/-- Two different row-major units `r ≠ r'` of width `E` of one signal never overlap. -/
theorem DrvWin.overlaps_rowMajor {n : String} {E r r' : Nat} (h : r ≠ r') :
    DrvWin.overlaps (n, some (r * E, E)) (n, some (r' * E, E)) = false := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := rowMajor_le (K := E) h
    simp [DrvWin.overlaps]; omega
  · have := rowMajor_le (K := E) h
    simp [DrvWin.overlaps]; omega

/-- Processes that write only `n`, and only `n' ≠ n`, are disjoint. -/
theorem ProcDisj.of_names {p q : Process2} {n n' : String} (h : n ≠ n') (hp : ∀ a ∈ p.procWins, a.1 = n)
    (hq : ∀ b ∈ q.procWins, b.1 = n') : ProcDisj p q := by
  intro a ha b hb
  obtain ⟨x, u⟩ := a; obtain ⟨y, v⟩ := b
  have h1 := hp _ ha; have h2 := hq _ hb
  simp only at h1 h2; subst h1; subst h2
  exact DrvWin.overlaps_of_ne h u v

/-- Processes whose windows are of names in `ns`, and in `ms`, two lists with no name in common, are disjoint. -/
theorem ProcDisj.of_nameLists {p q : Process2} {ns ms : List String} (hp : ∀ a ∈ p.procWins, a.1 ∈ ns)
    (hq : ∀ b ∈ q.procWins, b.1 ∈ ms) (h : ∀ n ∈ ns, n ∉ ms) : ProcDisj p q := by
  intro a ha b hb
  have h1 := hp a ha; have h2 := hq b hb
  simp only [DrvWin.overlaps, Bool.and_eq_false_iff]
  left
  rw [beq_eq_false_iff_ne]
  intro he; rw [he] at h1; exact h _ h1 h2

/-- Processes that each write one row-major unit of one signal, different units, are disjoint. -/
theorem ProcDisj.of_units {p q : Process2} {n : String} {E r r' : Nat} (h : r ≠ r')
    (hp : p.procWins = [(n, some (r * E, E))]) (hq : q.procWins = [(n, some (r' * E, E))]) : ProcDisj p q := by
  intro a ha b hb
  rw [hp] at ha; rw [hq] at hb
  simp only [List.mem_singleton] at ha hb; subst ha; subst hb
  exact DrvWin.overlaps_rowMajor h

/-- Two lists of processes, one writing only `n`, the other only `n' ≠ n`, are disjoint pair by pair. -/
theorem ProcDisj.of_lists {l₁ l₂ : List Process2} {n n' : String} (h : n ≠ n')
    (h₁ : ∀ p ∈ l₁, ∀ a ∈ p.procWins, a.1 = n) (h₂ : ∀ q ∈ l₂, ∀ b ∈ q.procWins, b.1 = n') :
    ∀ p ∈ l₁, ∀ q ∈ l₂, ProcDisj p q :=
  fun p hp q hq => ProcDisj.of_names h (h₁ p hp) (h₂ q hq)

/-- Row-major indices are ordered by their rows first. -/
theorem rowMajor_lt {N i j i' j' : Nat} (hj : j < N) (h : i < i') : i * N + j < i' * N + j' := by
  have := rowMajor_le (K := N) h; omega

/-- Row-major indices of different cells differ. -/
theorem rowMajor_ne {N i j i' j' : Nat} (hj : j < N) (hj' : j' < N) (h : i ≠ i' ∨ j ≠ j') :
    i * N + j ≠ i' * N + j' := by
  intro he
  rcases Nat.lt_or_ge i i' with hi | hi
  · exact absurd he (Nat.ne_of_lt (rowMajor_lt hj hi))
  · rcases Nat.lt_or_ge i' i with hi' | hi'
    · exact absurd he.symm (Nat.ne_of_lt (rowMajor_lt hj' hi'))
    · have : i = i' := by omega
      subst this; rcases h with h | h
      · exact h rfl
      · omega

/-- The row of a row-major index (its column is core's `Nat.mul_add_mod_of_lt`). -/
theorem rowMajor_div {N i j : Nat} (hj : j < N) : (i * N + j) / N = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

/-- A map over `range n`, related in index order. -/
theorem pairwise_map_range {α : Type} {R : α → α → Prop} {n : Nat} {f : Nat → α}
    (h : ∀ a b, a < b → b < n → R (f a) (f b)) : ((List.range n).map f).Pairwise R :=
  List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ hb hab => h _ _ hab (List.mem_range.mp hb))

/-- A double family `(k, j) ↦ f k j`, `k < m`, `j < n`, related in row-major order. -/
theorem pairwise_rowMajor {α : Type} {R : α → α → Prop} {m n : Nat} {f : Nat → Nat → α}
    (h : ∀ k j k' j', k < m → k' < m → j < n → j' < n → k * n + j < k' * n + j' → R (f k j) (f k' j')) :
    ((List.range m).flatMap fun k => (List.range n).map (f k)).Pairwise R := by
  refine pairwise_flatMap_range (fun k hk => pairwise_map_range fun a b hab hb =>
    h k a k b hk hk (by omega) hb (by omega)) ?_
  intro k k' hkk' hk' a ha b hb
  simp only [List.mem_map, List.mem_range] at ha hb
  obtain ⟨j, hj, rfl⟩ := ha; obtain ⟨j', hj', rfl⟩ := hb
  exact h k j k' j' (by omega) hk' hj hj' (rowMajor_lt hj hkk')

/-! ## 4. Generate loops -/

section gen

variable {env : IEnv} {elems : List (String × Nat)} {F : Nat}

/-- **A loop `for (g = 0; g < e; g++)` whose bound is `M`** over any body whose expansion at `g = v` is `f v`. -/
theorem GenItem.expand2_range_flatMap {label : Option String} {g : String} {e : PExpr} {rc : Option Nat}
    {body : List GenItem} {M : Nat} {f : Nat → List Process2}
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok (M : Int)) (hF : M < F)
    (hf : ∀ v, v < M → expandList2 (env.bindVal g v) elems F body = .ok (f v)) :
    (GenItem.genFor label g (.int 0) (.binary .slt (.genvarRef g) e) (.unary .inc (.genvarRef g)) rc body).expand2
      env elems F = .ok ((List.range M).flatMap f) := by
  rw [LeanModels.Sv.GenItem.expand2_genFor_ascending_flatMap (N := (M : Int)) (f := fun v => f v.toNat)
    (evalInt_int 0) hei he (by simpa using hF) (fun v h0 hv => by
      have := hf v.toNat (by omega)
      rwa [Int.toNat_of_nonneg h0] at this)]
  simp only [Int.sub_zero, Int.toNat_natCast, intRange_zero, List.flatMap_map]

/-- **A loop `for (g = 0; g < e; g++)` over one process template** expands to `(List.range M).map f`, from the
template's instantiation at each `g = v < M`. -/
theorem GenItem.expand2_range_map {label : Option String} {g : String} {e : PExpr} {rc : Option Nat}
    {p : PProcess} {M : Nat} {f : Nat → Process2}
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok (M : Int)) (hF : M < F)
    (hf : ∀ v, v < M → instProcess2 (env.bindVal g v) elems p = f v) :
    (GenItem.genFor label g (.int 0) (.binary .slt (.genvarRef g) e) (.unary .inc (.genvarRef g)) rc
      ([p].map GenItem.process)).expand2 env elems F = .ok ((List.range M).map f) := by
  rw [LeanModels.Sv.GenItem.expand2_genFor_ascending_processes (evalInt_int 0) hei he (by simpa using hF)]
  simp only [Int.sub_zero, Int.toNat_natCast, intRange_zero, List.flatMap_map, List.map_cons, List.map_nil,
    Gen2.flatMap_singleton_map]
  congr 1
  exact List.map_congr_left fun v hv => hf v (List.mem_range.mp hv)

/-- **Two nested loops over one process template** expand to the row-major family
`(List.range M).flatMap fun v => (List.range N).map (f v)`. -/
theorem GenItem.expand2_range_map₂ {label label' : Option String} {g g' : String} {e e' : PExpr}
    {rc rc' : Option Nat} {p : PProcess} {M N : Nat} {f : Nat → Nat → Process2}
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok (M : Int))
    (hei' : ∀ i j : Int, e'.isInt ((env.bindVal g i).bindVal g' j) = true)
    (he' : ∀ i j : Int, evalInt ((env.bindVal g i).bindVal g' j) e' = .ok (N : Int)) (hM : M < F) (hN : N < F)
    (hf : ∀ v w, v < M → w < N → instProcess2 ((env.bindVal g v).bindVal g' w) elems p = f v w) :
    (GenItem.genFor label g (.int 0) (.binary .slt (.genvarRef g) e) (.unary .inc (.genvarRef g)) rc
      [GenItem.genFor label' g' (.int 0) (.binary .slt (.genvarRef g') e') (.unary .inc (.genvarRef g')) rc'
        ([p].map GenItem.process)]).expand2 env elems F =
      .ok ((List.range M).flatMap fun v => (List.range N).map (f v)) :=
  GenItem.expand2_range_flatMap hei he hM fun v hv => expandList2_singleton_ok
    (GenItem.expand2_range_map (hei' v) (he' v) hN fun w hw => hf v w hv hw)

/-- `GenItem.expand2_range_map` for a bound that is a parameter `n` (`g < N`); `hN` is `fun _ => rfl` on a
concrete instantiation environment. -/
theorem GenItem.expand2_param_map {label : Option String} {g n : String} {rc : Option Nat} {p : PProcess} {M : Nat}
    {f : Nat → Process2} (hN : ∀ i : Int, (env.bindVal g i).vals.lookup n = some (M : Int)) (hF : M < F)
    (hf : ∀ v, v < M → instProcess2 (env.bindVal g v) elems p = f v) :
    (GenItem.genFor label g (.int 0) (.binary .slt (.genvarRef g) (.paramRef n none)) (.unary .inc (.genvarRef g)) rc
      ([p].map GenItem.process)).expand2 env elems F = .ok ((List.range M).map f) :=
  GenItem.expand2_range_map (fun i => isInt_paramRef_of (hN i)) (fun i => evalInt_paramRef_of (hN i)) hF hf

/-- `GenItem.expand2_range_map₂` for bounds that are parameters (`g < M`, `g' < N`). -/
theorem GenItem.expand2_param_map₂ {label label' : Option String} {g g' n n' : String} {rc rc' : Option Nat}
    {p : PProcess} {M N : Nat} {f : Nat → Nat → Process2}
    (hM : ∀ i : Int, (env.bindVal g i).vals.lookup n = some (M : Int))
    (hN : ∀ i j : Int, ((env.bindVal g i).bindVal g' j).vals.lookup n' = some (N : Int)) (hMF : M < F) (hNF : N < F)
    (hf : ∀ v w, v < M → w < N → instProcess2 ((env.bindVal g v).bindVal g' w) elems p = f v w) :
    (GenItem.genFor label g (.int 0) (.binary .slt (.genvarRef g) (.paramRef n none)) (.unary .inc (.genvarRef g)) rc
      [GenItem.genFor label' g' (.int 0) (.binary .slt (.genvarRef g') (.paramRef n' none))
        (.unary .inc (.genvarRef g')) rc' ([p].map GenItem.process)]).expand2 env elems F =
      .ok ((List.range M).flatMap fun v => (List.range N).map (f v)) :=
  GenItem.expand2_range_map₂ (fun i => isInt_paramRef_of (hM i)) (fun i => evalInt_paramRef_of (hM i))
    (fun i j => isInt_paramRef_of (hN i j)) (fun i j => evalInt_paramRef_of (hN i j)) hMF hNF hf

end gen

/-! ## 5. Power-up: every declaration's value, one at a time -/

/-- `powerUp_cases h with x₁ … xₙ`: `h : PowerUp d st`, for a design whose declaration list is literal (after
`rw [<agreement>] at h`), with `n` declarations. Takes the declarations off one at a time (`powerUp_cons`): `st`
becomes the literal state of the values `x₁ … xₙ`, and `w_xᵢ : xᵢ.width = <declared width>` is in context (the
knownness facts are dropped). Then `exact ⟨x₁, …, xₙ, rfl, w_…⟩` closes a shape `∃ x₁ … xₙ, st = MS x₁ … xₙ ∧ …`. -/
syntax (name := powerUpCases) "powerUp_cases " ident " with " (ppSpace colGt ident)+ : tactic

macro_rules
  | `(tactic| powerUp_cases $h:ident with $xs:ident*) => do
    -- `rfl` is the rcases keyword pattern only without macro scopes
    let rfl := Lean.mkIdent `rfl
    let mut tac ← `(tactic| skip)
    for x in xs do
      let w := Lean.mkIdent (x.getId.appendBefore "w_")
      tac ← `(tactic| ($tac; obtain ⟨$x:ident, _, $rfl:ident, $w:ident, -, $h:ident⟩ := powerUp_cons.mp $h))
    `(tactic| ($tac; obtain $rfl:ident := powerUp_nil.mp $h))

/-! ## 6. Values -/

/-- A left shift of known vectors by a known amount (the `<<` twin of `LVec.shr_ofBitVec`). -/
@[simp] theorem LVec.shl_ofBitVec {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shl (LVec.ofBitVec y) = LVec.ofBitVec (x <<< y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shl, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shl, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn, LVec.width_ofBitVec, hi,
    dite_true, BitVec.getLsbD_shiftLeft, LVec.getElem?_ofBitVec]
  by_cases h : i < y.toNat
  · simp [h]
  · simp [h, show i - y.toNat < w by omega]

/-- The one-bit literal `1'b0` is known. -/
@[simp] theorem LVec.allKnown_l0 : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

/-- The one-bit literal `1'b1` is known. -/
@[simp] theorem LVec.allKnown_l1 : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

/-- **The evaluated sign extension of a known window**: `{{m{v[lo+W-1]}}, v[lo +: W]}`, when `v[lo +: W]` is
`x`, is `x` sign-extended to `m + W` bits. -/
theorem LVec.sext_of_extract {v : LVec} {m lo W : Nat} (hW : 1 ≤ W) {x : BitVec W}
    (h : v.extract lo W = LVec.ofBitVec x) :
    LVec.concatMany #[LVec.replVec m (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W] =
      LVec.ofBitVec (x.signExtend (m + W)) := by
  have h1 : v.extract (lo + W - 1) 1 = (v.extract lo W).extract (W - 1) 1 := by
    rw [LVec.extract_extract v (show W - 1 + 1 ≤ W by omega), show lo + (W - 1) = lo + W - 1 by omega]
  have h2 := LVec.ofBitVec_replicate_append_eq_signExtend hW x m (p := W - 1) (lo := 0) (by omega)
  rw [BitVec.extractLsb'_eq_self] at h2
  rw [h1, h, LVec.extract_ofBitVec x (show W - 1 + 1 ≤ W by omega)]
  simp only [LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec]
  exact h2

/-- **The signed product, truncated**: two operands sign-extended to `n ≥ m` bits, multiplied and truncated to
`m` bits, are `ofInt` of the product of their values (`Lib.setWidth_add_mul_signExtend` with no accumulator). -/
theorem Lib.setWidth_mul_signExtend {m n w : Nat} (h : m ≤ n) (a b : BitVec w) :
    (a.signExtend n * b.signExtend n).setWidth m = BitVec.ofInt m (a.toInt * b.toInt) := by
  have := LeanModels.Sv.Lib.setWidth_add_mul_signExtend h (0#m) a b
  simpa using this

#print axioms commitNba2_eq_map
#print axioms commitNba2_eq_map_of_names
#print axioms nbaFold_map_insertEntries
#print axioms flatMap_range_rowMajor
#print axioms LVec.eq_ofBitVec_packBV
#print axioms ProcDisj.of_nameLists
#print axioms ProcDisj.of_units
#print axioms pairwise_rowMajor
#print axioms GenItem.expand2_range_map₂
#print axioms GenItem.expand2_param_map₂
#print axioms LVec.shl_ofBitVec
#print axioms LVec.sext_of_extract
#print axioms Lib.setWidth_mul_signExtend

end SvGolf

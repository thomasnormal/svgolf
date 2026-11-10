import tasks.sorter.Spec
import SvGolf.LoadSv
import SvGolf.Seq
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.Known2

/-!
# Task `sorter`: kernel refutations of wrong designs (untrusted, kernel-checked; 2026-11-08)

Nothing here is part of the trusted base. The statement (`tasks/sorter/Spec.lean`, `StreamTask.StatementV2`) is
refuted for a wrong design by ONE run that the kernel evaluates (`decide +kernel`), from one power-up state, on one
known stimulus. The latency is the submission's, so a refutation holds for EVERY latency function: the stimulus is a
concrete prefix (a reset, one transaction, idle entries until the design is at rest), then `lat + 1` idle entries,
and the design's state at the end of the prefix is a FIXED POINT of the idle entry (`cycleStep2_fixed`: under every
schedule, at every schedule counter, the clock step of an FF-only design returns that state), so the whole run is the
evaluated prefix followed by copies of its last snapshot, whatever `lat` is (`stream_refuted`). The statement's rely
holds on that stimulus (`rely_one`), and its guarantee for the transaction fails: the snapshots from the start on emit
`emitted (obsList …)` (the evaluated prefix; the copies of a snapshot with `out_valid` = 0 emit nothing), which is not
`sortAsc` of the inputs. A second shape (`early_refuted`) is a run with no transaction at all whose snapshot shows
`out_valid` = 1 after the release (the guarantee's "0 before the first start"); a third (`stream2_refuted`) runs two
transactions and refutes the second (its start is `Idle`: the first's outputs are shown before it, `showsB`).

The wrong designs are hand-built twins at one point of the family, `(N, W) = (2, 2)` (one at `(3, 2)`): each
refutation is stated for EVERY design family whose instance at that point is the twin (`sem 2 2 = d → ¬ Statement
sem lat`), and the twin is checked equal to the instance there of the design `load_sv` loads (`#guard reprStr …`: the
compiled evaluator compares the two printed designs; the kernel does not reduce the generate expansion), as in
`tests/arbiter/negative/Refute.lean`.

Here: the plumbing, the reference's twin `refD` (and `refDN N` for every `N`, at `W = 2`), and the refutations of
the attack designs of `tests/sorter/attacks/` (`tests/expected.json` pins each one at the `solution` stage with the
reference's proof; these show that no proof exists, for any latency). The generated mutants are refuted in
`Mutants.lean`.

| attack | point | run | refutation |
|---|---|---|---|
| `early_valid` | (2, 2) | on `2, 3` it emits `0, 2, 3` | `early_valid_refuted` |
| `missing_else` | (2, 2) | on `2, 3` it emits `3, 3` | `missing_else_refuted` |
| `push_own_value` | (2, 2) | on `3, 2` it emits `3, 3` | `push_own_value_refuted` |
| `signed_order` | (2, 2) | on `2, 3` it emits `0, 0` | `signed_order_refuted` |
| `token_self` | (2, 2) | on `2, 3` it emits nothing, for ever | `token_self_refuted` |
| `reset_keeps_cells` | (3, 2) | from the power-up with every cell 3, on `0, 0, 0` the first value it emits is 3 | `reset_keeps_cells_refuted` |
| `top_not_drained` | (2, 2) | two transactions: `2, 3` is emitted right, then `1, 1` emits `3, 3` (the top cell kept 3) | `top_not_drained_refuted` |
| `rst_gate` | (2, 2) | no run: `assign out_valid = ov_q & ~rst` is a combinational path from `rst` to `out_valid` (rule 1, nothing exempt since 2026-11-09) | `rst_gate_refuted` |

`reset_keeps_cells` is RIGHT at `N = 2` (its `why` in `tests/expected.json` says "every N >= 2"): the one unreset
cell takes the reset top cell's 0 at the entry after the release, an entry that never carries a value under the
rely.
-/

namespace SvGolf.Tasks.Sorter.Refute

open LeanModels.Sv SvGolf

/-! ## Runs: a prefix, then a fixed point -/

/-- The state a run from `st` with the trace `tr` ends in: its last snapshot, or `st` itself. -/
def lastOr (st : SvState) (tr : List SvState) : SvState := tr.getLast?.getD st

theorem lastOr_cons (st st' : SvState) (tr : List SvState) : lastOr st (st' :: tr) = lastOr st' tr := by
  simp [lastOr, List.getLast?_cons]

/-- A completed run of `a`, then a run of `b` from where it ended (at any schedule counter), is a run of `a ++ b`. -/
theorem runFrom2_append {d : Design2} {σ : ScheduleOracle} {F : Nat} :
    ∀ {a b tra trb : List SvState} {st : SvState} {k : Nat},
      runFrom2 d σ F st k a = .ok tra → (∀ k', runFrom2 d σ F (lastOr st tra) k' b = .ok trb) →
      runFrom2 d σ F st k (a ++ b) = .ok (tra ++ trb)
  | [], b, tra, trb, st, k, ha, hb => by
      simp only [runFrom2_nil, Res.ok.injEq] at ha
      subst ha
      simpa [lastOr] using hb k
  | x :: a, b, tra, trb, st, k, ha, hb => by
      obtain ⟨st', k', tr', h1, h2, rfl⟩ := runFrom2_cons_eq_ok.mp ha
      rw [lastOr_cons] at hb
      exact runFrom2_cons_eq_ok.mpr ⟨st', k', tr' ++ trb, h1, runFrom2_append h2 hb, rfl⟩

/-- A state that every clock step on the entry `e` returns is the whole run on copies of `e`. -/
theorem runFrom2_fixed {d : Design2} {σ : ScheduleOracle} {F : Nat} {e stF : SvState}
    (h : ∀ k, cycleStep2 d σ F e stF k = .ok (stF, k + 3)) :
    ∀ (L k : Nat), runFrom2 d σ F stF k (List.replicate L e) = .ok (List.replicate L stF)
  | 0, k => by simp
  | L + 1, k => by
      rw [List.replicate_succ, List.replicate_succ]
      exact runFrom2_cons_eq_ok.mpr ⟨stF, k + 3, _, h k, runFrom2_fixed h L (k + 3), rfl⟩

/-- `run2At` is `runFrom2` from the state for a design with no qualified `case` (nothing to validate). -/
theorem run2At_eq {d : Design2} {σ : ScheduleOracle} {F : Nat} {st0 : SvState} {stim : List SvState}
    (hq : d.processes.toList.any Process2.hasQualifiedCase = false) :
    run2At d σ F st0 stim = runFrom2 d σ F st0 0 stim := by
  simp only [run2At, hq, Bool.false_eq_true, if_false]
  cases runFrom2 d σ F st0 0 stim <;> rfl

/-- The edge run of process `p` on `st` leaves `st` alone (it issues nonblocking updates only), decided. -/
def keeps (F : Nat) (st : SvState) (p : Process2) : Bool :=
  match runEdgeProcess2 F st [] p with
  | .ok (s, _) => decide (s = st)
  | _ => false

/-- **A fixed point of the clock step**, decided at one state: for an FF-only design (`ffOnlyProfileB`) the clock
step under every schedule and at every counter is `clockStep` of the applied inputs (`cycleStep2_profile`); if that is
the state itself, the state is a fixed point of the entry. -/
theorem cycleStep2_fixed {d : Design2} {σ : ScheduleOracle} {e stF : SvState} (hp : d.ffOnlyProfileB = true)
    (hk : d.processes.toList.all (keeps 64 (applyInputs2 d e stF)) = true)
    (hnd : ((applyInputs2 d e stF).map Prod.fst).Nodup)
    (hfix : clockStep d 64 (applyInputs2 d e stF) d.edgeIndices = stF) (k : Nat) :
    cycleStep2 d σ 64 e stF k = .ok (stF, k + 3) := by
  rw [cycleStep2_profile hp σ e stF k ?_ hnd (by decide), hfix]
  intro i p hi
  have hmem : p ∈ d.processes.toList := by
    rw [Array.getElem?_eq_some_iff] at hi
    obtain ⟨hlt, rfl⟩ := hi
    exact Array.getElem_mem_toList hlt
  have hp' := List.all_eq_true.mp hk p hmem
  unfold keeps at hp'
  split at hp'
  · rename_i s q hr
    have hs : s = applyInputs2 d e stF := of_decide_eq_true hp'
    exact ⟨q, by rw [hr, hs]⟩
  · cases hp'

/-! ## Stimuli: rows of `rst`, `start`, `in_valid`, `in_data` -/

/-- One stimulus entry: `rst`, `start`, `in_valid`, `in_data` (the clock is not driven: it is not observed). -/
abbrev Row (W : Nat) := Bool × Bool × Bool × BitVec W

/-- The entry of a row. -/
def ent {W : Nat} (r : Row W) : SvState :=
  [("rst", LVec.ofBitVec (BitVec.ofBool r.1)), ("start", LVec.ofBitVec (BitVec.ofBool r.2.1)),
   ("in_valid", LVec.ofBitVec (BitVec.ofBool r.2.2.1)), ("in_data", LVec.ofBitVec r.2.2.2)]

/-- An idle row: no reset, no start, no input, `in_data` 0. -/
def idle (W : Nat) : Row W := (false, false, false, 0#W)

theorem lookup_ent_rst {W : Nat} (r : Row W) :
    SvState.lookup (ent r) "rst" = some (LVec.ofBitVec (BitVec.ofBool r.1)) := by
  simp [ent, SvState.lookup]

theorem lookup_ent_start {W : Nat} (r : Row W) :
    SvState.lookup (ent r) "start" = some (LVec.ofBitVec (BitVec.ofBool r.2.1)) := by
  simp [ent, SvState.lookup]

theorem lookup_ent_valid {W : Nat} (r : Row W) :
    SvState.lookup (ent r) "in_valid" = some (LVec.ofBitVec (BitVec.ofBool r.2.2.1)) := by
  simp [ent, SvState.lookup]

theorem lookup_ent_data {W : Nat} (r : Row W) :
    SvState.lookup (ent r) "in_data" = some (LVec.ofBitVec r.2.2.2) := by
  simp [ent, SvState.lookup]

/-- A signal that holds the known bit `a` binds the bit `b` iff `a = b`. -/
theorem bitIs_iff {st : SvState} {n : String} {a : Bool}
    (h : SvState.lookup st n = some (LVec.ofBitVec (BitVec.ofBool a))) (b : Bool) : BitIs st n b ↔ a = b := by
  unfold BitIs
  rw [h, Option.some.injEq, LVec.ofBitVec_inj]
  cases a <;> cases b <;> decide

theorem bitIs_ent_rst {W : Nat} (r : Row W) (b : Bool) : BitIs (ent r) "rst" b ↔ r.1 = b :=
  bitIs_iff (lookup_ent_rst r) b

theorem bitIs_ent_start {W : Nat} (r : Row W) (b : Bool) : BitIs (ent r) "start" b ↔ r.2.1 = b :=
  bitIs_iff (lookup_ent_start r) b

theorem bitIs_ent_valid {W : Nat} (r : Row W) (b : Bool) : BitIs (ent r) "in_valid" b ↔ r.2.2.1 = b :=
  bitIs_iff (lookup_ent_valid r) b

/-- The entry `c` of a stimulus of rows binds `n` to `b` iff the row exists and says so (`f` reads the field). -/
theorem stimBit_rows {W : Nat} {rows : List (Row W)} {c : Nat} {n : String} {b : Bool} {f : Row W → Bool}
    (hf : ∀ r, BitIs (ent r) n b ↔ f r = b) :
    StimBit (rows.map ent) c n b ↔ ∃ r, rows[c]? = some r ∧ f r = b := by
  simp only [StimBit, List.getElem?_map]
  constructor
  · rintro ⟨e, he, hb⟩
    cases hr : rows[c]? with
    | none => simp [hr] at he
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at he
      subst he
      exact ⟨r, rfl, (hf r).1 hb⟩
  · rintro ⟨r, hr, hb⟩
    exact ⟨ent r, by simp [hr], (hf r).2 hb⟩

/-! ## Observations of a trace -/

/-- The bit of the 1-bit signal `n` in `st` (`true` iff it is the known `1`). -/
def bitOf (st : SvState) (n : String) : Bool :=
  SvState.lookup st n == some (LVec.ofBitVec (BitVec.ofBool true))

/-- The `w`-bit value of `n` in `st` (`0` if absent). -/
def dataOf (w : Nat) (st : SvState) (n : String) : BitVec w :=
  BitVec.ofNat w (((SvState.lookup st n).map LVec.toNat).getD 0)

theorem bitOf_of_bitIs {st : SvState} {n : String} {b : Bool} (h : BitIs st n b) : bitOf st n = b := by
  unfold BitIs at h
  unfold bitOf
  rw [h]
  cases b <;> decide

theorem dataOf_of {w : Nat} {st : SvState} {n : String} {v : BitVec w}
    (h : SvState.lookup st n = some (LVec.ofBitVec v)) : dataOf w st n = v := by
  unfold dataOf
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp [LVec.toNat_ofBitVec]

/-- The observation (`out_valid`, `out_data`) of a snapshot, `(false, 0)` for none. -/
def obsOf (w : Nat) : Option SvState → Bool × BitVec w
  | some st => (bitOf st "out_valid", dataOf w st "out_data")
  | none => (false, 0#w)

/-- The observations of the snapshots `s, s + 1, …, s + n - 1` of `tr`. -/
def obsList (w : Nat) (tr : List SvState) (s n : Nat) : List (Bool × BitVec w) :=
  (List.range n).map fun j => obsOf w tr[s + j]?

/-! ## The rely on a one-transaction stimulus -/

/-- The rows of a one-transaction prefix, decided: row 0 resets; every later row deasserts `rst`, starts exactly at
row `s`, and has `in_valid` = 1 exactly at the `n` rows after it. -/
def oneTxn {W : Nat} (rows : List (Row W)) (s n : Nat) : Bool :=
  (rows[0]?.map (·.1) == some true) && 0 < s && s + 1 + n ≤ rows.length &&
    (List.range rows.length).all fun c => c == 0 || match rows[c]? with
      | some r => !r.1 && r.2.1 == (c == s) && r.2.2.1 == decide (s < c ∧ c ≤ s + n)
      | none => false

/-- What `oneTxn` says of the prefix as a whole. -/
theorem oneTxn_spec {W : Nat} {rows : List (Row W)} {s n : Nat} (h : oneTxn rows s n = true) :
    rows[0]?.map (·.1) = some true ∧ 0 < s ∧ s + 1 + n ≤ rows.length := by
  simp only [oneTxn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

/-- The rows of the whole stimulus: the prefix, then `L` idle rows. -/
def full {W : Nat} (rows : List (Row W)) (L : Nat) : List (Row W) := rows ++ List.replicate L (idle W)

theorem full_get {W : Nat} {rows : List (Row W)} {L c : Nat} (hc : rows.length ≤ c) (hc2 : c < rows.length + L) :
    (full rows L)[c]? = some (idle W) := by
  rw [full, List.getElem?_append_right hc, List.getElem?_replicate]
  simp; omega

theorem full_get_lt {W : Nat} {rows : List (Row W)} {L c : Nat} (hc : c < rows.length) :
    (full rows L)[c]? = rows[c]? := by
  rw [full, List.getElem?_append_left hc]

/-- What `oneTxn` says of every row of the whole stimulus `full rows L` from row 1 on. -/
theorem oneTxn_row {W : Nat} {rows : List (Row W)} {s n : Nat} (h : oneTxn rows s n = true) (L : Nat) {c : Nat}
    (h1 : 1 ≤ c) (h2 : c < rows.length + L) :
    ∃ r, (full rows L)[c]? = some r ∧ r.1 = false ∧ r.2.1 = (c == s) ∧
      r.2.2.1 = decide (s < c ∧ c ≤ s + n) := by
  simp only [oneTxn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨_, hs⟩, hl⟩, hall⟩ := h
  rcases Nat.lt_or_ge c rows.length with hc | hc
  · have := hall c hc
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h0 | this
    · omega
    · rw [full_get_lt hc]
      cases hr : rows[c]? with
      | none => simp [hr] at this
      | some r =>
        simp only [hr, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at this
        exact ⟨r, rfl, this.1.1, this.1.2, this.2⟩
  · refine ⟨idle W, full_get hc h2, rfl, ?_, ?_⟩
    · simp [idle]; omega
    · simp [idle]; omega

/-- **The rely holds** on `full rows L` from the release `1`, at the horizon `rows.length + L`, for every trace:
the one start is at `s`, after no earlier start, so it is `Idle`, and `in_valid` is 1 exactly at its `n` values. -/
theorem rely_one {p : Params} {rows : List (Row (task.width p))} {s : Nat} (h : oneTxn rows s (task.count p) = true)
    (L : Nat) (tr : List SvState) :
    task.Rely p ((full rows L).map ent) tr 1 (rows.length + L) := by
  obtain ⟨-, hs, hsl⟩ := oneTxn_spec h
  -- a start in the whole stimulus is at `s`
  have hstart : ∀ c, 1 ≤ c → c < rows.length + L → StimBit ((full rows L).map ent) c "start" true → c = s := by
    intro c h1 h2 hc
    obtain ⟨r, hr, -, hrs, -⟩ := oneTxn_row h L h1 h2
    obtain ⟨r', hr', hb⟩ := (stimBit_rows (f := fun r => r.2.1) (bitIs_ent_start · true)).1 hc
    rw [hr] at hr'; cases hr'
    simpa [hb] using hrs.symm
  intro c h1 h2
  obtain ⟨r, hr, -, hrs, hrv⟩ := oneTxn_row h L h1 h2
  refine ⟨⟨r.2.1, (stimBit_rows (bitIs_ent_start · _)).2 ⟨r, hr, rfl⟩⟩,
    ⟨ent r, r.2.2.2, by simp [hr], lookup_ent_data r⟩, ?_, ?_, ?_⟩
  · intro hc s' h1' h2' hs'
    exact absurd (hstart s' h1' (by omega) hs') (by have := hstart c h1 h2 hc; omega)
  · intro s' h1' h2' h3' hs'
    obtain rfl := hstart s' h1' (by omega) hs'
    refine (stimBit_rows (bitIs_ent_valid · _)).2 ⟨r, hr, ?_⟩
    simp only [hrv, decide_eq_true_eq]; omega
  · intro hno
    refine (stimBit_rows (bitIs_ent_valid · _)).2 ⟨r, hr, ?_⟩
    rw [hrv]
    simp only [decide_eq_false_iff_not, not_and, Nat.not_le]
    intro hsc
    rcases Nat.lt_or_ge (s + task.count p) c with hlt | hle
    · exact hlt
    · exfalso
      refine hno s (by omega) hsc hle ?_
      obtain ⟨r', hr', -, hrs', -⟩ := oneTxn_row h L (c := s) (by omega) (by omega)
      exact (stimBit_rows (bitIs_ent_start · _)).2 ⟨r', hr', by simpa using hrs'⟩

theorem released_one {W : Nat} {rows : List (Row W)} {s n : Nat} (h : oneTxn rows s n = true) (L : Nat) :
    Released "rst" ((full rows L).map ent) 1 (rows.length + L) := by
  refine ⟨by decide, ?_, fun c h1 h2 => ?_⟩
  · obtain ⟨h0, -, hl⟩ := oneTxn_spec h
    refine (stimBit_rows (bitIs_ent_rst · _)).2 ?_
    cases hr : rows[0]? with
    | none => simp [hr] at h0
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at h0
      exact ⟨r, by rw [full_get_lt (by omega)]; exact hr, h0⟩
  · obtain ⟨r, hr, hrr, -, -⟩ := oneTxn_row h L h1 h2
    exact (stimBit_rows (bitIs_ent_rst · _)).2 ⟨r, hr, hrr⟩

/-! ## The refutation of a stream design by one transaction -/

/-- The trace of `d` from the power-up state `st0` on `stim` under the source schedule (`[]` if the run does not
complete). -/
def trAt (d : Design2) (st0 : SvState) (stim : List SvState) : List SvState :=
  ((run2At d σ_src 64 st0 stim).toOption).getD []

/-- The power-up state of `d` with every bit 0. -/
def zeros (d : Design2) : SvState := d.decls.toList.map fun dc => (dc.name, LVec.ofNat dc.width 0)

/-- The power-up state of `d` with the signals `ns` all ones and every other bit 0. -/
def onesAt (d : Design2) (ns : List String) : SvState :=
  d.decls.toList.map fun dc => (dc.name, LVec.ofNat dc.width (if dc.name ∈ ns then 2 ^ dc.width - 1 else 0))

theorem powerUp_onesAt (d : Design2) (ns : List String) : PowerUp d (onesAt d ns) := by
  unfold PowerUp onesAt
  generalize d.decls.toList = ds
  refine ⟨by simp, ?_⟩
  induction ds with
  | nil => simp
  | cons dc ds ih =>
    intro b hb
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨LVec.width_ofNat _ _, LVec.allKnown_ofNat _ _⟩
    · exact ih b hb

theorem powerUp_zeros (d : Design2) : PowerUp d (zeros d) := by
  have : zeros d = onesAt d [] := by simp [zeros, onesAt]
  rw [this]; exact powerUp_onesAt d []

/-- The observation of snapshot `s + j` of `tr`. -/
def obsFn (w : Nat) (tr : List SvState) (s j : Nat) : Bool × BitVec w := obsOf w tr[s + j]?

/-- **The one-transaction refutation**, for every latency. `rows` is a prefix (`oneTxn`: a reset, one start at `s`,
its `count` values), evaluated from the power-up state `st0` (the trace `trAt d st0 (rows.map ent)`), and its last
snapshot is a fixed point of the idle entry that shows `out_valid` = 0. Then for every `lat` the run on `rows` and
`lat + 1` idle entries is that trace and copies of its last snapshot; the rely holds on it; and the guarantee for the
start `s` with the horizon at the end asks the snapshots from `s` on to emit `sortAsc` of the transaction's values,
while they emit what the prefix's snapshots from `s` on emit (`hbad`). -/
theorem stream_refuted {p : Params} {lat : Nat} {d : Design2} (st0 : SvState) (hpu : PowerUp d st0)
    (rows : List (Row (task.width p))) (s : Nat) (h1 : oneTxn rows s (task.count p) = true)
    (hq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (hks : KnownStim d (rows.map ent)) (hki : KnownEntry d (ent (idle (task.width p))))
    (hrun : run2At d σ_src 64 st0 (rows.map ent) = .ok (trAt d st0 (rows.map ent)))
    (hfix : ∀ k, cycleStep2 d σ_src 64 (ent (idle (task.width p))) (lastOr st0 (trAt d st0 (rows.map ent))) k =
      .ok (lastOr st0 (trAt d st0 (rows.map ent)), k + 3))
    (hrest : bitOf (lastOr st0 (trAt d st0 (rows.map ent))) "out_valid" = false)
    (hbad : task.emitted p (obsList (task.width p) (trAt d st0 (rows.map ent)) s (rows.length - s)) ≠
      task.spec p (((rows.drop (s + 1)).take (task.count p)).map (·.2.2.2))) :
    ¬ task.FollowsPU p lat d := fun hf => by
  obtain ⟨-, hs0, hsl⟩ := oneTxn_spec h1
  rw [run2At_eq hq] at hrun
  generalize trAt d st0 (rows.map ent) = trA at hrun hfix hrest hbad
  generalize hstF : lastOr st0 trA = stF at hfix hrest
  have hlenA : trA.length = rows.length := by simpa using runFrom2_length hrun
  have hstim : (full rows (lat + 1)).map ent =
      rows.map ent ++ List.replicate (lat + 1) (ent (idle (task.width p))) := by
    simp [full, List.map_replicate]
  have hrunF : RunsAt d σ_src st0 ((full rows (lat + 1)).map ent) (trA ++ List.replicate (lat + 1) stF) := by
    refine ⟨64, ?_⟩
    rw [run2At_eq hq, hstim]
    exact runFrom2_append hrun fun k' => by rw [hstF]; exact runFrom2_fixed hfix (lat + 1) k'
  have hksF : KnownStim d ((full rows (lat + 1)).map ent) := by
    rw [hstim]
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hks e he
    · rw [List.eq_of_mem_replicate he]; exact hki
  have hg := hf st0 hpu σ_src _ _ hksF hrunF 1 (rows.length + (lat + 1)) (released_one h1 (lat + 1))
    (rely_one h1 (lat + 1) _)
  -- the transaction's values
  obtain ⟨xs, hxs⟩ : ∃ xs, ((rows.drop (s + 1)).take (task.count p)).map (·.2.2.2) = xs := ⟨_, rfl⟩
  rw [hxs] at hbad
  have hxl : xs.length = task.count p := by rw [← hxs]; simp; omega
  have hxd : ∀ j v, xs[j]? = some v →
      ∃ e, ((full rows (lat + 1)).map ent)[s + 1 + j]? = some e ∧ task.DataIs p e task.inData v := by
    intro j v hj
    have hj' : j < task.count p := by have := (List.getElem?_eq_some_iff.mp hj).1; omega
    rw [← hxs] at hj
    simp only [List.getElem?_map, List.getElem?_take, List.getElem?_drop, if_pos hj'] at hj
    cases hr : rows[s + 1 + j]? with
    | none => simp [hr] at hj
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at hj
      subst hj
      exact ⟨ent r, by simp [List.getElem?_map, full_get_lt (show s + 1 + j < rows.length by omega), hr],
        lookup_ent_data r⟩
  -- the one start
  have hst : ∀ c, 1 ≤ c → c < rows.length + (lat + 1) →
      (StimBit ((full rows (lat + 1)).map ent) c "start" true ↔ c = s) := by
    intro c h1' h2'
    obtain ⟨r, hr, -, hrs, -⟩ := oneTxn_row h1 (lat + 1) h1' h2'
    rw [stimBit_rows (bitIs_ent_start · _)]
    constructor
    · rintro ⟨r', hr', hb⟩
      rw [hr] at hr'
      cases hr'
      simpa [hb] using hrs.symm
    · rintro rfl
      exact ⟨r, hr, by simpa using hrs⟩
  obtain ⟨obs, hol, hsh, hem, -⟩ := hg.2.2 s xs (by omega) (by omega) ((hst s (by omega) (by omega)).2 rfl)
    hxl hxd (rows.length + (lat + 1)) (by omega) (Nat.le_refl _)
    (fun s' h1' h2' hs' => by have := (hst s' (by omega) (by omega)).1 hs'; omega)
    (fun h => absurd h (Nat.lt_irrefl _))
  -- the observations are the trace's
  have hm : ∀ k o, obs[k]? = some o → o.1 = (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s k).1 ∧
      (o.1 = true → o.2 = (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s k).2) := by
    intro k o hk
    obtain ⟨st, hst', hb, hd⟩ := hsh k o hk
    simp only [obsFn, hst', obsOf]
    exact ⟨(bitOf_of_bitIs (n := "out_valid") hb).symm, fun ho => (dataOf_of (n := "out_data") (hd ho)).symm⟩
  have e1 := task.emitted_match obs _ hm
  have e2 : task.emitted p ((List.range obs.length).map (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s)) =
      task.emitted p ((List.range (rows.length - s)).map
        (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s)) := by
    refine task.emitted_stable (fun j hj => ?_) (by omega)
    simp only [obsFn]
    rw [List.getElem?_append_right (by omega)]
    cases hr : (List.replicate (lat + 1) stF)[s + j - trA.length]? with
    | none => rfl
    | some st =>
      rw [List.getElem?_replicate] at hr
      split at hr
      · cases hr; exact hrest
      · cases hr
  have e3 : (List.range (rows.length - s)).map (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s) =
      obsList (task.width p) trA s (rows.length - s) := by
    unfold obsList
    refine List.map_congr_left fun j hj => ?_
    simp only [List.mem_range] at hj
    simp only [obsFn, List.getElem?_append_left (show s + j < trA.length by omega)]
  exact hbad (by rw [← e3, ← e2, ← e1]; exact hem)

/-- **The early-output refutation**, for every latency: a run with no start (`rows`: a reset, then idle rows) whose
snapshot `c` after the release shows `out_valid` = 1, where the guarantee asks for 0 before the first start. -/
theorem early_refuted {p : Params} {lat : Nat} {d : Design2} (st0 : SvState) (hpu : PowerUp d st0)
    (rows : List (Row (task.width p))) (c : Nat)
    (h0 : rows[0]?.map (·.1) = some true)
    (hidle : ∀ j, j < rows.length → 1 ≤ j → rows[j]? = some (idle (task.width p)))
    (hc : 1 ≤ c ∧ c < rows.length)
    (hks : KnownStim d (rows.map ent))
    (hrun : run2At d σ_src 64 st0 (rows.map ent) = .ok (trAt d st0 (rows.map ent)))
    (hv : (trAt d st0 (rows.map ent))[c]?.map (bitOf · "out_valid") = some true) :
    ¬ task.FollowsPU p lat d := fun hf => by
  have hrel : Released "rst" (rows.map ent) 1 rows.length := by
    refine ⟨by decide, ?_, fun j h1 h2 => ?_⟩
    · refine (stimBit_rows (bitIs_ent_rst · _)).2 ?_
      cases hr : rows[0]? with
      | none => simp [hr] at h0
      | some r => simp only [hr, Option.map_some, Option.some.injEq] at h0; exact ⟨r, rfl, h0⟩
    · exact (stimBit_rows (bitIs_ent_rst · _)).2 ⟨_, hidle j h2 h1, rfl⟩
  have hnost : ∀ j, 1 ≤ j → j < rows.length → ¬ StimBit (rows.map ent) j "start" true := by
    intro j h1 h2 hb
    obtain ⟨r, hr, hb⟩ := (stimBit_rows (bitIs_ent_start · _)).1 hb
    rw [hidle j h2 h1] at hr; cases hr; simp [idle] at hb
  have hrely : task.Rely p (rows.map ent) (trAt d st0 (rows.map ent)) 1 rows.length := by
    intro j h1 h2
    refine ⟨⟨false, (stimBit_rows (bitIs_ent_start · _)).2 ⟨_, hidle j h2 h1, rfl⟩⟩,
      ⟨ent (idle _), 0#_, by simp [hidle j h2 h1], lookup_ent_data _⟩,
      fun hb => absurd hb (hnost j h1 h2), fun s' h1' h2' _ hs' => absurd hs' (hnost s' h1' (by omega)),
      fun _ => (stimBit_rows (bitIs_ent_valid · _)).2 ⟨_, hidle j h2 h1, rfl⟩⟩
  have hg := hf st0 hpu σ_src _ _ hks ⟨64, hrun⟩ 1 rows.length hrel hrely
  obtain ⟨st, hst, hb⟩ := hg.2.1 c hc.1 hc.2 fun s' h1' h2' => hnost s' h1' (by omega)
  rw [hst, Option.map_some, Option.some.injEq, bitOf_of_bitIs (n := "out_valid") hb] at hv
  cases hv

/-! ## The refutations as one decided check each -/

/-- Every hypothesis of `stream_refuted` but `PowerUp`, decided at once (one `decide +kernel` per refutation). -/
def streamCheck {p : Params} (d : Design2) (st0 : SvState) (rows : List (Row (task.width p))) (s : Nat) : Bool :=
  oneTxn rows s (task.count p) && !(d.processes.toList.any Process2.hasQualifiedCase) &&
    decide (KnownStim d (rows.map ent)) && decide (KnownEntry d (ent (idle (task.width p)))) &&
    decide (run2At d σ_src 64 st0 (rows.map ent) = .ok (trAt d st0 (rows.map ent))) && d.ffOnlyProfileB &&
    d.processes.toList.all (keeps 64 (applyInputs2 d (ent (idle (task.width p)))
      (lastOr st0 (trAt d st0 (rows.map ent))))) &&
    decide (((applyInputs2 d (ent (idle (task.width p))) (lastOr st0 (trAt d st0 (rows.map ent)))).map
      Prod.fst).Nodup) &&
    decide (clockStep d 64 (applyInputs2 d (ent (idle (task.width p))) (lastOr st0 (trAt d st0 (rows.map ent))))
      d.edgeIndices = lastOr st0 (trAt d st0 (rows.map ent))) &&
    !bitOf (lastOr st0 (trAt d st0 (rows.map ent))) "out_valid" &&
    decide (task.emitted p (obsList (task.width p) (trAt d st0 (rows.map ent)) s (rows.length - s)) ≠
      task.spec p (((rows.drop (s + 1)).take (task.count p)).map (·.2.2.2)))

theorem stream_refuted_of_check {p : Params} {d : Design2} {st0 : SvState} (hpu : PowerUp d st0)
    {rows : List (Row (task.width p))} {s : Nat} (h : streamCheck d st0 rows s = true) (lat : Nat) :
    ¬ task.FollowsPU p lat d := by
  simp only [streamCheck, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hq⟩, hks⟩, hki⟩, hrun⟩, hp⟩, hk⟩, hnd⟩, hfix⟩, hrest⟩, hbad⟩ := h
  exact stream_refuted st0 hpu rows s h1 hq hks hki hrun (cycleStep2_fixed hp hk hnd hfix) hrest hbad

/-- Every hypothesis of `early_refuted` but `PowerUp`, decided at once. -/
def earlyCheck {p : Params} (d : Design2) (st0 : SvState) (rows : List (Row (task.width p))) (c : Nat) : Bool :=
  (rows[0]?.map (·.1) == some true) &&
    (List.range rows.length).all (fun j => j == 0 || rows[j]? == some (idle (task.width p))) &&
    decide (1 ≤ c ∧ c < rows.length) && decide (KnownStim d (rows.map ent)) &&
    decide (run2At d σ_src 64 st0 (rows.map ent) = .ok (trAt d st0 (rows.map ent))) &&
    ((trAt d st0 (rows.map ent))[c]?.map (bitOf · "out_valid") == some true)

theorem early_refuted_of_check {p : Params} {d : Design2} {st0 : SvState} (hpu : PowerUp d st0)
    {rows : List (Row (task.width p))} {c : Nat} (h : earlyCheck d st0 rows c = true) (lat : Nat) :
    ¬ task.FollowsPU p lat d := by
  simp only [earlyCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, hidle⟩, hc⟩, hks⟩, hrun⟩, hv⟩ := h
  refine early_refuted st0 hpu rows c h0 (fun j hj h1 => ?_) hc hks hrun hv
  rcases hidle j hj with h | h
  · omega
  · exact h

/-! ## Two transactions (an attack that is wrong only from the second) -/

/-- The rows of a two-transaction prefix, decided: row 0 resets; every later row deasserts `rst`, starts exactly at
rows `s1` and `s2` (`s1 + n < s2`), and has `in_valid` = 1 exactly at the `n` rows after each start. -/
def twoTxn {W : Nat} (rows : List (Row W)) (s1 s2 n : Nat) : Bool :=
  (rows[0]?.map (·.1) == some true) && 0 < s1 && s1 + n < s2 && s2 + 1 + n ≤ rows.length &&
    (List.range rows.length).all fun c => c == 0 || match rows[c]? with
      | some r => !r.1 && r.2.1 == (c == s1 || c == s2) &&
          r.2.2.1 == decide ((s1 < c ∧ c ≤ s1 + n) ∨ (s2 < c ∧ c ≤ s2 + n))
      | none => false

theorem twoTxn_spec {W : Nat} {rows : List (Row W)} {s1 s2 n : Nat} (h : twoTxn rows s1 s2 n = true) :
    rows[0]?.map (·.1) = some true ∧ 0 < s1 ∧ s1 + n < s2 ∧ s2 + 1 + n ≤ rows.length := by
  simp only [twoTxn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem twoTxn_row {W : Nat} {rows : List (Row W)} {s1 s2 n : Nat} (h : twoTxn rows s1 s2 n = true) (L : Nat)
    {c : Nat} (h1 : 1 ≤ c) (h2 : c < rows.length + L) :
    ∃ r, (full rows L)[c]? = some r ∧ r.1 = false ∧ r.2.1 = (c == s1 || c == s2) ∧
      r.2.2.1 = decide ((s1 < c ∧ c ≤ s1 + n) ∨ (s2 < c ∧ c ≤ s2 + n)) := by
  obtain ⟨-, -, h12, hl⟩ := twoTxn_spec h
  simp only [twoTxn, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hall := h.2
  rcases Nat.lt_or_ge c rows.length with hc | hc
  · have := hall c hc
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h0 | this
    · omega
    · rw [full_get_lt hc]
      cases hr : rows[c]? with
      | none => simp [hr] at this
      | some r =>
        simp only [hr, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at this
        exact ⟨r, rfl, this.1.1, this.1.2, this.2⟩
  · refine ⟨idle W, full_get hc h2, rfl, ?_, ?_⟩
    · simp [idle]; omega
    · simp [idle]; omega

/-- The snapshots `s .. s + m - 1` of `tr` show known observations: `out_valid` a known bit, and `out_data` a known
value where it is 1 (so `obsList` is what they show), decided. -/
def showsB (w : Nat) (tr : List SvState) (s m : Nat) : Bool :=
  (List.range m).all fun k => match tr[s + k]? with
    | some st => (SvState.lookup st "out_valid" == some (LVec.ofBitVec (BitVec.ofBool (bitOf st "out_valid")))) &&
        (!bitOf st "out_valid" || SvState.lookup st "out_data" == some (LVec.ofBitVec (dataOf w st "out_data")))
    | none => false

theorem shows_of_showsB {p : Params} {tr trB : List SvState} {s m : Nat}
    (h : showsB (task.width p) tr s m = true) (hlt : s + m ≤ tr.length) :
    task.Shows p (tr ++ trB) s (obsList (task.width p) tr s m) := by
  intro k o hk
  have hkm : k < m := by simpa [obsList] using (List.getElem?_eq_some_iff.mp hk).1
  simp only [obsList, List.getElem?_map, List.getElem?_range hkm, Option.map_some, Option.some.injEq] at hk
  simp only [showsB, List.all_eq_true, List.mem_range] at h
  have hk' := h k hkm
  cases hst : tr[s + k]? with
  | none => rw [hst] at hk'; cases hk'
  | some st =>
    rw [hst] at hk'
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hk'
    rw [hst] at hk
    subst hk
    refine ⟨st, by rw [List.getElem?_append_left (by omega), hst], hk'.1, fun hv => ?_⟩
    rcases hk'.2 with h' | h'
    · simp [obsOf] at hv; rw [hv] at h'; cases h'
    · exact h'

/-- **The rely holds** on `full rows L` (two starts) from the release `1`, at the horizon `rows.length + L`, for a
trace whose snapshots from `s1` to before `s2` show the first transaction's `count` outputs (`Idle` at `s2`). -/
theorem rely_two {p : Params} {rows : List (Row (task.width p))} {s1 s2 : Nat}
    (h : twoTxn rows s1 s2 (task.count p) = true) (L : Nat) (tr : List SvState)
    (hidle : ∃ obs : List (task.Obs p), s1 + obs.length ≤ s2 ∧ task.Shows p tr s1 obs ∧
      (task.emitted p obs).length = task.count p) :
    task.Rely p ((full rows L).map ent) tr 1 (rows.length + L) := by
  obtain ⟨-, hs1, h12, hl⟩ := twoTxn_spec h
  have hstart : ∀ c, 1 ≤ c → c < rows.length + L → StimBit ((full rows L).map ent) c "start" true →
      c = s1 ∨ c = s2 := by
    intro c h1 h2 hc
    obtain ⟨r, hr, -, hrs, -⟩ := twoTxn_row h L h1 h2
    obtain ⟨r', hr', hb⟩ := (stimBit_rows (f := fun r => r.2.1) (bitIs_ent_start · true)).1 hc
    rw [hr] at hr'; cases hr'
    simpa [hb] using hrs.symm
  have hstartI : ∀ c, c = s1 ∨ c = s2 → StimBit ((full rows L).map ent) c "start" true := by
    intro c hc
    obtain ⟨r, hr, -, hrs, -⟩ := twoTxn_row h L (c := c) (by omega) (by omega)
    exact (stimBit_rows (bitIs_ent_start · _)).2 ⟨r, hr, by rw [hrs]; rcases hc with rfl | rfl <;> simp⟩
  intro c h1 h2
  obtain ⟨r, hr, -, hrs, hrv⟩ := twoTxn_row h L h1 h2
  refine ⟨⟨r.2.1, (stimBit_rows (bitIs_ent_start · _)).2 ⟨r, hr, rfl⟩⟩,
    ⟨ent r, r.2.2.2, by simp [hr], lookup_ent_data r⟩, ?_, ?_, ?_⟩
  · intro hc s' h1' h2' hs'
    rcases hstart c h1 h2 hc with rfl | rfl <;> rcases hstart s' h1' (by omega) hs' with rfl | rfl
    · omega
    · omega
    · exact hidle
    · omega
  · intro s' h1' h2' h3' hs'
    refine (stimBit_rows (bitIs_ent_valid · _)).2 ⟨r, hr, ?_⟩
    simp only [hrv, decide_eq_true_eq]
    rcases hstart s' h1' (by omega) hs' with rfl | rfl <;> omega
  · intro hno
    refine (stimBit_rows (bitIs_ent_valid · _)).2 ⟨r, hr, ?_⟩
    rw [hrv]
    simp only [decide_eq_false_iff_not, not_or, not_and, Nat.not_le]
    refine ⟨fun ha => ?_, fun hb => ?_⟩
    · rcases Nat.lt_or_ge (s1 + task.count p) c with hlt | hle
      · exact hlt
      · exact absurd (hstartI s1 (.inl rfl)) (hno s1 (by omega) ha hle)
    · rcases Nat.lt_or_ge (s2 + task.count p) c with hlt | hle
      · exact hlt
      · exact absurd (hstartI s2 (.inr rfl)) (hno s2 (by omega) hb hle)

theorem released_two {W : Nat} {rows : List (Row W)} {s1 s2 n : Nat} (h : twoTxn rows s1 s2 n = true) (L : Nat) :
    Released "rst" ((full rows L).map ent) 1 (rows.length + L) := by
  obtain ⟨h0, -, -, hl⟩ := twoTxn_spec h
  refine ⟨by decide, ?_, fun c h1 h2 => ?_⟩
  · refine (stimBit_rows (bitIs_ent_rst · _)).2 ?_
    cases hr : rows[0]? with
    | none => simp [hr] at h0
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at h0
      exact ⟨r, by rw [full_get_lt (by omega)]; exact hr, h0⟩
  · obtain ⟨r, hr, hrr, -, -⟩ := twoTxn_row h L h1 h2
    exact (stimBit_rows (bitIs_ent_rst · _)).2 ⟨r, hr, hrr⟩

/-- **The refutation at the second transaction**, for every latency: as `stream_refuted`, with two starts `s1`,
`s2`; the snapshots from `s1` to before `s2` show the first transaction's `count` outputs (so `s2` is `Idle`), and
the snapshots from `s2` on emit what the prefix's do, which is not `sortAsc` of the second transaction's values. -/
theorem stream2_refuted {p : Params} {lat : Nat} {d : Design2} (st0 : SvState) (hpu : PowerUp d st0)
    (rows : List (Row (task.width p))) (s1 s2 : Nat) (h1 : twoTxn rows s1 s2 (task.count p) = true)
    (hq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (hks : KnownStim d (rows.map ent)) (hki : KnownEntry d (ent (idle (task.width p))))
    (hrun : run2At d σ_src 64 st0 (rows.map ent) = .ok (trAt d st0 (rows.map ent)))
    (hfix : ∀ k, cycleStep2 d σ_src 64 (ent (idle (task.width p))) (lastOr st0 (trAt d st0 (rows.map ent))) k =
      .ok (lastOr st0 (trAt d st0 (rows.map ent)), k + 3))
    (hrest : bitOf (lastOr st0 (trAt d st0 (rows.map ent))) "out_valid" = false)
    (hsh1 : showsB (task.width p) (trAt d st0 (rows.map ent)) s1 (s2 - s1) = true)
    (hn1 : (task.emitted p (obsList (task.width p) (trAt d st0 (rows.map ent)) s1 (s2 - s1))).length = task.count p)
    (hbad : task.emitted p (obsList (task.width p) (trAt d st0 (rows.map ent)) s2 (rows.length - s2)) ≠
      task.spec p (((rows.drop (s2 + 1)).take (task.count p)).map (·.2.2.2))) :
    ¬ task.FollowsPU p lat d := fun hf => by
  obtain ⟨-, hs0, h12, hsl⟩ := twoTxn_spec h1
  rw [run2At_eq hq] at hrun
  generalize trAt d st0 (rows.map ent) = trA at hrun hfix hrest hbad hsh1 hn1
  generalize hstF : lastOr st0 trA = stF at hfix hrest
  have hlenA : trA.length = rows.length := by simpa using runFrom2_length hrun
  have hstim : (full rows (lat + 1)).map ent =
      rows.map ent ++ List.replicate (lat + 1) (ent (idle (task.width p))) := by
    simp [full, List.map_replicate]
  have hrunF : RunsAt d σ_src st0 ((full rows (lat + 1)).map ent) (trA ++ List.replicate (lat + 1) stF) := by
    refine ⟨64, ?_⟩
    rw [run2At_eq hq, hstim]
    exact runFrom2_append hrun fun k' => by rw [hstF]; exact runFrom2_fixed hfix (lat + 1) k'
  have hksF : KnownStim d ((full rows (lat + 1)).map ent) := by
    rw [hstim]
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hks e he
    · rw [List.eq_of_mem_replicate he]; exact hki
  have hidle : ∃ obs : List (task.Obs p), s1 + obs.length ≤ s2 ∧
      task.Shows p (trA ++ List.replicate (lat + 1) stF) s1 obs ∧ (task.emitted p obs).length = task.count p :=
    ⟨obsList (task.width p) trA s1 (s2 - s1), by simp [obsList]; omega, shows_of_showsB hsh1 (by omega), hn1⟩
  have hg := hf st0 hpu σ_src _ _ hksF hrunF 1 (rows.length + (lat + 1)) (released_two h1 (lat + 1))
    (rely_two h1 (lat + 1) _ hidle)
  obtain ⟨xs, hxs⟩ : ∃ xs, ((rows.drop (s2 + 1)).take (task.count p)).map (·.2.2.2) = xs := ⟨_, rfl⟩
  rw [hxs] at hbad
  have hxl : xs.length = task.count p := by rw [← hxs]; simp; omega
  have hxd : ∀ j v, xs[j]? = some v →
      ∃ e, ((full rows (lat + 1)).map ent)[s2 + 1 + j]? = some e ∧ task.DataIs p e task.inData v := by
    intro j v hj
    have hj' : j < task.count p := by have := (List.getElem?_eq_some_iff.mp hj).1; omega
    rw [← hxs] at hj
    simp only [List.getElem?_map, List.getElem?_take, List.getElem?_drop, if_pos hj'] at hj
    cases hr : rows[s2 + 1 + j]? with
    | none => simp [hr] at hj
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at hj
      subst hj
      exact ⟨ent r, by simp [List.getElem?_map, full_get_lt (show s2 + 1 + j < rows.length by omega), hr],
        lookup_ent_data r⟩
  have hst : ∀ c, 1 ≤ c → c < rows.length + (lat + 1) →
      (StimBit ((full rows (lat + 1)).map ent) c "start" true ↔ c = s1 ∨ c = s2) := by
    intro c h1' h2'
    obtain ⟨r, hr, -, hrs, -⟩ := twoTxn_row h1 (lat + 1) h1' h2'
    rw [stimBit_rows (bitIs_ent_start · _)]
    constructor
    · rintro ⟨r', hr', hb⟩
      rw [hr] at hr'
      cases hr'
      simpa [hb] using hrs.symm
    · intro hc
      exact ⟨r, hr, by rw [hrs]; rcases hc with rfl | rfl <;> simp⟩
  obtain ⟨obs, hol, hsh, hem, -⟩ := hg.2.2 s2 xs (by omega) (by omega) ((hst s2 (by omega) (by omega)).2 (.inr rfl))
    hxl hxd (rows.length + (lat + 1)) (by omega) (Nat.le_refl _)
    (fun s' h1' h2' hs' => by have := (hst s' (by omega) (by omega)).1 hs'; omega)
    (fun h => absurd h (Nat.lt_irrefl _))
  have hm : ∀ k o, obs[k]? = some o → o.1 = (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s2 k).1 ∧
      (o.1 = true → o.2 = (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s2 k).2) := by
    intro k o hk
    obtain ⟨st, hst', hb, hd⟩ := hsh k o hk
    simp only [obsFn, hst', obsOf]
    exact ⟨(bitOf_of_bitIs (n := "out_valid") hb).symm, fun ho => (dataOf_of (n := "out_data") (hd ho)).symm⟩
  have e1 := task.emitted_match obs _ hm
  have e2 : task.emitted p ((List.range obs.length).map (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s2)) =
      task.emitted p ((List.range (rows.length - s2)).map
        (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s2)) := by
    refine task.emitted_stable (fun j hj => ?_) (by omega)
    simp only [obsFn]
    rw [List.getElem?_append_right (by omega)]
    cases hr : (List.replicate (lat + 1) stF)[s2 + j - trA.length]? with
    | none => rfl
    | some st =>
      rw [List.getElem?_replicate] at hr
      split at hr
      · cases hr; exact hrest
      · cases hr
  have e3 : (List.range (rows.length - s2)).map (obsFn (task.width p) (trA ++ List.replicate (lat + 1) stF) s2) =
      obsList (task.width p) trA s2 (rows.length - s2) := by
    unfold obsList
    refine List.map_congr_left fun j hj => ?_
    simp only [List.mem_range] at hj
    simp only [obsFn, List.getElem?_append_left (show s2 + j < trA.length by omega)]
  exact hbad (by rw [← e3, ← e2, ← e1]; exact hem)

/-- Every hypothesis of `stream2_refuted` but `PowerUp`, decided at once. -/
def stream2Check {p : Params} (d : Design2) (st0 : SvState) (rows : List (Row (task.width p))) (s1 s2 : Nat) : Bool :=
  twoTxn rows s1 s2 (task.count p) && !(d.processes.toList.any Process2.hasQualifiedCase) &&
    decide (KnownStim d (rows.map ent)) && decide (KnownEntry d (ent (idle (task.width p)))) &&
    decide (run2At d σ_src 64 st0 (rows.map ent) = .ok (trAt d st0 (rows.map ent))) && d.ffOnlyProfileB &&
    d.processes.toList.all (keeps 64 (applyInputs2 d (ent (idle (task.width p)))
      (lastOr st0 (trAt d st0 (rows.map ent))))) &&
    decide (((applyInputs2 d (ent (idle (task.width p))) (lastOr st0 (trAt d st0 (rows.map ent)))).map
      Prod.fst).Nodup) &&
    decide (clockStep d 64 (applyInputs2 d (ent (idle (task.width p))) (lastOr st0 (trAt d st0 (rows.map ent))))
      d.edgeIndices = lastOr st0 (trAt d st0 (rows.map ent))) &&
    !bitOf (lastOr st0 (trAt d st0 (rows.map ent))) "out_valid" &&
    showsB (task.width p) (trAt d st0 (rows.map ent)) s1 (s2 - s1) &&
    ((task.emitted p (obsList (task.width p) (trAt d st0 (rows.map ent)) s1 (s2 - s1))).length == task.count p) &&
    decide (task.emitted p (obsList (task.width p) (trAt d st0 (rows.map ent)) s2 (rows.length - s2)) ≠
      task.spec p (((rows.drop (s2 + 1)).take (task.count p)).map (·.2.2.2)))

theorem stream2_refuted_of_check {p : Params} {d : Design2} {st0 : SvState} (hpu : PowerUp d st0)
    {rows : List (Row (task.width p))} {s1 s2 : Nat} (h : stream2Check d st0 rows s1 s2 = true) (lat : Nat) :
    ¬ task.FollowsPU p lat d := by
  simp only [stream2Check, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hq⟩, hks⟩, hki⟩, hrun⟩, hp⟩, hk⟩, hnd⟩, hfix⟩, hrest⟩, hsh⟩, hn⟩, hbad⟩ := h
  exact stream2_refuted st0 hpu rows s1 s2 h1 hq hks hki hrun (cycleStep2_fixed hp hk hnd hfix) hrest hsh hn hbad

/-! ## The reference's twin at `(N, W) = (2, 2)`, with the parts a mutant or an attack changes as arguments -/

/-- A `W = 2` constant. -/
def c2 (v : Nat) : Expr2 := .lit (LVec.ofNat 2 v)
/-- A 1-bit constant. -/
def c1 (v : Nat) : Expr2 := .lit (LVec.ofNat 1 v)
/-- `data[lo +: 2]` read. -/
def dR (lo : Nat) : Expr2 := .slice (.ident "data") lo 2
/-- `data[lo +: 2] <= e`. -/
def dW (lo : Nat) (e : Expr2) : Stmt2 := .nbaAssign (.slice "data" lo 2) e
/-- `tok[i] <= e`. -/
def tW (i : Nat) (e : Expr2) : Stmt2 := .nbaAssign (.slice "tok" i 1) e
/-- `tok[i]` read. -/
def tR (i : Nat) : Expr2 := .slice (.ident "tok") i 1

/-- The declarations of `sorter_ins.sv` at `(2, 2)`: the ports, then `data`, `tok`. -/
def sDecls : Array Decl :=
  #[{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
    { name := "start", width := 1, isInput := true }, { name := "in_valid", width := 1, isInput := true },
    { name := "in_data", width := 2, isInput := true }, { name := "out_valid", width := 1, isOutput := true },
    { name := "out_data", width := 2, isOutput := true }, { name := "data", width := 4 },
    { name := "tok", width := 2 }]

/-- `in_data > e` for the input expression `ie`. -/
def gtE (ie e : Expr2) : Expr2 := .binary .gt ie e

/-- A cell's process: `if (<cond>) <ins> else <drain>; <tok>; if (rst) <rst>` (the top cell and the generate family's
cell have this shape). -/
def cellShape (cond : Expr2) (ins : Stmt2) (drain : Option Stmt2) (tok rst : Stmt2) : Process2 :=
  .alwaysFF "clk" (.block #[.ifStmt cond ins drain, tok, .ifStmt (.ident "rst") rst none])

/-- The top cell's insert: `if (in_data > data[2 +: 2]) data[2 +: 2] <= in_data;` (`ie` reads `in_data`). -/
def topInsE (ie : Expr2) : Stmt2 := .block #[.ifStmt (gtE ie (dR 2)) (dW 2 ie) none]
def topIns : Stmt2 := topInsE (.ident "in_data")
def topDrain : Stmt2 := dW 2 (c2 0)
def topTok : Stmt2 := tW 1 (.ident "in_valid")
def topRst : Stmt2 := .block #[dW 2 (c2 0), tW 1 (c1 0)]

/-- The output: `out_valid <= <ov>; out_data <= <od>; if (rst) <rst>`. -/
def outP (ov od : Stmt2) (rst : Stmt2) : Process2 :=
  .alwaysFF "clk" (.block #[ov, od, .ifStmt (.ident "rst") rst none])

def outOv : Stmt2 := .nbaAssign (.ident "out_valid") (tR 0)
def outOd : Stmt2 := .nbaAssign (.ident "out_data") (dR 0)
def outRst : Stmt2 := .nbaAssign (.ident "out_valid") (c1 0)

/-- Cell 0's insert: `if (in_data > data[2 +: 2]) data[0 +: 2] <= data[2 +: 2]; else if (in_data > data[0 +: 2])
data[0 +: 2] <= in_data;`, with the first test `t1`, the push `push`, the second test `t2` and the store `store`. -/
def cellInsW (t1 : Expr2) (push : Stmt2) (t2 : Expr2) (store : Stmt2) : Stmt2 :=
  .block #[.ifStmt t1 push (some (.ifStmt t2 store none))]
def cellT1 : Expr2 := gtE (.ident "in_data") (dR 2)
def cellPush : Stmt2 := dW 0 (dR 2)
def cellT2 : Expr2 := gtE (.ident "in_data") (dR 0)
def cellStore : Stmt2 := dW 0 (.ident "in_data")
def cellIns : Stmt2 := cellInsW cellT1 cellPush cellT2 cellStore
def cellDrain : Stmt2 := dW 0 (dR 2)
def cellTok : Stmt2 := tW 0 (tR 1)
def cellRst : Stmt2 := .block #[dW 0 (c2 0), tW 0 (c1 0)]

/-- The design with the given declarations and processes (the loader's order: the top cell, the output, then the
generate family). -/
def sWithD (decls : Array Decl) (top out cell : Process2) : Design2 :=
  { name := "sorter", decls, processes := #[top, out, cell] }

/-- The design with the reference's declarations. -/
def sWith (top out cell : Process2) : Design2 := sWithD sDecls top out cell

def topRef : Process2 := cellShape (.ident "in_valid") topIns (some topDrain) topTok topRst
def outRef : Process2 := outP outOv outOd outRst
def cellRef : Process2 := cellShape (.ident "in_valid") cellIns (some cellDrain) cellTok cellRst

/-- The reference `sorter_ins.sv` at `(2, 2)`. -/
def refD : Design2 := sWith topRef outRef cellRef

/-- The top cell with one part changed. -/
def topWith (cond : Expr2 := .ident "in_valid") (ins : Stmt2 := topIns) (drain : Option Stmt2 := some topDrain)
    (tok : Stmt2 := topTok) (rst : Stmt2 := topRst) : Process2 := cellShape cond ins drain tok rst

/-- Cell 0 with one part changed. -/
def cellWith (cond : Expr2 := .ident "in_valid") (ins : Stmt2 := cellIns) (drain : Option Stmt2 := some cellDrain)
    (tok : Stmt2 := cellTok) (rst : Stmt2 := cellRst) : Process2 := cellShape cond ins drain tok rst

/-- The null statement `;` (the loader reads it as an empty block). -/
def nop : Stmt2 := .block #[]

load_sv refL from "tasks/sorter/reference/sorter_ins.sv"

#guard reprStr (refL.sem 2 2) == reprStr refD

/-- `(2, 2)` is in range. -/
theorem p22_inRange : task.inRange (2, 2) := by simp [task]

/-! ### The reference's twin at `(N, 2)` for every `N ≥ 2` (the generate family of `N - 1` cells) -/

/-- The declarations at `(N, 2)`. -/
def sDeclsN (N : Nat) : Array Decl :=
  #[{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
    { name := "start", width := 1, isInput := true }, { name := "in_valid", width := 1, isInput := true },
    { name := "in_data", width := 2, isInput := true }, { name := "out_valid", width := 1, isOutput := true },
    { name := "out_data", width := 2, isOutput := true }, { name := "data", width := 2 * N },
    { name := "tok", width := N }]

/-- The top cell `N - 1` at `(N, 2)`. -/
def topN (N : Nat) : Process2 :=
  cellShape (.ident "in_valid") (topInsE' (2 * (N - 1))) (some (dW (2 * (N - 1)) (c2 0))) (tW (N - 1) (.ident "in_valid"))
    (.block #[dW (2 * (N - 1)) (c2 0), tW (N - 1) (c1 0)])
where
  topInsE' (lo : Nat) : Stmt2 := .block #[.ifStmt (gtE (.ident "in_data") (dR lo)) (dW lo (.ident "in_data")) none]

/-- Cell `k < N - 1`, with the reset branch `rst` (the reference's: `cellRstK k`). -/
def cellK (rst : Nat → Stmt2) (k : Nat) : Process2 :=
  cellShape (.ident "in_valid")
    (cellInsW (gtE (.ident "in_data") (dR (2 * k + 2))) (dW (2 * k) (dR (2 * k + 2))) (gtE (.ident "in_data") (dR (2 * k)))
      (dW (2 * k) (.ident "in_data")))
    (some (dW (2 * k) (dR (2 * k + 2)))) (tW k (tR (k + 1))) (rst k)

def cellRstK (k : Nat) : Stmt2 := .block #[dW (2 * k) (c2 0), tW k (c1 0)]

/-- The design at `(N, 2)` with the cells' reset branches `rst`. -/
def sN (N : Nat) (rst : Nat → Stmt2) : Design2 :=
  { name := "sorter", decls := sDeclsN N,
    processes := (topN N :: outRef :: (List.range (N - 1)).map (cellK rst)).toArray }

/-- The reference at `(N, 2)`. -/
def refDN (N : Nat) : Design2 := sN N cellRstK

#guard reprStr (refDN 2) == reprStr refD
#guard reprStr (refL.sem 3 2) == reprStr (refDN 3)

/-- The refutation at `(2, 2)` of every family whose instance there is `d`, for every latency function. -/
theorem refuted_of_sat {d : Design2} (h : ∀ lat, ¬ task.SatisfiedAtV2 (2, 2) lat d) (sem : Nat → Nat → Design2)
    (lat : Nat → Nat → Nat) (hd : sem 2 2 = d) : ¬ Statement sem lat := fun hs => by
  have hf : task.SatisfiedAtV2 (2, 2) (lat 2 2) (sem 2 2) := hs (2, 2) p22_inRange
  rw [hd] at hf
  exact h _ hf

/-- The refutation at `(N, 2)` of every family whose instance there is `d`, from `¬ FollowsPU` there. -/
theorem refuted_at {N : Nat} (hN : task.inRange (N, 2)) {d : Design2} (h : ∀ lat, ¬ task.FollowsPU (N, 2) lat d)
    (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem N 2 = d) : ¬ Statement sem lat := fun hs => by
  have hf : task.FollowsPU (N, 2) (lat N 2) (sem N 2) := (hs (N, 2) hN).2.2.2.1
  rw [hd] at hf
  exact h _ hf

/-- The same from `¬ FollowsPU` (rule 2's claims) at `(2, 2)`. -/
theorem refuted_of {d : Design2} (h : ∀ lat, ¬ task.FollowsPU (2, 2) lat d) (sem : Nat → Nat → Design2)
    (lat : Nat → Nat → Nat) (hd : sem 2 2 = d) : ¬ Statement sem lat :=
  refuted_of_sat (fun lat hs => h lat hs.2.2.2.1) sem lat hd

/-- A reset, a start, the values `x0`, `x1`, then six idle rows (the design is at rest after them). -/
def rowsTxn (x0 x1 : BitVec 2) : List (Row 2) :=
  [(true, false, false, 0#2), (false, true, false, 0#2), (false, false, true, x0), (false, false, true, x1)] ++
    List.replicate 6 (idle 2)

/-! ## The attacks of `tests/sorter/attacks/` (each one change of the reference; twins checked as above) -/

/-- `early_valid.sv`: the valid token enters with the start, `tok[N-1] <= in_valid | start`. -/
def earlyValidD : Design2 :=
  sWith (topWith (tok := tW 1 (.binary .or (.ident "in_valid") (.ident "start")))) outRef cellRef

/-- `missing_else.sv`: the cell's second test lost its `else`. -/
def missingElseD : Design2 :=
  sWith topRef outRef (cellWith (ins := .block #[.ifStmt cellT1 cellPush none, .ifStmt cellT2 cellStore none]))

/-- `push_own_value.sv`: the push test compares the input with the cell's own value. -/
def pushOwnValueD : Design2 :=
  sWith topRef outRef (cellWith (ins := cellInsW (gtE (.ident "in_data") (dR 0)) cellPush cellT2 cellStore))

/-- `signed_order.sv`: the three comparisons are signed (`$signed(in_data) > $signed(data[…])`). -/
def signedOrderD : Design2 :=
  sWith (topWith (ins := .block #[.ifStmt (.scmp .gt (.ident "in_data") (dR 2)) (dW 2 (.ident "in_data")) none]))
    outRef (cellWith (ins := cellInsW (.scmp .gt (.ident "in_data") (dR 2)) cellPush
      (.scmp .gt (.ident "in_data") (dR 0)) cellStore))

/-- `token_self.sv`: the token shift reads the cell's own token, `tok[k] <= tok[k]`. -/
def tokenSelfD : Design2 := sWith topRef outRef (cellWith (tok := tW 0 (tR 0)))

/-- `reset_keeps_cells.sv` at `(3, 2)`: the reset clears the tokens and the top cell but not cells `0 .. N-2`. -/
def resetKeepsCellsD : Design2 := sN 3 fun k => .block #[tW k (c1 0)]

/-- `top_not_drained.sv`: the top cell's drain `else` branch is gone (it keeps the transaction's maximum). -/
def topNotDrainedD : Design2 := sWith (topWith (drain := none)) outRef cellRef

/-- `rst_gate.sv`: the outputs registered as `ov_q` and `od_q`, `out_valid` the reset-gated `ov_q`
(`assign out_valid = ov_q & ~rst`), `out_data` a copy of `od_q`. -/
def rstGateD : Design2 :=
  { name := "sorter", decls := sDecls ++ #[{ name := "ov_q", width := 1 }, { name := "od_q", width := 2 }],
    processes := #[topRef,
      outP (.nbaAssign (.ident "ov_q") (tR 0)) (.nbaAssign (.ident "od_q") (dR 0)) (.nbaAssign (.ident "ov_q") (c1 0)),
      .assign (.ident "out_valid") (.binary .and (.ident "ov_q") (.unary .bnot (.ident "rst"))),
      .assign (.ident "out_data") (.ident "od_q"), cellRef] }

load_sv earlyValidL from "tests/sorter/attacks/early_valid.sv"
load_sv missingElseL from "tests/sorter/attacks/missing_else.sv"
load_sv pushOwnValueL from "tests/sorter/attacks/push_own_value.sv"
load_sv signedOrderL from "tests/sorter/attacks/signed_order.sv"
load_sv tokenSelfL from "tests/sorter/attacks/token_self.sv"
load_sv resetKeepsCellsL from "tests/sorter/attacks/reset_keeps_cells.sv"
load_sv topNotDrainedL from "tests/sorter/attacks/top_not_drained.sv"
load_sv rstGateL from "tests/sorter/attacks/rst_gate.sv"

#guard reprStr (earlyValidL.sem 2 2) == reprStr earlyValidD
#guard reprStr (missingElseL.sem 2 2) == reprStr missingElseD
#guard reprStr (pushOwnValueL.sem 2 2) == reprStr pushOwnValueD
#guard reprStr (signedOrderL.sem 2 2) == reprStr signedOrderD
#guard reprStr (tokenSelfL.sem 2 2) == reprStr tokenSelfD
#guard reprStr (resetKeepsCellsL.sem 3 2) == reprStr resetKeepsCellsD
#guard reprStr (topNotDrainedL.sem 2 2) == reprStr topNotDrainedD
#guard reprStr (rstGateL.sem 2 2) == reprStr rstGateD

/-- **`early_valid` is rejected**: on `2, 3` it emits `0, 2, 3` (out_valid rises one cycle early, with the padding
0 of cell 0). -/
theorem early_valid_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = earlyValidD) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

/-- **`missing_else` is rejected**: on `2, 3` it emits `3, 3` (the input is written over the pushed neighbour). -/
theorem missing_else_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = missingElseD) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

/-- **`push_own_value` is rejected**: on `3, 2` it emits `3, 3` (cell 0 takes the top cell's value, not the input). -/
theorem push_own_value_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = pushOwnValueD) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 3#2 2#2) (s := 1) (by decide +kernel))
    sem lat hd

/-- **`signed_order` is rejected**: on `2, 3` (both negative as signed 2-bit values) it emits `0, 0`: both sort
below the padding 0 and are lost. -/
theorem signed_order_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = signedOrderD) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

/-- **`token_self` is rejected**: on `2, 3` it emits nothing, for ever (the run comes to rest with `out_valid` = 0:
the fixed point of `stream_refuted`). -/
theorem token_self_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = tokenSelfD) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

/-! ## The reference passes the same runs (an executable reading, not a proof) -/

/-- A reset, a start, the values `2, 3` (the sorted output `2, 3`), then idle until the design is at rest. -/
def rowsA : List (Row 2) :=
  [(true, false, false, 0#2), (false, true, false, 0#2), (false, false, true, 2#2), (false, false, true, 3#2)] ++
    List.replicate 6 (idle 2)

#guard (trAt refD (zeros refD) (rowsA.map ent)).length == rowsA.length
#guard obsList 2 (trAt refD (zeros refD) (rowsA.map ent)) 1 (rowsA.length - 1) ==
  [(false, 0#2), (false, 0#2), (false, 0#2), (true, 2#2), (true, 3#2), (false, 0#2), (false, 0#2), (false, 0#2),
   (false, 0#2)]

/-- A reset, a start, the values `0, 0, 0` at `N = 3`, then eight idle rows. -/
def rowsRK : List (Row 2) :=
  [(true, false, false, 0#2), (false, true, false, 0#2), (false, false, true, 0#2), (false, false, true, 0#2),
    (false, false, true, 0#2)] ++ List.replicate 8 (idle 2)

/-- **`reset_keeps_cells` is rejected** at `(3, 2)` (at `N = 2` it is right: the one unreset cell takes the reset
top cell's 0 at the entry after the release, which never carries a value). From the power-up with every cell 3,
the reset entry and the start entry drain cell 1 into cell 0, which keeps 3; the inputs `0, 0, 0` push nothing, and
the first value emitted is 3 (the reference emits `0, 0, 0`). -/
theorem reset_keeps_cells_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat)
    (hd : sem 3 2 = resetKeepsCellsD) : ¬ Statement sem lat :=
  refuted_at (N := 3) (by simp [task]) (stream_refuted_of_check (p := (3, 2)) (powerUp_onesAt _ ["data"])
    (rows := rowsRK) (s := 1) (by decide +kernel)) sem lat hd

#guard (((obsList 2 (trAt (refDN 3) (onesAt (refDN 3) ["data"]) (rowsRK.map ent)) 1 12).filter (·.1)).map (·.2) ==
  [0#2, 0#2, 0#2])

/-- Two transactions: a reset, a start at 1 with `2, 3`, idle until its outputs are shown (snapshots 4, 5), a start
at 6 with `1, 1`, then eight idle rows. -/
def rowsTN : List (Row 2) :=
  [(true, false, false, 0#2), (false, true, false, 0#2), (false, false, true, 2#2), (false, false, true, 3#2),
    idle 2, idle 2, (false, true, false, 0#2), (false, false, true, 1#2), (false, false, true, 1#2)] ++
    List.replicate 8 (idle 2)

/-- **`top_not_drained` is rejected** at the second transaction: the first (`2, 3`) is emitted right, but the top
cell keeps its maximum 3, which no later value beats, and the second (`1, 1`) emits `3, 3` (the reference emits
`1, 1`). -/
theorem top_not_drained_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = topNotDrainedD) :
    ¬ Statement sem lat :=
  refuted_of (stream2_refuted_of_check (p := (2, 2)) (powerUp_zeros _) (rows := rowsTN) (s1 := 1) (s2 := 6)
    (by decide +kernel)) sem lat hd

#guard (((obsList 2 (trAt refD (zeros refD) (rowsTN.map ent)) 6 11).filter (·.1)).map (·.2) == [1#2, 1#2])
#guard (((obsList 2 (trAt topNotDrainedD (zeros topNotDrainedD) (rowsTN.map ent)) 1 5).filter (·.1)).map (·.2))
  == [2#2, 3#2]
#guard (((obsList 2 (trAt topNotDrainedD (zeros topNotDrainedD) (rowsTN.map ent)) 6 11).filter (·.1)).map (·.2))
  == [3#2, 3#2]

/-! ## Rule 1 with nothing exempt (decided 2026-11-09) -/

/-- `rst_gate` fails rule 1: its one combinational dependency, `out_valid` on `ov_q` and `rst`, reaches the output
from the input `rst`, which is no longer exempt. -/
theorem rst_gate_not_moore : ¬ MooreOutDep rstGateD [] := by
  rintro ⟨S, hin, hcl, hout⟩
  exact hout "out_valid" (by decide)
    (hcl ("out_valid", ["out_valid", "ov_q", "rst"]) (by decide) ⟨"rst", by simp, hin "rst" (by decide) (by simp)⟩)

/-- **`rst_gate` is rejected**, for every latency function: every snapshot it shows is the reference's, but in the
cycle of a reset entry its wire shows `out_valid` = 0 where the claimed snapshot before it shows the transaction's
last output, and rule 1 now refuses the path from `rst`. -/
theorem rst_gate_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = rstGateD) :
    ¬ Statement sem lat :=
  refuted_of_sat (fun _ hs => rst_gate_not_moore hs.2.2.2.2.1) sem lat hd

-- the reference has no combinational dependency at all; `rst_gate` has the one from `rst` (executable readings)
#guard (combDeps refD).isEmpty
#guard combDeps rstGateD == [("out_valid", ["out_valid", "ov_q", "rst"]), ("out_data", ["out_data", "od_q"])]

#print axioms stream_refuted
#print axioms stream2_refuted
#print axioms top_not_drained_refuted
#print axioms reset_keeps_cells_refuted
#print axioms early_valid_refuted
#print axioms missing_else_refuted
#print axioms push_own_value_refuted
#print axioms signed_order_refuted
#print axioms token_self_refuted
#print axioms rst_gate_refuted

end SvGolf.Tasks.Sorter.Refute

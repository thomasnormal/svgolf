import tasks.sorter.Spec

/-!
# Task `sorter`: the statement as named properties (proved, not trusted)

`Spec.lean`'s `Statement` is one formula. This file gives each part of it a name, one definition
per thing a design must satisfy, and proves `statement_iff_properties`: the statement holds
exactly when, at every `(N, W)` in range, every property holds. The theorem is checked by Lean's
kernel, so the properties cover the whole statement and nothing else; this file adds nothing to
the trusted base. `properties.json` explains each property in plain words.

The statement's guarantee (`StreamTask.Guar`) is one conjunction under the protocol; here it is
four properties, each under the same protocol (`UnderProtocol`): `OutValidKnown`,
`SilentBeforeFirstStart`, `EmitsSorted` and `SilentAfterLatency`. The last two split the
statement's per-transaction claim (one list of observations that emits the sorted values and is
silent after the latency) in two; they are equivalent to it because the snapshots fix the
`out_valid` bit of every observation.
-/

namespace SvGolf.Tasks.Sorter.Properties

open SvGolf LeanModels.Sv

/-- The parameters the statement covers: `N, W ≥ 1` and `N·W` below `2^31`. -/
def ParamsInRange (N W : Nat) : Prop :=
  1 ≤ N ∧ 1 ≤ W ∧ N * W < 2 ^ 31

/-- Exactly these ports, in this order, with these widths. -/
def Interface (W : Nat) (d : Design2) : Prop :=
  inputPorts d = [("clk", 1), ("rst", 1), ("start", 1), ("in_valid", 1), ("in_data", W)] ∧
    outputPorts d = [("out_valid", 1), ("out_data", W)]

/-- `clk` is an input; every process that runs at a clock edge is clocked by `clk`; an
asynchronous reset can only be `rst`; no process reads `clk` as data. -/
def ClockDiscipline (d : Design2) : Prop :=
  "clk" ∈ d.inputNames.toList ∧
    ∀ p ∈ d.processes.toList,
      (p.isEdgePhase = true → edgeClock p = some "clk") ∧
      (∀ r, asyncReset p = some r → r = "rst") ∧
      "clk" ∉ processDataNames p

/-- Under every schedule and every stimulus, the run completes. -/
def Terminates (d : Design2) : Prop :=
  ∀ (σ : ScheduleOracle) (stim : List SvState), ∃ tr, Runs2 d σ stim tr

/-- The declared latency is at least one cycle. -/
def LatencyAtLeastOne (lat : Nat) : Prop :=
  1 ≤ lat

/-- `G` holds in every completed run, from every release `c1` of the reset, up to every horizon
`h` before which the environment kept the protocol (`StreamTask.Rely`). -/
def UnderProtocol (N W : Nat) (d : Design2)
    (G : List SvState → List SvState → Nat → Nat → Prop) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ c1 h, Released "rst" stim c1 h → task.Rely (N, W) stim tr c1 h → G stim tr c1 h

/-- `out_valid` is a known bit at every cycle from the release. -/
def OutValidKnown (N W : Nat) (d : Design2) : Prop :=
  UnderProtocol N W d fun _ tr c1 h =>
    ∀ c, c1 ≤ c → c < h → ∃ b, TraceBit tr c "out_valid" b

/-- `out_valid` is 0 at every cycle from the release up to the first start. -/
def SilentBeforeFirstStart (N W : Nat) (d : Design2) : Prop :=
  UnderProtocol N W d fun stim tr c1 h =>
    ∀ c, c1 ≤ c → c < h → (∀ s, c1 ≤ s → s ≤ c → ¬ StimBit stim s "start" true) →
      TraceBit tr c "out_valid" false

/-- `Transaction N W stim c1 h s xs e`: `s` is a start after the release `c1`, `xs` are the `N`
values on `in_data` in the cycles after it, and `e` is the next start, or the horizon `h` if
there is none before it. -/
def Transaction (N W : Nat) (stim : List SvState) (c1 h s : Nat) (xs : List (BitVec W))
    (e : Nat) : Prop :=
  c1 ≤ s ∧ StimBit stim s "start" true ∧ xs.length = N ∧
    (∀ j v, xs[j]? = some v → ∃ en, stim[s + 1 + j]? = some en ∧
      SvState.lookup en "in_data" = some (LVec.ofBitVec v)) ∧
    s < e ∧ e ≤ h ∧ (∀ s', s < s' → s' < e → ¬ StimBit stim s' "start" true) ∧
    (e < h → StimBit stim e "start" true)

/-- From each start to the next, the values shown on `out_data` while `out_valid` is 1 are, in
order, the transaction's input values sorted ascending. -/
def EmitsSorted (N W lat : Nat) (d : Design2) : Prop :=
  UnderProtocol N W d fun stim tr c1 h =>
    ∀ s xs e, s + lat < h → Transaction N W stim c1 h s xs e →
      ∃ obs : List (Bool × BitVec W), obs.length = e - s ∧ task.Shows (N, W) tr s obs ∧
        task.emitted (N, W) obs = sortAsc xs

/-- From each start to the next, `out_valid` is 0 at every cycle more than `lat` cycles after
the start. -/
def SilentAfterLatency (N W lat : Nat) (d : Design2) : Prop :=
  UnderProtocol N W d fun stim tr c1 h =>
    ∀ s xs e, s + lat < h → Transaction N W stim c1 h s xs e →
      ∀ c, s + lat < c → c < e → TraceBit tr c "out_valid" false

theorem clockDiscipline_iff (d : Design2) : ClockDiscipline d ↔ task.Disciplined d := by
  constructor
  · rintro ⟨hk, hp⟩
    refine ⟨hk, fun p hmem => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hp p hmem
    exact ⟨h1, fun r hr => by rw [h2 r hr]; rfl, h3⟩
  · rintro ⟨hk, hp⟩
    refine ⟨hk, fun p hmem => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hp p hmem
    exact ⟨h1, fun r hr => (Option.some.inj (h2 r hr)).symm, h3⟩

/-- A snapshot shows one value of a 1-bit signal. -/
private theorem bitIs_unique {st : SvState} {n : String} {a b : Bool} (ha : BitIs st n a)
    (hb : BitIs st n b) : a = b := by
  unfold BitIs at ha hb
  rw [ha] at hb
  cases a <;> cases b <;> first | rfl | exact absurd hb (by decide)

/-- The guarantee is the four properties. -/
theorem follows_iff (N W lat : Nat) (d : Design2) :
    task.Follows (N, W) lat d ↔
      OutValidKnown N W d ∧ SilentBeforeFirstStart N W d ∧ EmitsSorted N W lat d ∧
        SilentAfterLatency N W lat d := by
  constructor
  · intro hF
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro σ stim tr hr c1 h hrel hrely
      exact (hF σ stim tr hr c1 h hrel hrely).1
    · intro σ stim tr hr c1 h hrel hrely
      exact (hF σ stim tr hr c1 h hrel hrely).2.1
    · intro σ stim tr hr c1 h hrel hrely s xs e hlat htx
      obtain ⟨hs, hst, hlen, hdata, hse, heh, hno, hnext⟩ := htx
      obtain ⟨obs, hl, hsh, hem, _⟩ :=
        (hF σ stim tr hr c1 h hrel hrely).2.2 s xs hs hlat hst hlen hdata e hse heh hno hnext
      exact ⟨obs, hl, hsh, hem⟩
    · intro σ stim tr hr c1 h hrel hrely s xs e hlat htx c hc hce
      obtain ⟨hs, hst, hlen, hdata, hse, heh, hno, hnext⟩ := htx
      obtain ⟨obs, hl, hsh, _, hq⟩ :=
        (hF σ stim tr hr c1 h hrel hrely).2.2 s xs hs hlat hst hlen hdata e hse heh hno hnext
      have hk : c - s < obs.length := by omega
      obtain ⟨o, ho⟩ : ∃ o, obs[c - s]? = some o := ⟨_, List.getElem?_eq_getElem hk⟩
      obtain ⟨st, hst', hb, _⟩ := hsh (c - s) o ho
      have hc' : s + (c - s) = c := by omega
      rw [hc'] at hst'
      refine ⟨st, hst', ?_⟩
      rw [hq (c - s) o ho (by omega)] at hb
      exact hb
  · rintro ⟨hK, hS, hE, hQ⟩ σ stim tr hr c1 h hrel hrely
    refine ⟨hK σ stim tr hr c1 h hrel hrely, hS σ stim tr hr c1 h hrel hrely,
      fun s xs hs hlat hst hlen hdata e hse heh hno hnext => ?_⟩
    have htx : Transaction N W stim c1 h s xs e := ⟨hs, hst, hlen, hdata, hse, heh, hno, hnext⟩
    obtain ⟨obs, hl, hsh, hem⟩ := hE σ stim tr hr c1 h hrel hrely s xs e hlat htx
    refine ⟨obs, hl, hsh, hem, fun k o hk hlk => ?_⟩
    obtain ⟨st, hst', hb, _⟩ := hsh k o hk
    have hkl : k < obs.length := by
      obtain ⟨hkl, _⟩ := List.getElem?_eq_some_iff.1 hk
      exact hkl
    obtain ⟨st', hst'', hb'⟩ := hQ σ stim tr hr c1 h hrel hrely s xs e hlat htx (s + k)
      (by omega) (by omega)
    rw [hst'] at hst''
    cases hst''
    exact bitIs_unique hb hb'

/-- **The statement is exactly the properties.** -/
theorem statement_iff_properties (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) :
    Statement sem lat ↔ ∀ N W, ParamsInRange N W →
      Interface W (sem N W) ∧ ClockDiscipline (sem N W) ∧ Terminates (sem N W) ∧
        LatencyAtLeastOne (lat N W) ∧ OutValidKnown N W (sem N W) ∧
        SilentBeforeFirstStart N W (sem N W) ∧ EmitsSorted N W (lat N W) (sem N W) ∧
        SilentAfterLatency N W (lat N W) (sem N W) := by
  constructor
  · intro h N W hp
    obtain ⟨hi, ⟨hd, ht⟩, hl, hf⟩ := h (N, W) hp
    exact ⟨hi, (clockDiscipline_iff _).2 hd, ht, hl, (follows_iff N W _ _).1 hf⟩
  · rintro h ⟨N, W⟩ hp
    obtain ⟨hi, hd, ht, hl, hf⟩ := h N W hp
    exact ⟨hi, ⟨(clockDiscipline_iff _).1 hd, ht⟩, hl, (follows_iff N W _ _).2 hf⟩

end SvGolf.Tasks.Sorter.Properties

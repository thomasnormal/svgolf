import CounterCycle
import ObsComb

/-!
# `SeqTask` over `Obs_run2`: v1's convention (`_stim`), the counter, and read-during-write through the pre sample

Not in any lake library and imported by nothing trusted. Compile with `compile-obs.sh`; it imports the
sequential sketches `../sequential/SeqTask.lean` and `CounterCycle.lean` from the same scratch copy.
The trusted (pre-sample) restatement of `SeqTask` is in `TaskV2.lean`.

**Status labels.**

* `SeqTask.RstDrives_stim`, `Drives_stim`, `Follows_stim`, `SatisfiedAt_stim`: v1's convention
  over `Obs_run2`, **provisional over `run2`** (Day 3's `Follows_obs`, renamed when ruling (a) made
  the pre-sample convention the trusted one).
* `follows_stim_iff`, `satisfiedAt_stim_iff`, `statement_stim_bounded`, `satisfiedAt_stim_of_cycle`,
  `cnt_satisfiedAt_stim`, `cnt_statement_stim`, and the register-file `#guard`s: **provisional over
  `run2`.**
* `ReadsBeforeWrite`: **DRAFT of trusted text**, a property stated over trusted samples only.

## What is here

1. `SeqTask.Follows_stim`: v1's `Follows`, with the snapshot replaced by the trusted post sample.
   `follows_stim_iff` and `satisfiedAt_stim_iff` prove that it is v1 over `Obs_run2`.
2. **The counter over `Obs_run2`**, v1's convention: `cnt_statement_stim` for every `N ≥ 1`. It is the
   sketch's `cnt_satisfiedAt` (proved by `SeqTask.satisfiedAt_of_cycle`) carried over by
   `satisfiedAt_stim_iff`. The counter under the trusted convention is `CounterObs.lean` (Day 5).
3. **Read-during-write through the pre sample** (the Mealy gap of `../sequential/README.md` §1.2): a
   4 × 8 register file with a combinational read port. `ReadsBeforeWrite` is stated on the pre
   samples alone (ruling (a): the write and the read are the inputs the pre samples hold). The
   `#guard`s run it on `Obs_run2`: it holds when `rdata` is read from the pre samples, and fails when
   it is read from the post samples (`run2`'s snapshots). The post sample of a cycle that writes the
   address it reads already shows the new data, so a statement over snapshots alone could not say
   this.
-/

namespace SvGolf.Seq.SeqTask

open LeanModels.Sv LeanModels.Sv.Observe SvGolf SvGolf.Arch

variable (t : SeqTask)

/-- `run2`'s convention: stimulus entry `c` binds the reset port at the level that means `r`. Without a
reset port only `r = false` is available. -/
def RstDrives_stim (stim : List SvState) (c : Nat) (r : Bool) : Prop :=
  match t.rst with
  | none => r = false
  | some (n, lvl) => stimDrive stim c n = some (LVec.ofBitVec (BitVec.ofBool (if r then lvl else !lvl)))

/-- `run2`'s convention: stimulus entry `c` binds the spec-side input `(r, v)`. -/
def Drives_stim (N : Nat) (stim : List SvState) (c : Nat) (p : Bool × t.Ins N) : Prop :=
  t.RstDrives_stim stim c p.1 ∧ DrivesAll (stimDrive stim) c (t.inputs N) p.2

/-- **v1's `Follows` over `Obs_run2`**: if the stimulus covers and binds the cycles `c0, c0 + 1, …`
with the spec-side inputs `ps` (the first one asserting reset), the post samples of those cycles show
the spec machine's observations. -/
def Follows_stim (N : Nat) (d : Design2) : Prop :=
  ∀ σ stim b, Obs_run2.Behaves d σ stim b →
    ∀ (c0 : Nat) (ps : List (Bool × t.Ins N)), t.StartOK N ps →
      (∀ j p, ps[j]? = some p → c0 + j < stim.length ∧ t.Drives_stim N stim (c0 + j) p) →
      ∀ j a, (t.scan N (t.init N) ps)[j]? = some a →
        ∃ o, b[c0 + j]? = some o ∧ t.ObsOKS N o.post a

/-- v1's `SatisfiedAt` over `Obs_run2`, with the clock discipline `Disciplined` (`ClockedBy`) as
`run2`'s admission predicate. -/
def SatisfiedAt_stim (N : Nat) (d : Design2) : Prop :=
  t.InterfaceObs Obs_run2 N d ∧ (t.Disciplined d ∧ Obs_run2.Progress t.clocking d) ∧
    t.Follows_stim N d

/-- The `_stim` statement restricted to the parameter values the declared type can hold. -/
def Statement_stim_bounded (ty : Nat → Prop) (sem : Nat → Design2) : Prop :=
  ∀ N, t.inRange N → ty N → t.SatisfiedAt_stim N (sem N)

end SvGolf.Seq.SeqTask

namespace SvGolf.Arch.Seq

open LeanModels.Sv LeanModels.Sv.Observe SvGolf SvGolf.Seq SvGolf.Arch

/-! ## 1. The `_stim` variant is v1 (provisional over `run2`) -/

/-- A stimulus entry drives a spec-side input exactly when the stimulus covers the cycle and binds
it. -/
theorem drives_iff {t : SvGolf.Seq.SeqTask} {N : Nat} {stim : List SvState} {c : Nat}
    {p : Bool × t.Ins N} :
    (∃ e, stim[c]? = some e ∧ t.Drives N e p) ↔ c < stim.length ∧ t.Drives_stim N stim c p := by
  constructor
  · rintro ⟨e, he, hrst, hall⟩
    refine ⟨(List.getElem?_eq_some_iff.mp he).1, ?_, (drivesAll_stimDrive he _ _).mpr hall⟩
    unfold SeqTask.RstDrives_stim
    unfold SvGolf.Seq.SeqTask.RstDrives at hrst
    split
    · rename_i h; rw [h] at hrst; exact hrst
    · rename_i n lvl h; rw [h] at hrst; simpa [stimDrive, he] using hrst
  · rintro ⟨hlt, hrst, hall⟩
    have he : stim[c]? = some stim[c] := List.getElem?_eq_getElem hlt
    refine ⟨stim[c], he, ?_, (drivesAll_stimDrive he _ _).mp hall⟩
    unfold SeqTask.RstDrives_stim at hrst
    unfold SvGolf.Seq.SeqTask.RstDrives
    split
    · rename_i h; rw [h] at hrst; exact hrst
    · rename_i n lvl h; rw [h] at hrst; simpa [stimDrive, he] using hrst

/-- **`Follows ↔ Follows_stim` over `Obs_run2`**, whenever the task's output names are ports. -/
theorem follows_stim_iff {t : SvGolf.Seq.SeqTask} {N : Nat} {d : Design2}
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (hout : ∀ p ∈ t.outputs N, p.1 ∈ (Obs_run2.iface d).names) :
    t.Follows N d ↔ t.Follows_stim N d := by
  constructor
  · intro h σ stim b hb c0 ps hstart hdrv j a ha
    obtain ⟨r, hr, rfl⟩ := hb
    have hruns := Obs_run2.runs2_of_runs hnq hr
    obtain ⟨st, hst, hok⟩ :=
      h σ stim _ hruns c0 ps hstart (fun j p hp => drives_iff.mpr (hdrv j p hp)) j a ha
    rw [List.getElem?_map] at hst
    cases hrc : r[c0 + j]? with
    | none => rw [hrc] at hst; cases hst
    | some o' =>
        rw [hrc] at hst
        simp only [Option.map_some, Option.some.injEq] at hst
        subst hst
        exact ⟨o'.map (Obs_run2.sample d), by simp [hrc], (holdAllS_sample _ _ hout).mpr hok⟩
  · intro h σ stim tr htr c0 ps hstart hdrv j a ha
    obtain ⟨r, hr, rfl⟩ := Obs_run2.runs_of_runs2 htr
    obtain ⟨o, ho, hok⟩ := h σ stim _ ⟨r, hr, rfl⟩ c0 ps hstart
      (fun j p hp => drives_iff.mp (hdrv j p hp)) j a ha
    obtain ⟨o', hrc, rfl⟩ := obs_run2_cycle ho
    exact ⟨o'.post, by simp [hrc], (holdAllS_sample _ _ hout).mp hok⟩

/-- Under `Interface`, every task output is a port. -/
theorem outputs_mem_of_interface {t : SvGolf.Seq.SeqTask} {N : Nat} {d : Design2}
    (h : t.Interface N d) : ∀ p ∈ t.outputs N, p.1 ∈ (Obs_run2.iface d).names := by
  intro p hp
  have : outputSigs d = t.outputs N := h.2
  exact mem_names_of_outputs (this ▸ hp)

/-- **v1's `SeqTask.SatisfiedAt` is exactly the `_stim` variant over `Obs_run2`**, for a design with
no qualified `case` (`Obs_run2` omits master's qualified-case trace check, `Observe.lean`). -/
theorem satisfiedAt_stim_iff {t : SvGolf.Seq.SeqTask} {N : Nat} {d : Design2}
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false) :
    t.SatisfiedAt N d ↔ t.SatisfiedAt_stim N d := by
  constructor
  · rintro ⟨hI, ⟨hD, hT⟩, hF⟩
    exact ⟨hI, ⟨hD, Obs_run2.progress_of_terminates _ d hT⟩,
      (follows_stim_iff hnq (outputs_mem_of_interface hI)).mp hF⟩
  · rintro ⟨hI, ⟨hD, hP⟩, hF⟩
    exact ⟨hI, ⟨hD, (Obs_run2.progress_iff _ d hnq).mp hP⟩,
      (follows_stim_iff hnq (outputs_mem_of_interface hI)).mpr hF⟩

/-- **v1 implies the bounded statement**, for any declared type's range. -/
theorem statement_stim_bounded {t : SvGolf.Seq.SeqTask} {sem : Nat → Design2} (ty : Nat → Prop)
    (hnq : ∀ N, t.inRange N → (sem N).processes.toList.any Process2.hasQualifiedCase = false)
    (h : t.Statement sem) : t.Statement_stim_bounded ty sem :=
  fun N hr _ => (satisfiedAt_stim_iff (hnq N hr)).mp (h N hr)

/-- **The reduction theorem with its conclusion over `Obs_run2`** (v1's convention):
`SeqTask.satisfiedAt_of_cycle` composed with `satisfiedAt_stim_iff`. -/
theorem satisfiedAt_stim_of_cycle (t : SvGolf.Seq.SeqTask) (N : Nat) (d : Design2)
    (hrst : ∃ r, t.rst = some r)
    (hI : t.Interface N d) (hD : t.Disciplined d) (hT : Terminates2 d)
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (Inv : SvState → Prop) (R : SvState → t.State N → Prop)
    (hinit : Inv (initState2 d))
    (hinv : ∀ σ F inputs prev k st k', Inv prev →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → Inv st)
    (hreset : ∀ σ F inputs prev k st k' (v : t.Ins N), Inv prev →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → t.Drives N inputs (true, v) →
        R st (t.init N) ∧ t.ObsOK N st (t.init N, v))
    (hstep : ∀ σ F inputs prev k st k' (s : t.State N) (v : t.Ins N), Inv prev → R prev s →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → t.Drives N inputs (false, v) →
        R st (t.step N s v) ∧ t.ObsOK N st (t.step N s v, v)) :
    t.SatisfiedAt_stim N d :=
  (satisfiedAt_stim_iff hnq).mp
    (SvGolf.Seq.SeqTask.satisfiedAt_of_cycle t N d hrst hI hD hT Inv R hinit hinv hreset hstep)

/-! ## 2. The counter over `Obs_run2`, v1's convention (provisional over `run2`) -/

open SvGolf.Seq.Counter in
/-- **The counter task over `Obs_run2`** (v1's convention), at every `N ≥ 1`: for every schedule,
every stimulus and every completed behaviour, from every reset, the post samples of `q` are the spec
counter. For the hand-built family `cntD` of `../sequential/CounterCycle.lean`, whose agreement with
`cnt.sem N` is checked there by `#guard` at seven points. -/
theorem cnt_satisfiedAt_stim (N : Nat) : cntTask.SatisfiedAt_stim N (cntD N) :=
  (satisfiedAt_stim_iff rfl).mp (cnt_satisfiedAt N)

open SvGolf.Seq.Counter in
theorem cnt_statement_stim :
    ∀ N, cntTask.inRange N → cntTask.SatisfiedAt_stim N (cntD N) :=
  fun N _ => cnt_satisfiedAt_stim N

/-! ## 3. Read-during-write through the pre sample (provisional over `run2`)

`logic [7:0] mem [0:3]` as one 32-bit vector with 8-bit element selects (the shape the loader
produces for an unpacked memory), a write port written by NBA at the clock edge, and a
combinational read port `assign rdata = mem[raddr]` (a Mealy output: it reads an input). -/

/-- The register file. -/
def rfD : Design2 where
  name := "rf"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "we", width := 1, isInput := true },
             { name := "waddr", width := 2, isInput := true },
             { name := "wdata", width := 8, isInput := true },
             { name := "raddr", width := 2, isInput := true },
             { name := "rdata", width := 8, isOutput := true },
             { name := "mem", width := 32 }]
  processes := #[
    .alwaysFF "clk"
      (.ifStmt (.ident "we") (.nbaAssign (.index "mem" (.ident "waddr") 8) (.ident "wdata")) none),
    .assign (.ident "rdata") (.index (.ident "mem") (.ident "raddr") 8)]

/-- **Read-during-write, stated over trusted observations, on the pre samples alone.** Whenever the
pre sample of cycle `c` holds a write of `w` at address `a` (`we = 1`) and the pre sample of cycle
`c + 1` holds the read address `a`, the read port in the pre sample of cycle `c + 1` shows `w`. This is
the value a synchronous consumer samples at edge `c + 1`, before cycle `c + 1`'s own write lands, even
when cycle `c + 1` writes `a` too. -/
def ReadsBeforeWrite (b : List (CycleObs PortSample)) : Prop :=
  ∀ (c : Nat) (a : BitVec 2) (w : BitVec 8) (o o' : CycleObs PortSample),
    b[c]? = some o → b[c + 1]? = some o' →
    o.pre.read "we" = some (LVec.ofBitVec (1#1)) →
    o.pre.read "waddr" = some (LVec.ofBitVec a) →
    o.pre.read "wdata" = some (LVec.ofBitVec w) →
    o'.pre.read "raddr" = some (LVec.ofBitVec a) →
    o'.pre.read "rdata" = some (LVec.ofBitVec w)

/-- The executable check behind the `#guard`s: `ReadsBeforeWrite` on a finite run, with the write
and the read address taken from the pre samples and `rdata` read from the sample `sel` picks. -/
def readsBeforeWriteB (sel : CycleObs PortSample → PortSample)
    (b : List (CycleObs PortSample)) : Bool :=
  (List.range b.length).all fun c =>
    match b[c]?, b[c + 1]? with
    | some o, some o' =>
        match o.pre.read "we", o.pre.read "waddr", o.pre.read "wdata", o'.pre.read "raddr" with
        | some we, some wa, some wd, some ra =>
            !(we == LVec.ofBitVec (1#1) && wa == ra) || (sel o').read "rdata" == some wd
        | _, _, _, _ => true
    | _, _ => true

/-- Four cycles: write `A5` at 1 and read 1; write `3C` at 1 and read 1 (the read-during-write
cycle); hold; write `FF` at 2 and read 1. -/
def rfStim : List SvState :=
  let e (we wa wd ra : Nat) : SvState :=
    [("we", LVec.ofNat 1 we), ("waddr", LVec.ofNat 2 wa), ("wdata", LVec.ofNat 8 wd),
     ("raddr", LVec.ofNat 2 ra)]
  [e 1 1 0xA5 1, e 1 1 0x3C 1, e 0 1 0x00 1, e 1 2 0xFF 1]

/-- The trusted behaviour of `rfD` under `rfStim` (σ_src; one comb process and one edge process,
so σ does not matter). -/
def rfRun : Option (List (CycleObs PortSample)) :=
  (runObs2 rfD σ_src 64 rfStim).toOption.map (·.map (CycleObs.map (Obs_run2.sample rfD)))

-- The `rdata` port per cycle, (pre, post). Cycle 1 is the read-during-write cycle: its pre sample
-- shows the OLD word `A5` (what the consumer samples at the edge), its post sample the NEW `3C`.
#guard rfRun.map (·.map fun o => ((o.pre.read "rdata").map LVec.toBinString,
    (o.post.read "rdata").map LVec.toBinString)) ==
  some [(some "xxxxxxxx", some "10100101"),
        (some "10100101", some "00111100"),
        (some "00111100", some "00111100"),
        (some "00111100", some "00111100")]

-- `ReadsBeforeWrite` holds on the pre samples of this run ...
#guard rfRun.map (readsBeforeWriteB CycleObs.pre) == some true
-- ... and the same property read on the post samples (run2's snapshots) fails at cycle 1.
#guard rfRun.map (readsBeforeWriteB CycleObs.post) == some false

-- Trusted samples hold the ports only: the internal `mem` reads `none`, the proof observation reads it.
#guard rfRun.map (·.map fun o => o.post.read "mem") == some [none, none, none, none]
#guard (runObs2 rfD σ_src 64 rfStim).toOption.map (·.map fun o => (SvState.lookup o.post "mem").isSome)
  == some [true, true, true, true]

#print axioms drives_iff
#print axioms follows_stim_iff
#print axioms outputs_mem_of_interface
#print axioms satisfiedAt_stim_iff
#print axioms statement_stim_bounded
#print axioms satisfiedAt_stim_of_cycle
#print axioms cnt_satisfiedAt_stim
#print axioms cnt_statement_stim

end SvGolf.Arch.Seq

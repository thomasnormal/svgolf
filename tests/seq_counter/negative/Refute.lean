import SvGolf.SeqV2
import tests.seq_counter.Spec

/-!
# The counter fixture: the soundness probe's twins do NOT satisfy txtask-v2 (revision 2)

Kernel-checked refutations of the two designs the soundness probe (`design/soundness/TXTASK-V2-REVIEW.md`)
found ACCEPTED end to end under txtask-v1, against the v2
statement of the counter (`tests/seq_counter/Spec.lean`, `SeqTask.StatementV2`), at `N = 1`:

* **H1, x-optimism** (`h1x`: `h1_xopt.sv`; `h1r`: `h1_rare.sv`, the twin v1's checker accepted
  with a wrong scored netlist). `u <= u` is never reset. Under v1 the run starts at ls-sv's x start,
  `u` is `x`, and `if (!u)` takes the else branch: the counter. Rule 2 (every power-up) runs it from
  the power-up state with `u = 0` too, where `if (!u)` is taken: `h1x` holds `q` at 0, `h1r`
  saturates. Rule 1 does not see H1 (both twins are FF-only), and rule 3 does not either (no
  x-creating construct: the `x` came from the start state, which rule 2 replaces).
* **F1, the Mealy phantom** (`f1m`: `f1_mealy.sv`, accepted by v1's checker). The assign that
  drives the output `q` reads the input `en`: rule 1 (`MooreOutDep`) fails. `f1m_wire` shows the
  phantom on one run: snapshot 1 shows `q = 1`, the wire during the next period `q = 0`.

The twins are hand-built `Design2`s, as in the probe: the probe's fixtures are not on this
branch. MEASURED (review session, 2026-11-05, `load_sv` of the probe's three `.sv` files through
this branch's extractor, `(task := "tests/seq_counter")`): `reprStr (design.sem N)` equals
`reprStr` of the twin at `N = 1` and at `N = 8`, for all three. `cntRef` is `cnt.lean`'s `cntD`
verbatim, which `cnt.lean` proves equal to the loaded counter for every `N ≥ 1` (`cnt_sem_eq`).

`cnt_not_followsPU` is the refutation shape the maintainers' acceptance table
(`tests/seq_counter/negative/Table.lean`) uses too: one power-up state, one known stimulus whose
first entry is a reset, and one snapshot whose `q` is not the counter's. The proof of the v2
statement for the loaded counter is `tests/seq_counter/reference/cnt.lean`.
-/

namespace SvGolf.Tests.SeqCounter.Negative

open LeanModels.Sv SvGolf

abbrev cntTask : SeqTask := SvGolf.Tests.SeqCounter.task

/-! ## The designs, hand-built at width `N` -/

/-- The reference counter (`tests/seq_counter/reference/cnt.sv`), as `cnt.lean`'s `cntD`. -/
def cntRef (N : Nat) : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := N, isOutput := true }]
  processes := #[.alwaysFF "clk"
    (.ifStmt (.ident "rst")
      (.nbaAssign (.ident "q") (.lit (LVec.replicate N .l0)))
      (some (.ifStmt (.ident "en")
        (.nbaAssign (.ident "q")
          (.binary .add (.ident "q") (.resize N (.lit ⟨#[.l1]⟩))))
        none)))]

/-- The H1 twin `h1_xopt.sv`: the counter plus `u <= u` (never reset) and an `else if (!u) q <= '0`
arm, which ls-sv never takes and Yosys keeps. -/
def h1x (N : Nat) : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := N, isOutput := true },
             { name := "u", width := 1 }]
  processes := #[.alwaysFF "clk" (.block #[
    .nbaAssign (.ident "u") (.ident "u"),
    .ifStmt (.ident "rst") (.nbaAssign (.ident "q") (.lit (LVec.replicate N .l0)))
      (some (.ifStmt (.unary .lnot (.ident "u"))
        (.nbaAssign (.ident "q") (.lit (LVec.replicate N .l0)))
        (some (.ifStmt (.ident "en")
          (.nbaAssign (.ident "q") (.binary .add (.ident "q") (.resize N (.lit ⟨#[.l1]⟩))))
          none))))])]

/-- The H1 twin `h1_rare.sv` (ACCEPTED end to end by v1's checker): the dead arm is a counter that
saturates at all-ones, so the netlist differs from q = 2^N - 1 on. -/
def h1r (N : Nat) : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := N, isOutput := true },
             { name := "u", width := 1 }]
  processes := #[.alwaysFF "clk" (.block #[
    .nbaAssign (.ident "u") (.ident "u"),
    .ifStmt (.ident "rst") (.nbaAssign (.ident "q") (.lit (LVec.replicate N .l0)))
      (some (.ifStmt (.unary .lnot (.ident "u"))
        (.block #[.ifStmt (.reduce .and (.ident "q")) (.nbaAssign (.ident "q") (.ident "q"))
          (some (.ifStmt (.ident "en")
            (.nbaAssign (.ident "q") (.binary .add (.ident "q") (.resize N (.lit ⟨#[.l1]⟩))))
            none))])
        (some (.ifStmt (.ident "en")
          (.nbaAssign (.ident "q") (.binary .add (.ident "q") (.resize N (.lit ⟨#[.l1]⟩))))
          none))))])]

/-- The F1 twin's output assign: `assign q = (en == en_q) ? q_r : ~q_r`. -/
def f1Assign : Process2 :=
  .assign (.ident "q")
    (.ternary (.binary .eq (.ident "en") (.ident "en_q")) (.ident "q_r")
      (.unary .bnot (.ident "q_r")))

/-- The F1 twin `f1_mealy.sv` (ACCEPTED end to end by v1's checker): the counter in `q_r`,
`en_q <= en`, and `assign q = (en == en_q) ? q_r : ~q_r`. -/
def f1m (N : Nat) : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := N, isOutput := true },
             { name := "q_r", width := N },
             { name := "en_q", width := 1 }]
  processes := #[.alwaysFF "clk" (.block #[
      .nbaAssign (.ident "en_q") (.ident "en"),
      .ifStmt (.ident "rst") (.nbaAssign (.ident "q_r") (.lit (LVec.replicate N .l0)))
        (some (.ifStmt (.ident "en")
          (.nbaAssign (.ident "q_r") (.binary .add (.ident "q_r") (.resize N (.lit ⟨#[.l1]⟩))))
          none))]),
    f1Assign]

/-! ## Runs from a power-up state -/

/-- One stimulus entry of the counter (the clock is not driven: it is not observed). -/
def entry (r e : Nat) : SvState := [("rst", LVec.ofNat 1 r), ("en", LVec.ofNat 1 e)]

/-- The power-up state of `d` with every bit 0. -/
def zeros (d : Design2) : SvState := d.decls.toList.map fun dc => (dc.name, LVec.ofNat dc.width 0)

/-- The power-up state of `d` with the signal `n` set to `v` and every other bit 0. -/
def pu (d : Design2) (n : String) (v : Nat) : SvState :=
  d.decls.toList.map fun dc => (dc.name, LVec.ofNat dc.width (if dc.name = n then v else 0))

/-- The trace of `d` from `st0` on `stim` (source schedule, fuel 64; `[]` if the run does not
complete). -/
def trAt (d : Design2) (st0 : SvState) (stim : List SvState) : List SvState :=
  ((run2At d σ_src 64 st0 stim).toOption).getD []

/-- The trace of `d` from ls-sv's own start state (txtask-v1's run). -/
def trOf (d : Design2) (stim : List SvState) : List SvState := trAt d (initState2 d) stim

/-- `q` in snapshot `j`. -/
def qAt (tr : List SvState) (j : Nat) : Option LVec := (tr[j]?).bind fun st => SvState.lookup st "q"

/-- **The counter's claim fails on one run from a power-up state**: a known stimulus driving the
spec inputs `ps` (a reset first) from entry 0, and a snapshot `j` whose `q` is not the spec's.
Then the design does not satisfy rule 2's claim (`FollowsPU`). -/
theorem cnt_not_followsPU {N : Nat} {d : Design2} {st0 : SvState} {stim : List SvState}
    (hpu : PowerUp d st0) (hk : KnownStim d stim)
    (hrun : run2At d σ_src 64 st0 stim = .ok (trAt d st0 stim))
    {ps : List (Bool × cntTask.Ins N)} (hstart : cntTask.StartOK N ps)
    (hdrv : ∀ j p, ps[j]? = some p → ∃ e, stim[0 + j]? = some e ∧ cntTask.Drives N e p)
    {j : Nat} {a : cntTask.State N × cntTask.Ins N}
    (ha : (cntTask.scan N (cntTask.init N) ps)[j]? = some a)
    (hbad : qAt (trAt d st0 stim) j ≠ some (LVec.ofBitVec a.1)) : ¬ cntTask.FollowsPU N d := by
  intro h
  obtain ⟨st, hst, hobs⟩ := h st0 hpu σ_src stim _ hk ⟨64, hrun⟩ 0 ps hstart hdrv j a ha
  apply hbad
  rw [Nat.zero_add] at hst
  simp only [qAt, hst, Option.bind_some]
  exact hobs.1

/-- The spec inputs of a stimulus of `entry`s: the reset bit and `en` (the counter's inputs do not
depend on `N`). -/
def psOf {N : Nat} (es : List (Nat × Nat)) : List (Bool × cntTask.Ins N) :=
  es.map fun (r, e) => (r == 1, (BitVec.ofNat 1 e, ()))

/-- A stimulus of `entry`s drives the spec inputs `psOf` of its pairs. -/
theorem drives_entries {N : Nat} : ∀ (es : List (Nat × Nat)), (∀ x ∈ es, x.1 < 2 ∧ x.2 < 2) →
    ∀ j p, (psOf (N := N) es)[j]? = some p →
      ∃ e, (es.map fun x => entry x.1 x.2)[0 + j]? = some e ∧ cntTask.Drives N e p
  | [], _, j, p, h => by simp [psOf] at h
  | (r, e) :: es, hb, j, p, h => by
      cases j with
      | zero =>
          simp only [psOf, List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          have hr := (hb (r, e) List.mem_cons_self).1
          have he := (hb (r, e) List.mem_cons_self).2
          refine ⟨entry r e, by simp, ?_⟩
          rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;>
            rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;>
            simp [SeqTask.Drives, SeqTask.RstDrives, HoldAll, entry, SvState.lookup, cntTask,
              SvGolf.Tests.SeqCounter.task] <;>
            first | decide +kernel | rfl
      | succ j =>
          have := drives_entries es (fun x hx => hb x (List.mem_cons_of_mem _ hx)) j p
            (by simpa [psOf] using h)
          simpa [Nat.zero_add] using this

/-! ## H1: refuted by rule 2 (every power-up) -/

/-- `reset; en` from the power-up state `u = 0`. -/
def stimH : List (Nat × Nat) := [(1, 0), (0, 1)]

/-- **`h1_xopt` fails v2**: from the power-up state with `u = 0`, `if (!u) q <= '0` holds `q` at 0,
so snapshot 1 shows `q = 0` where the counter is at 1. -/
theorem h1x_refuted : ¬ cntTask.StatementV2 h1x := fun hs =>
  cnt_not_followsPU (d := h1x 1) (st0 := zeros (h1x 1)) (stim := stimH.map fun x => entry x.1 x.2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (ps := psOf stimH) rfl
    (drives_entries stimH (by decide)) (j := 1) (a := (1#1, (1#1, ()))) rfl (by decide +kernel)
    (hs 1 (Nat.le_refl 1)).2.2.1

/-- `reset; en; en` from the power-up state `u = 0`. -/
def stimH3 : List (Nat × Nat) := [(1, 0), (0, 1), (0, 1)]

/-- **`h1_rare` fails v2** (the twin v1's checker ACCEPTED): from the power-up state with `u = 0`
the counter saturates at all-ones, so snapshot 2 shows `q = 1` where the counter wrapped to 0. -/
theorem h1r_refuted : ¬ cntTask.StatementV2 h1r := fun hs =>
  cnt_not_followsPU (d := h1r 1) (st0 := zeros (h1r 1)) (stim := stimH3.map fun x => entry x.1 x.2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (ps := psOf stimH3) rfl
    (drives_entries stimH3 (by decide)) (j := 2) (a := (0#1, (1#1, ()))) rfl (by decide +kernel)
    (hs 1 (Nat.le_refl 1)).2.2.1

/-- Rule 1 does not see H1: both twins are Moore (FF-only). -/
theorem h1x_moore (N : Nat) : MooreOutDep (h1x N) [] :=
  MooreOutDep.of_noComb rfl (by simp [h1x, Design2.outputNames, Design2.inputNames])

theorem h1r_moore (N : Nat) : MooreOutDep (h1r N) [] :=
  MooreOutDep.of_noComb rfl (by simp [h1r, Design2.outputNames, Design2.inputNames])

/-- Rule 3 does not see H1 either: no construct of the twins creates an `x` from known operands
(the `x` of v1's run is the start state's, which rule 2 replaces by every power-up). -/
theorem h1x_xsafe : XSafe (h1x 1) := by decide +kernel
theorem h1r_xsafe : XSafe (h1r 1) := by decide +kernel

/-- And under txtask-v1's run (ls-sv's x start, `u = x`) both twins ARE the counter on these runs:
`if (!x)` takes the else branch. -/
example : qAt (trOf (h1x 1) (stimH.map fun x => entry x.1 x.2)) 1 = some (LVec.ofNat 1 1) := by
  decide +kernel
example : qAt (trOf (h1r 1) (stimH3.map fun x => entry x.1 x.2)) 2 = some (LVec.ofNat 1 0) := by
  decide +kernel

/-! ## F1: refuted by rule 1 -/

/-- The F1 twin's one combinational dependency: `q` on `q` (the target), `en`, `en_q`, `q_r`. -/
theorem f1m_combDeps (N : Nat) :
    combDeps (f1m N) = [("q", ["q", "en", "en_q", "q_r", "q_r"])] := rfl

/-- **`f1_mealy` fails rule 1**: the assign that drives the output `q` reads the input `en`. -/
theorem f1m_not_moore (N : Nat) : ¬ MooreOutDep (f1m N) [] := by
  rintro ⟨S, hin, hcl, hout⟩
  have hen : S "en" := hin "en" (by simp [f1m, Design2.inputNames]) (by simp)
  have hq : S "q" := hcl ("q", ["q", "en", "en_q", "q_r", "q_r"]) (by rw [f1m_combDeps]; simp)
    ⟨"en", by simp, hen⟩
  exact hout "q" (by simp [f1m, Design2.outputNames]) hq

/-- **`f1_mealy` fails v2.** -/
theorem f1m_refuted : ¬ cntTask.StatementV2 f1m := fun hs =>
  f1m_not_moore 1 (hs 1 (Nat.le_refl 1)).2.2.2.1

/-- **Why F1 must be rejected**: on `reset; en = 1; en = 0` at `N = 1`, snapshot 1 shows `q = 1`
(the counter), but during the period after edge 1 the environment drives entry 2 (`en = 0`), and
the settled value on the wire is `q = 0`. -/
def stimF : List SvState := [entry 1 0, entry 0 1, entry 0 0]

/-- The outputs on the wire during the period after edge `c`: entry `c + 1` applied to snapshot
`c`, settled (source schedule, fuel 64). -/
def wireSample (d : Design2) (stim tr : List SvState) (c : Nat) : Option SvState :=
  match tr[c]?, stim[c + 1]? with
  | some st, some e => ((combSettle2 d σ_src 64 (applyInputs2 d e st) 0).toOption).map Prod.fst
  | _, _ => none

theorem f1m_wire :
    ((trOf (f1m 1) stimF)[1]?).bind (fun st => SvState.lookup st "q") = some (LVec.ofNat 1 1) ∧
    ((wireSample (f1m 1) stimF (trOf (f1m 1) stimF) 1).bind fun st =>
      SvState.lookup st "q") = some (LVec.ofNat 1 0) := by
  decide +kernel

/-! ## The reference counter: evidence for the rules (the proof is `reference/cnt.lean`) -/

-- rule 1: no combinational dependency at all; the checker agrees
example : combDeps (cntRef 8) = [] := rfl
#guard mooreOutDepB (cntRef 8) []
-- rule 1 rejects the F1 twin, and passes the H1 twins
#guard !mooreOutDepB (f1m 8) []
#guard mooreOutDepB (h1x 8) [] && mooreOutDepB (h1r 8) []
-- rule 3: the counter, the H1 twins and the F1 twin have no x-creating construct
#guard xsafeB (cntRef 8) && xsafeB (h1x 8) && xsafeB (h1r 8) && xsafeB (f1m 8)

#print axioms cnt_not_followsPU
#print axioms h1x_refuted
#print axioms h1r_refuted
#print axioms f1m_refuted
#print axioms f1m_wire

end SvGolf.Tests.SeqCounter.Negative

import SvGolf.TaskSeq

/-!
# svGolf reactive task statements: the kind `ReactTask` (TRUSTED text, 2026-11-05; txtask-v2's rules, 2026-11-06)

**Status: final trusted text (decided 2026-11-07).** The reactive kind was decided on
2026-11-05 with the study's defaults (`design/reactive/README.md`): Moore observation, safety plus
BOUNDED response, no environment assumption beyond reset and known inputs. It is a module of its
own beside `SvGolf/TaskSeq.lean`, so that it changes nothing the frozen kinds (`SeqTask`,
`TxTask`, `StreamTask`) and their tasks depend on. Its first task is `tasks/arbiter/Spec.lean`.
On 2026-11-06 it took txtask-v2's rules (`SvGolf/TaskSeq.lean`, its last section; the review
`design/soundness/TXTASK-V2-REVIEW.md`): its claims hold of every run from EVERY power-up state
(rule 2, `ModelsPU`, `TerminatesPU`), and no construct of the design can create an `x` (rule 3,
`XSafe`). They are txtask-v2's definitions, not copies.

The existing kinds say WHAT is computed: a function (`CombTask`), or a function delivered after a
start within a latency (`TxTask`, `StreamTask`). A reactive controller has no transaction: it runs
for ever and must keep a temporal property over the whole input trace.

## What a reactive task fixes

* the ports: the clock `clk`, a synchronous active-high reset `rst`, the data inputs, the outputs;
* `atReset`: what the snapshot of a reset entry must show;
* a SAFETY monitor: spec-side ghost state (`Ghost`, `ginit`, `gnext`, computed from the observed
  history) and a per-cycle predicate `safe` on the ghost state, the cycle's inputs and the
  cycle's outputs;
* RESPONSE obligations (`Obl`, `trig`, `resp`), answered within one bound `K`, an argument of
  `ReactTask.Statement`: a task fixes it in its own `Statement` abbreviation (the arbiter:
  `N - 1`) or exposes it to the golfer, like `TxTask`'s latency.

The semantics is ls-sv's E, unchanged: one stimulus entry is one clock period; the snapshot is the
state after the edge and the settle, with the entry still applied. The runs are ls-sv's
(`cycleStep2`) from a CONCRETE start (`run2At`, `RunsAt`): an `x` is an unknown 0/1 value, so the
standard's `x` start is read as every power-up state, and a proof holds for each of them.

## The statement, conjunct by conjunct (`ReactTask.SatisfiedAt p K d`)

1. **`Interface`**: the input ports are exactly `clk`, `rst`, then the data inputs; the output
   ports exactly the outputs (names, order, widths); and no two declarations share a name.
2. **`Disciplined` and `TerminatesPU`**: `ClockedBy clk none` (one clock, no asynchronous process,
   the clock not read as data), the kind's output discipline `OutDiscipline` (`MooreOut`: no
   combinational path from an input port to an output port), and termination of every run from
   every power-up state, under every schedule, on every known stimulus.
3. **`Follows`** (rule 2): from EVERY power-up state (`PowerUp`: every declared signal, 2-state ones
   included, holds some 0/1 value of its declared width, one value per signal for all its reads),
   under every schedule, on every known stimulus (`KnownStim`: every input an entry binds is a 0/1
   value of its width), in every completed run, at every RESET RELEASE `c1` (the entry `c1 - 1`
   asserts `rst`, the entries `c1, c1 + 1, …` deassert it) and for every list `x0 :: xs` of data
   inputs that the entries `c1 - 1, c1, c1 + 1, …` drive, the snapshots `c1 - 1, c1, …` show known
   outputs `y0, ys[0], ys[1], …` with `atReset y0`, safety on every cycle (`Safe`) and bounded
   response (`Responds`): an obligation triggered at `K + 1` consecutive entries is answered in one
   of those `K + 1` snapshots.
4. **`XSafe`** (rule 3): no construct that can create an `x` or `z` from known operands (the list
   at `xsWidth`, `SvGolf/TaskSeq.lean`).

## Why it cannot be satisfied vacuously or gamed (in addition to `SeqTask`'s and `TxTask`'s lists)

* **No assumption reads the design.** The hypotheses are about the STIMULUS and the start only (a
  power-up, known inputs, a release, `rst` = 0 afterwards), so for every input list there is a
  stimulus meeting them, and by `TerminatesPU` a completed run from every power-up whose snapshots
  must meet the guarantee. A design cannot make the hypothesis false (the "coach injures his own
  player" trap of assume-guarantee specs), and no guarantee is voided by an environment
  "violation": there is no environment obligation. The distinct names of `Interface` are what make
  a known entry of the ports exist: `KnownEntry` reads an input's width from the FIRST declaration
  of its name, so a second declaration of a port's name, earlier and of another width, would leave
  no known entry that drives the port, and the claims would hold vacuously (SystemVerilog forbids
  the redeclaration; the loader refuses it in a flattened hierarchy).
* **Every prefix is a claim.** The list `xs` has any length, so a later input cannot void an
  earlier claim.
* **Bounded, not eventual, response.** `Responds` is falsified by a finite trace, so ls-sv's finite
  runs can refute it; a design that defers an answer for ever, or by more than `K`, fails.
* **Mealy outputs (`OutDiscipline`).** The snapshot is taken after the edge with the cycle's
  inputs still applied, so an output computed combinationally from an input shows `f(registers
  after the edge, OLD inputs)`, a value no wire carries in silicon. A design can exploit it:
  register `last <= x` and drive `out = (x == last) ? good : bad`; in every snapshot `x == last`.
  `MooreOut` rejects every output inside the combinational cone of the inputs. This is the kind's
  own form of txtask-v2's rule 1 (`MooreOutDep`), which is not added: `MooreOut` already forbids
  every combinational path from an input port, the reset included, to an output port, per
  process (so more conservatively than `MooreOutDep`, which follows each assignment's own reads).
  The kind does not permit a combinational grant by design: the decided observation is Moore.
* **Unknown and unreset values (rules 2 and 3).** ls-sv computes with `x` as an IEEE 1800 simulator
  does, and its `x` start makes an unreset register `x`, a 2-state one `0`; Yosys reads an unreset
  register as whatever it powers up to. The claims are therefore about every power-up state, the
  first reset edge included (it reads the power-up values), and rule 3 keeps every value of such a
  run known (`SvGolf/XFree.lean`, `xfree_runsAt`: no decision reads an `x`, no 2-state conversion
  turns an `x` into `0`). So a correct arbiter behind `if (!u)` on a never-reset `u` fails from the
  power-up `u = 0`, a never-reset 2-state ring `u` that turns the arbiter into fixed priority when
  `&u` fails from `u` all ones, and a flag set at the first reset edge from the pre-reset `&u` fails
  from `u` all ones (`tests/arbiter/negative/`). v1's known-state clause (`KnownAt`: every signal but
  the clock known in the claimed snapshots) is gone: under rules 2 and 3 every value of every run
  is known (`ReactTask.snapshots_known`, `SvGolf/React.lean`), so it would restate rule 3.
* **Never-loaded registers (a PIPELINE precondition, not this text).** The pinned Yosys removes a
  flop whose next value is always its own and resolves each read of the undefined value
  separately, which no single power-up value gives; the `score` stage refuses such a design in
  every clocked kind (`check.py` `never_loaded`, decided 2026-11-06). An undriven net is the
  combinational analogue; the `fourstate` stage's undriven check refuses it.
* **Asynchronous reset, `negedge`, `iff` (a PIPELINE precondition, not this text).** `ClockedBy clk
  none` forbids the one asynchronous shape `Design2` expresses (`alwaysFFR`). The loader drops the
  extractor's `areset`, `edge: neg` and `iff` fields, so each of those becomes a plain `alwaysFF
  clk`, a different circuit; the source gate's clocked rules refuse all three, so the checker
  kind `react-family` is a CLOCKED kind (`check.py` `CLOCKED_KINDS`).
* **Never-reset outputs.** `ShowsAt` needs the reset snapshot's outputs to meet `atReset` from every
  power-up state.

## What it does NOT pin, on purpose

* anything while `rst` = 1 except the reset snapshot, and anything before the first reset;
* the state encoding, and any behaviour the task's `safe`/`trig`/`resp` leave free;
* glitch-freedom inside a period: an output decoded from registers settles after the edge, and
  synchronous consumers sample it at the next edge.

## The output discipline, a named slot

The output discipline is ONE definition, `ReactTask.OutDiscipline`, used once in the statement:
this kind's own `MooreOut` (Moore by process: sound, conservative). Switching to the shared
`MooreOutDep` (Moore by signal dependency) would change that body only.

Known restrictions (a design right in silicon that fails the text): `MooreOut` is per process (an
`always_comb` that reads an input puts ALL its targets in the input cone; split the block); it
rejects a reset-gated output `assign o = q & ~{W{rst}}` (`rst` is an input); Moore only (a Mealy
output needs one output register); a one-cycle synchronous reset; rule 3's structural limits
(`SvGolf/TaskSeq.lean`: a run-time divisor, an index whose width can leave its range).

Read with `SvGolf/TaskSeq.lean` (`ClockedBy`, `Released`, `processDataNames`, `lhsTargets`, and
the txtask-v2 section: `PowerUp`, `KnownStim`, `ModelsPU`, `TerminatesPU`, `XSafe`; the final
part of that file, which its Status lists), `SvGolf/Task.lean` (ports,
`Vals`, `HoldAll`) and the ls-sv semantics (`LeanModels/Sv/Sem2.lean`).
-/

namespace SvGolf

open LeanModels.Sv

/-! ## Names a process writes (for `MooreOut`; an assignment target's are `lhsTargets`,
`SvGolf/TaskSeq.lean`) -/

mutual
/-- The signals a statement writes: every blocking or nonblocking target, in every branch. -/
def stmtTargets : Stmt2 → List String
  | .blockingAssign t _ | .nbaAssign t _ => lhsTargets t
  | .ifStmt _ t e => stmtTargets t ++ stmtOptTargets e
  | .block body => stmtListTargets body.toList
  | .caseStmt _ items dflt _ _ => itemListTargets items.toList ++ stmtOptTargets dflt
  | .unsupported _ _ => []
termination_by structural s => s

/-- `stmtTargets` of an optional statement. -/
def stmtOptTargets : Option Stmt2 → List String
  | none => []
  | some s => stmtTargets s
termination_by structural o => o

/-- `stmtTargets` of a list of statements, concatenated. -/
def stmtListTargets : List Stmt2 → List String
  | [] => []
  | s :: ss => stmtTargets s ++ stmtListTargets ss
termination_by structural ss => ss

/-- The signals a case item's body writes. -/
def itemTargets : CaseItem2 → List String
  | .mk _ body => stmtTargets body
termination_by structural it => it

/-- `itemTargets` of a list of case items, concatenated. -/
def itemListTargets : List CaseItem2 → List String
  | [] => []
  | it :: its => itemTargets it ++ itemListTargets its
termination_by structural its => its
end

/-- The signals a process writes. -/
def processTargets : Process2 → List String
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ | .alwaysComb b => stmtTargets b
  | .assign t _ => lhsTargets t
  | .unsupported _ _ => []

/-- **Moore outputs: no combinational path from an input port to an output port.** There is a
set `S` of signal names that contains every input port, is closed under the comb-phase processes
(a continuous assign or `always_comb` block that mentions a signal of `S` writes only signals of
`S`), and contains no output port. The least such set is the combinational cone of the inputs, so
an output outside it changes only at the clock edge: its value in the snapshot after an edge is its
value for the whole following clock period, whatever the inputs do. Conservative on purpose: a
comb process that mentions one signal of `S` puts all its targets in `S`. For a design whose
processes are all edge processes (the FF-only profile) `S` = the input ports. -/
def MooreOut (d : Design2) : Prop :=
  ∃ S : String → Prop,
    (∀ n ∈ d.inputNames.toList, S n) ∧
    (∀ p ∈ d.processes.toList, p.isCombPhase = true → (∃ n ∈ processDataNames p, S n) →
      ∀ m ∈ processTargets p, S m) ∧
    ∀ o ∈ d.outputNames.toList, ¬ S o

/-! ## The reactive task kind -/

/-- **A reactive controller task** over parameters `P`. The ports are `clk`, `rst` and the data
inputs (inputs), and the outputs. The specification is a safety monitor with spec-side ghost
state, a predicate on the reset snapshot, and bounded-response obligations; see the module
docstring. -/
structure ReactTask (P : Type) where
  /-- The parameter values the statement covers. -/
  inRange : P → Prop
  /-- The clock input port (clocking only; its value is not observed). -/
  clk : String
  /-- The synchronous, active-high reset input port. -/
  rst : String
  /-- The data input ports at `p`, in port order (after `clk`, `rst`). -/
  inputs : P → List Sig
  /-- The output ports at `p`, in port order. -/
  outputs : P → List Sig
  /-- What the snapshot of a reset entry must show. -/
  atReset : (p : P) → Vals ((outputs p).map Prod.snd) → Prop
  /-- The ghost state of the safety monitor (`Unit` when the safety property is per cycle). -/
  Ghost : P → Type
  /-- The ghost state at a reset release. -/
  ginit : (p : P) → Ghost p
  /-- The ghost state after a cycle with these inputs and outputs. -/
  gnext : (p : P) → Ghost p → Vals ((inputs p).map Prod.snd) → Vals ((outputs p).map Prod.snd) →
    Ghost p
  /-- Safety: what every cycle's inputs and outputs must satisfy, given the ghost state before it. -/
  safe : (p : P) → Ghost p → Vals ((inputs p).map Prod.snd) → Vals ((outputs p).map Prod.snd) →
    Prop
  /-- The response obligations (for an arbiter: one per requester). -/
  Obl : P → Type
  /-- The trigger of an obligation, on a cycle's inputs. -/
  trig : (p : P) → Obl p → Vals ((inputs p).map Prod.snd) → Prop
  /-- The response of an obligation, on a cycle's outputs. -/
  resp : (p : P) → Obl p → Vals ((outputs p).map Prod.snd) → Prop

namespace ReactTask

variable {P : Type} (t : ReactTask P)

/-- The data input values of one cycle. -/
abbrev In (p : P) := Vals ((t.inputs p).map Prod.snd)

/-- The output values of one cycle. -/
abbrev Out (p : P) := Vals ((t.outputs p).map Prod.snd)

/-- Conjunct 1: the input ports are exactly `clk`, `rst`, then the data inputs; the output ports
exactly the outputs (names, order and widths); no two declarations share a name (so a port's
declared width is the width `KnownEntry` reads, and a known entry of every input exists). -/
def Interface (p : P) (d : Design2) : Prop :=
  inputPorts d = (t.clk, 1) :: (t.rst, 1) :: t.inputs p ∧ outputPorts d = t.outputs p ∧
    (d.decls.toList.map Decl.name).Nodup

/-- **The kind's output discipline** (a named slot, used once: `Disciplined`; the same for every
reactive task, so it takes no task): Moore by process, `MooreOut`, which already forbids every
combinational path from an input port to an output port (txtask-v2's rule 1 is not added). A
switch to the shared `MooreOutDep` (Moore by signal dependency) would replace this body only. -/
def OutDiscipline (d : Design2) : Prop :=
  MooreOut d

/-- Conjunct 2a: one clock, no asynchronous process at all, the clock not read as data; and the
output discipline. -/
def Disciplined (d : Design2) : Prop :=
  ClockedBy t.clk none d ∧ OutDiscipline d

/-- The stimulus entries `c, c + 1, …` drive the data inputs with the known values `xs`. -/
def InsAt (p : P) (stim : List SvState) (c : Nat) (xs : List (t.In p)) : Prop :=
  ∀ j x, xs[j]? = some x → ∃ e, stim[c + j]? = some e ∧ HoldAll e (t.inputs p) x

/-- The snapshots `c, c + 1, …` show the known output values `ys`. -/
def ShowsAt (p : P) (tr : List SvState) (c : Nat) (ys : List (t.Out p)) : Prop :=
  ∀ j y, ys[j]? = some y → ∃ st, tr[c + j]? = some st ∧ HoldAll st (t.outputs p) y

/-- The ghost state before cycle `j` of a segment with inputs `xs` and outputs `ys`. -/
def ghostAt (p : P) (xs : List (t.In p)) (ys : List (t.Out p)) (j : Nat) : t.Ghost p :=
  ((xs.zip ys).take j).foldl (fun g a => t.gnext p g a.1 a.2) (t.ginit p)

/-- **Safety** on a segment: every cycle's inputs and outputs satisfy `safe` at the ghost state. -/
def Safe (p : P) (xs : List (t.In p)) (ys : List (t.Out p)) : Prop :=
  ∀ j x y, xs[j]? = some x → ys[j]? = some y → t.safe p (t.ghostAt p xs ys j) x y

/-- **Bounded response** on a segment: an obligation triggered at the `K + 1` entries
`j, …, j + K` has its response in one of the snapshots `j, …, j + K`. -/
def Responds (p : P) (K : Nat) (xs : List (t.In p)) (ys : List (t.Out p)) : Prop :=
  ∀ (o : t.Obl p) (j : Nat), j + K < xs.length →
    (∀ i x, i ≤ K → xs[j + i]? = some x → t.trig p o x) →
    ∃ i y, i ≤ K ∧ ys[j + i]? = some y ∧ t.resp p o y

/-- **The guarantee on a segment**: the reset snapshot shows `y0` with `atReset`, then safety and
bounded response on the inputs `xs` and outputs `ys`. -/
def Guar (p : P) (K : Nat) (xs : List (t.In p)) (y0 : t.Out p) (ys : List (t.Out p)) : Prop :=
  t.atReset p y0 ∧ t.Safe p xs ys ∧ t.Responds p K xs ys

/-- Conjunct 3 (txtask-v2's rule 2): from every power-up state, under every schedule, on every
known stimulus (`ModelsPU`), in every completed run, at every reset release `c1`, for every list
`x0 :: xs` of inputs that the reset entry `c1 - 1` and the entries `c1, c1 + 1, …` (with `rst`
deasserted) drive, the snapshots `c1 - 1` (the reset entry's), `c1, c1 + 1, …` show known outputs
`y0, ys` meeting the guarantee. -/
def Follows (p : P) (K : Nat) (d : Design2) : Prop :=
  ModelsPU d fun stim tr =>
    ∀ (c1 : Nat) (x0 : t.In p) (xs : List (t.In p)), Released t.rst stim c1 (c1 + xs.length) →
      t.InsAt p stim (c1 - 1) (x0 :: xs) →
      ∃ (y0 : t.Out p) (ys : List (t.Out p)), ys.length = xs.length ∧
        t.ShowsAt p tr (c1 - 1) (y0 :: ys) ∧ t.Guar p K xs y0 ys

/-- The statement at one parameter value and response bound: the interface; the clock discipline,
the output discipline and termination from every power-up (`TerminatesPU`); the claims from every
power-up (`Follows`, rule 2); no x-creating construct (`XSafe`, rule 3). -/
def SatisfiedAt (p : P) (K : Nat) (d : Design2) : Prop :=
  t.Interface p d ∧ (t.Disciplined d ∧ TerminatesPU d) ∧ t.Follows p K d ∧ XSafe d

/-- **The challenge statement** for a design family `sem` with the response bound `K`. -/
def Statement (sem : P → Design2) (K : P → Nat) : Prop :=
  ∀ p, t.inRange p → t.SatisfiedAt p (K p) (sem p)

end ReactTask

end SvGolf

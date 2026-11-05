import SvGolf.Task

/-!
# svGolf sequential task statements (DRAFT of TRUSTED text, for review, 2026-11-03)

**Status: DRAFT of trusted text.** When the maintainers approve it, it becomes part of the trusted base
beside `SvGolf/Task.lean` (or moves into it). It is a separate module for now so that the draft
does not change `SvGolf/Task.lean`, which every task's statement, every record's trusted-file
hashes and the whole `tasks` library depend on. Nothing outside the draft tasks imports it.
Proof helpers for it live in `SvGolf/Seq.lean` (untrusted, kernel-checked).

Contents:

* `ClockedBy`: the clock discipline that replaces `Unclocked` for a clocked design.
* `SeqTask`: the cycle-exact Moore statement approved on 10/30 (warm-up fixtures such as the
  counter).
* the handshake shared by the public sequential tasks (contract decisions C1 to C5 of
  `design/sequential/CONTRACT.md`): reset release, `Idle`, start, latency, knownness;
* `TxTask` (held operands, a result at `done`: `matmul`) and `StreamTask` (a stream in, a stream
  out: `sorter`), each a bounded-latency rely/guarantee with a declared latency.

Read with `SvGolf/Task.lean` (ports, `Vals`, `HoldAll`, `Unclocked`) and the ls-sv semantics it rests
on (`LeanModels/Sv/Spec2.lean`, `Sem2.lean`).
-/

namespace SvGolf

open LeanModels.Sv

/-! ## Sequential tasks: `SeqTask` (the cycle-exact Moore form)

The shape the maintainers approved on 10/30 (`design/sequential/README.md`, section 2):
a state machine in Lean, Moore outputs read after the clock edge, a claim from
every reset, and the clock discipline `ClockedBy` in place of `Unclocked`.
`CombTask.toSeq` (`SvGolf/Seq.lean`) proves that a combinational task is the
one-point-state case of this statement. No public task uses `SeqTask` (it is
cycle-exact, so it leaves no design freedom); it is kept for warm-up fixtures
such as the counter. The public sequential tasks use `TxTask` (below).

### What a sequential task says

A task fixes, for every `N` in range: a clock input port, an optional reset
input port with its asserted level, the data inputs and the outputs (name and
width, in order), and a machine: a state type, the state after reset (`init`),
the next state (`step`) and the observation (`obs`). `SeqTask.Statement t sem`
says that at every `N` in range, `sem N` satisfies three conjuncts:

1. **`Interface`**: the input ports are exactly the clock, then the reset,
   then the data inputs, and the output ports exactly the task's outputs.
2. **`Disciplined` and `Terminates2`**: the clock discipline (`ClockedBy`,
   below) and termination under every schedule and stimulus.
3. **`Follows`**: in every completed run, for every start cycle `c0` and
   every list `ps` of spec inputs (reset asserted or not, plus known data
   values) whose first entry asserts reset, if the stimulus entries
   `c0, c0+1, ...` drive exactly `ps`, then the snapshots `c0, c0+1, ...`
   show on the output ports, as known values, the machine's observations,
   the machine being restarted at `init` by that first reset and stepped by
   `step` on every later non-reset entry (a later reset entry restarts it).

The protocol is ls-sv's: one stimulus entry is one clock period with one
rising edge of the clock port; the snapshot is taken after the edge and the
settle that follows, with the entry's inputs still applied. Under
`ClockedBy` that reading is exact, not an approximation: every edge process
is clocked by the clock input port, and nothing else reads that port.

### Why it cannot be satisfied vacuously (in addition to `CombTask`'s list)

* **A clock that never ticks, is tied, gated or derived, or is read as
  data.** `ClockedBy`: the clock is an input port, every edge process names
  it, an asynchronous reset uses the task's reset port, and no process reads
  the clock as data. (The loader's own guard, `LeanModels/Sv/ClockGuard2.lean`,
  refuses the same designs earlier; this conjunct is what the statement
  itself requires.)
* **History before the first reset.** The claim starts at a reset entry, so
  nothing depends on the 4-state start-up; and it starts at EVERY reset
  entry, so a design must forget, at each reset, everything the machine
  forgets.
* **A register that is never reset.** Outputs must hold KNOWN values
  (`LVec.ofBitVec`), so an output that depends on an unreset register (x
  after reset) fails conjunct 3.
* **Hypotheses that never hold.** As for `CombTask`, the hypothesis is
  about the STIMULUS (the list `ps` is universally quantified, and
  `Terminates2` gives a completed run for each stimulus).

### What it does NOT pin, on purpose

* the clock port's value in a stimulus entry (the clock is not observed as
  data: ruled on 2026-11-03, `docs/sv-kernel.md`, "Statement scope
  is narrower than E");
* synchronous versus asynchronous reset: both give the same post-edge
  snapshot (inputs change between edges), so the statement does not see the
  style, the cost does;
* anything before the first reset.

### Known restriction (a review point)

`ClockedBy` forbids every data read of the clock, including the plain copy
`assign t = clk` that a flattened child instance's clock connection becomes.
So a design whose flip-flops sit in a child instance cannot satisfy it; the
loader's guard accepts such copies. Widening `ClockedBy` to the guard's
copy-set rule is a later change to this text.

### Moore outputs

`obs` receives the cycle's inputs only so that a combinational task is the
one-point-state case. A task with registers should state a Moore machine
(`SeqTask.Moore`: the observation ignores its input); the task's review
checks it, the statement does not depend on it. -/

/-! ### Names a process reads (for the clock discipline) -/

mutual
/-- Every signal name an expression reads (source order, with repeats). -/
def exprNames : Expr2 → List String
  | .ident n => [n]
  | .lit _ | .unsupported _ _ => []
  | .unary _ a | .resizeSigned _ a | .squash2 a | .repl _ a | .reduce _ a | .resize _ a
  | .slice a _ _ => exprNames a
  | .binary _ l r | .scmp _ l r | .logical _ l r | .index l r _ => exprNames l ++ exprNames r
  | .ternary c t f => exprNames c ++ exprNames t ++ exprNames f
  | .concat parts => exprListNames parts.toList
termination_by structural e => e

/-- `exprNames` of a list of expressions, concatenated. -/
def exprListNames : List Expr2 → List String
  | [] => []
  | e :: es => exprNames e ++ exprListNames es
termination_by structural es => es
end

mutual
/-- Every signal name an assignment target mentions: the names it writes and
the names its indices read. -/
def lhsNames : Lhs2 → List String
  | .ident m => [m]
  | .slice m _ _ => [m]
  | .index m i _ => m :: exprNames i
  | .concat ps => lhsListNames ps
termination_by structural t => t

/-- `lhsNames` of a list of targets, concatenated. -/
def lhsListNames : List Lhs2 → List String
  | [] => []
  | t :: ts => lhsNames t ++ lhsListNames ts
termination_by structural ts => ts
end

mutual
/-- Every signal name a statement mentions: targets, conditions, case
subjects and patterns, right-hand sides. -/
def stmtNames : Stmt2 → List String
  | .blockingAssign t e | .nbaAssign t e => lhsNames t ++ exprNames e
  | .ifStmt c t e => exprNames c ++ stmtNames t ++ stmtOptNames e
  | .block body => stmtListNames body.toList
  | .caseStmt s items dflt _ _ =>
      exprNames s ++ itemListNames items.toList ++ stmtOptNames dflt
  | .unsupported _ _ => []
termination_by structural s => s

/-- `stmtNames` of an optional statement. -/
def stmtOptNames : Option Stmt2 → List String
  | none => []
  | some s => stmtNames s
termination_by structural o => o

/-- `stmtNames` of a list of statements, concatenated. -/
def stmtListNames : List Stmt2 → List String
  | [] => []
  | s :: ss => stmtNames s ++ stmtListNames ss
termination_by structural ss => ss

/-- The names a case item mentions: its patterns and its body. -/
def itemNames : CaseItem2 → List String
  | .mk pats body => exprListNames pats.toList ++ stmtNames body
termination_by structural it => it

/-- `itemNames` of a list of case items, concatenated. -/
def itemListNames : List CaseItem2 → List String
  | [] => []
  | it :: its => itemNames it ++ itemListNames its
termination_by structural its => its
end

/-- The names a process mentions as DATA: everything in its body (or its
target and value). The clock and reset names in an edge process's event
control are not data. -/
def processDataNames : Process2 → List String
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ | .alwaysComb b => stmtNames b
  | .assign t e => lhsNames t ++ exprNames e
  | .unsupported _ _ => []

/-- The clock of an edge process (`always_ff @(posedge c)`, `always
@(posedge c)`, `always_ff @(posedge c or negedge rn)`, `always_ff @(posedge c
or posedge r)`); `none` for every other process. -/
def edgeClock : Process2 → Option String
  | .alwaysFF c _ | .alwaysPlain c _ | .alwaysFFR c _ _ _ => some c
  | _ => none

/-- The asynchronous reset of an edge process (the `rn` of `posedge c or
negedge rn`, or the `r` of `posedge c or posedge r`), if it has one. Both
polarities name their reset, so the clock discipline below holds an
active-high reset to the task's reset port too. -/
def asyncReset : Process2 → Option String
  | .alwaysFFR _ r _ _ => some r
  | _ => none

/-- **The clock discipline** (replaces `Unclocked` for a task with a clock):
`k` is an input port of `d`; every edge-phase process (the processes ls-sv
runs at the clock edge, `Process2.isEdgePhase`) is clocked by `k`; an edge
process with an asynchronous reset uses the reset port `rst`; and no process
reads `k` as data. Under it, "one stimulus entry is one rising edge of `k`"
is the protocol, so an undriven, tied, derived or gated clock cannot occur. -/
def ClockedBy (k : String) (rst : Option String) (d : Design2) : Prop :=
  k ∈ d.inputNames.toList ∧
  ∀ p ∈ d.processes.toList,
    (p.isEdgePhase = true → edgeClock p = some k) ∧
    (∀ r, asyncReset p = some r → rst = some r) ∧
    k ∉ processDataNames p

/-- **A sequential svGolf task** for a one-parameter design family.
`clk = none` (with `rst = none` and a one-point `State`) is a combinational
task. `rst = some (name, level)`: the port `name` asserts reset when it
carries the 1-bit value `level`. `State`, `init`, `step`, `obs` are the spec
machine; `obs` is read AFTER the edge, with the cycle's inputs still applied. -/
structure SeqTask where
  /-- The parameter values the statement covers. -/
  inRange : Nat → Prop
  /-- The clock input port (`none`: no clock, a combinational task). -/
  clk : Option String
  /-- The reset input port and its asserted level (`none`: no reset). -/
  rst : Option (String × Bool)
  /-- The data input ports at parameter `N`: (name, width), in port order. -/
  inputs : Nat → List Sig
  /-- The output ports at parameter `N`: (name, width), in port order. -/
  outputs : Nat → List Sig
  /-- The spec machine's state. -/
  State : Nat → Type
  /-- The state after a reset. -/
  init : (N : Nat) → State N
  /-- The next state, on a cycle that does not assert reset. -/
  step : (N : Nat) → State N → Vals ((inputs N).map Prod.snd) → State N
  /-- The output values in a state, with the cycle's data inputs. -/
  obs : (N : Nat) → State N → Vals ((inputs N).map Prod.snd) → Vals ((outputs N).map Prod.snd)

namespace SeqTask

variable (t : SeqTask)

/-- A Moore task: the observation does not read the current input. -/
def Moore : Prop := ∀ N s v w, t.obs N s v = t.obs N s w

/-- The input ports, in order: the clock, the reset, then the data inputs. -/
def ports (N : Nat) : List Sig :=
  (t.clk.map fun k => (k, 1)).toList ++ (t.rst.map fun r => (r.1, 1)).toList ++ t.inputs N

/-- Conjunct 1: exactly these ports, names, order and widths included. -/
def Interface (N : Nat) (d : Design2) : Prop :=
  inputPorts d = t.ports N ∧ outputPorts d = t.outputs N

/-- Conjunct 2a: the clock discipline (no clock: no edge process at all,
`Unclocked`). -/
def Disciplined (d : Design2) : Prop :=
  match t.clk with
  | none => Unclocked d
  | some k => ClockedBy k (t.rst.map Prod.fst) d

/-- The data values of one cycle. -/
abbrev Ins (N : Nat) := Vals ((t.inputs N).map Prod.snd)

/-- The stimulus entry `e` drives the reset port at the level that means `r`
(asserted iff `r`). Without a reset port only `r = false` is available. -/
def RstDrives (e : SvState) (r : Bool) : Prop :=
  match t.rst with
  | none => r = false
  | some (n, lvl) =>
      SvState.lookup e n = some (LVec.ofBitVec (BitVec.ofBool (if r then lvl else !lvl)))

/-- The stimulus entry `e` drives the spec input `(r, v)`: the reset port at
the level for `r`, every data input at the known value in `v`. The clock
port's value is not constrained (ls-sv does not read it; `ClockedBy` says
nothing else may). -/
def Drives (N : Nat) (e : SvState) (p : Bool × t.Ins N) : Prop :=
  t.RstDrives e p.1 ∧ HoldAll e (t.inputs N) p.2

/-- The spec state after one cycle: a reset restarts at `init`, any other
cycle applies `step`. -/
def next (N : Nat) (s : t.State N) (r : Bool) (v : t.Ins N) : t.State N :=
  if r then t.init N else t.step N s v

/-- The spec machine's state after each cycle of `ps`, paired with that
cycle's data inputs. -/
def scan (N : Nat) : t.State N → List (Bool × t.Ins N) → List (t.State N × t.Ins N)
  | _, [] => []
  | s, (r, v) :: rest => (t.next N s r v, v) :: scan N (t.next N s r v) rest

/-- The snapshot `st` shows, as known values, the observation of the spec
state and inputs `a`. -/
def ObsOK (N : Nat) (st : SvState) (a : t.State N × t.Ins N) : Prop :=
  HoldAll st (t.outputs N) (t.obs N a.1 a.2)

/-- Where a claim may start: at an entry that asserts reset (a task with a
reset port); anywhere for a task without one (which the review checks is
stateless). -/
def StartOK (N : Nat) (ps : List (Bool × t.Ins N)) : Prop :=
  match t.rst with
  | none => True
  | some _ => ps.head?.map Prod.fst = some true

/-- Conjunct 3: in every completed run, from every start cycle `c0`, every
good spec-input list `ps` driven by the stimulus entries `c0, c0+1, ...`
gives the spec machine's observations in the snapshots `c0, c0+1, ...`. -/
def Follows (N : Nat) (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ (c0 : Nat) (ps : List (Bool × t.Ins N)), t.StartOK N ps →
      (∀ j p, ps[j]? = some p → ∃ e, stim[c0 + j]? = some e ∧ t.Drives N e p) →
      ∀ j a, (t.scan N (t.init N) ps)[j]? = some a →
        ∃ st, tr[c0 + j]? = some st ∧ t.ObsOK N st a

/-- The statement at one parameter value: interface; clock discipline and
termination; the machine's observations from every reset. -/
def SatisfiedAt (N : Nat) (d : Design2) : Prop :=
  t.Interface N d ∧ (t.Disciplined d ∧ Terminates2 d) ∧ t.Follows N d

/-- **The challenge statement** for a design family `sem : Nat → Design2`. -/
def Statement (sem : Nat → Design2) : Prop :=
  ∀ N, t.inRange N → t.SatisfiedAt N (sem N)

end SeqTask


/-! ## The handshake common to `TxTask` and `StreamTask` (contract decisions C1 to C5, C8;
`design/sequential/CONTRACT.md`)

Both statements are bounded-latency rely/guarantee contracts (the D11 shape of
`LeanModels/Sv/Contract.lean`) over the same handshake:

* **Reset (C1).** A synchronous, active-high input `rst`. A claim begins at a
  release cycle `c1`: the stimulus entry before it asserts `rst` (so `rst` was
  held at least one cycle) and every entry from `c1` on deasserts it. Nothing
  is claimed while `rst` is 1 or before the first reset.
* **Start and idle (C2).** `start` is a one-cycle pulse that the environment
  raises only when the design is `Idle`: from the release until the next
  start, and again from the cycle after the design shows that it has finished
  (for `TxTask`: `done` = 1; for `StreamTask`: its last output), until the
  next start. A start in a cycle where the design has just finished is
  accepted (back-to-back).
* **Latency (C3).** The submission's latency `lat ≥ 1` bounds, in cycles after
  the edge that samples `start`, when the design finishes: the snapshot of
  the start entry is cycle 0, and the design must finish at a cycle `≤ lat`.
  Finishing earlier is legal, and so is a data-dependent latency within `lat`.
* **Knownness (C4, C5).** The output flag (`done`, `out_valid`) is KNOWN in
  every cycle from the release on; the payload (`C`, `out_data`) only where
  the flag is 1.

The rely depends on what the design shows (`Idle` reads `done`), so it is
stated up to a HORIZON `h`: if the environment followed the protocol at every
cycle before `h`, the guarantee holds at every cycle before `h`. A violation
of the protocol at a later cycle cannot void an earlier claim. -/

/-- The snapshot or stimulus entry `st` binds the 1-bit signal `n` to the known
bit `b`. -/
def BitIs (st : SvState) (n : String) (b : Bool) : Prop :=
  SvState.lookup st n = some (LVec.ofBitVec (BitVec.ofBool b))

/-- The stimulus entry `c` exists and binds `n` to `b`. -/
def StimBit (stim : List SvState) (c : Nat) (n : String) (b : Bool) : Prop :=
  ∃ e, stim[c]? = some e ∧ BitIs e n b

/-- The snapshot `c` exists and binds `n` to `b`. -/
def TraceBit (tr : List SvState) (c : Nat) (n : String) (b : Bool) : Prop :=
  ∃ st, tr[c]? = some st ∧ BitIs st n b

/-- **C1**: `c1` is a release cycle of the synchronous reset `rst` within the
first `h` entries: the entry before `c1` asserts it, every entry in `[c1, h)`
deasserts it. -/
def Released (rst : String) (stim : List SvState) (c1 h : Nat) : Prop :=
  0 < c1 ∧ StimBit stim (c1 - 1) rst true ∧ ∀ c, c1 ≤ c → c < h → StimBit stim c rst false

/-! ## `TxTask`: held operands, a result at `done` (matmul) -/

/-- **A held-operand transaction task** over parameters `P`. The ports are `clk`,
`rst`, `start`, the operands (inputs) and `done`, the payload (outputs). When
the environment starts a transaction, it holds the operands until `done`
rises; the design raises `done` within the latency and then shows `result` of
the operands on the payload, holding both until the next start. -/
structure TxTask (P : Type) where
  /-- The parameter values the statement covers. -/
  inRange : P → Prop
  /-- The clock input port (clocking only; its value is not observed). -/
  clk : String
  /-- The synchronous, active-high reset input port (C1). -/
  rst : String
  /-- The start input port (C2). -/
  start : String
  /-- The operand input ports at `p`, in port order (after `start`). -/
  operands : P → List Sig
  /-- The `done` output port (C4), the first output. -/
  done : String
  /-- The payload output ports at `p`, in port order (after `done`). -/
  payload : P → List Sig
  /-- The function of the transaction. -/
  result : (p : P) → Vals ((operands p).map Prod.snd) → Vals ((payload p).map Prod.snd)

namespace TxTask

variable {P : Type} (t : TxTask P)

/-- Operand values at `p`. -/
abbrev Ops (p : P) := Vals ((t.operands p).map Prod.snd)

/-- Conjunct 1: the input ports are exactly `clk`, `rst`, `start`, then the
operands; the output ports exactly `done`, then the payload. -/
def Interface (p : P) (d : Design2) : Prop :=
  inputPorts d = (t.clk, 1) :: (t.rst, 1) :: (t.start, 1) :: t.operands p ∧
    outputPorts d = (t.done, 1) :: t.payload p

/-- Conjunct 2a: the clock discipline, with `rst` the only possible
asynchronous reset. -/
def Disciplined (d : Design2) : Prop :=
  ClockedBy t.clk (some t.rst) d

/-- The stimulus entry `c` exists and drives the operands with the values `x`. -/
def OpsAt (p : P) (stim : List SvState) (c : Nat) (x : t.Ops p) : Prop :=
  ∃ e, stim[c]? = some e ∧ HoldAll e (t.operands p) x

/-- **C2, `Idle`**: from the release `c1`, every start before cycle `c` has
been followed, before `c`, by a cycle showing `done` = 1. -/
def Idle (stim tr : List SvState) (c1 c : Nat) : Prop :=
  ∀ s, c1 ≤ s → s < c → StimBit stim s t.start true →
    ∃ c', s ≤ c' ∧ c' < c ∧ TraceBit tr c' t.done true

/-- **The rely, up to the horizon `h`**: from the release `c1`, every entry
before `h` drives `start` and the operands with known values; `start` is 1
only when `Idle`; and the operands of a start are held until the cycle in
which `done` first rises. -/
def Rely (p : P) (stim tr : List SvState) (c1 h : Nat) : Prop :=
  ∀ c, c1 ≤ c → c < h →
    (∃ b, StimBit stim c t.start b) ∧ (∃ x, t.OpsAt p stim c x) ∧
    (StimBit stim c t.start true → t.Idle stim tr c1 c) ∧
    ∀ s x, c1 ≤ s → s ≤ c → StimBit stim s t.start true → t.OpsAt p stim s x →
      (∀ c', s ≤ c' → c' < c → ¬ TraceBit tr c' t.done true) → t.OpsAt p stim c x

/-- **The guarantee, up to the horizon `h`** (C3, C4, C5): `done` is known at
every cycle from the release (so before it first rises after a start it is
0); and for every start `s` with operands `x`: `done` rises at a cycle
`≤ s + lat` (when that cycle is before `h`), and from the first cycle it is 1
until the next start it stays 1 with the payload equal to `result x`. -/
def Guar (p : P) (lat : Nat) (stim tr : List SvState) (c1 h : Nat) : Prop :=
  (∀ c, c1 ≤ c → c < h → ∃ b, TraceBit tr c t.done b) ∧
  ∀ s x, c1 ≤ s → s < h → StimBit stim s t.start true → t.OpsAt p stim s x →
    (s + lat < h → ∃ c, s ≤ c ∧ c ≤ s + lat ∧ TraceBit tr c t.done true) ∧
    ∀ c, s ≤ c → c < h → (∃ c', s ≤ c' ∧ c' ≤ c ∧ TraceBit tr c' t.done true) →
      (∀ s', s < s' → s' ≤ c → ¬ StimBit stim s' t.start true) →
      ∃ st, tr[c]? = some st ∧ BitIs st t.done true ∧ HoldAll st (t.payload p) (t.result p x)

/-- Conjunct 3: in every completed run, from every reset release, at every
horizon, the rely gives the guarantee. -/
def Follows (p : P) (lat : Nat) (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ c1 h, Released t.rst stim c1 h → t.Rely p stim tr c1 h → t.Guar p lat stim tr c1 h

/-- The statement at one parameter value and latency (C3: `lat ≥ 1`). -/
def SatisfiedAt (p : P) (lat : Nat) (d : Design2) : Prop :=
  t.Interface p d ∧ (t.Disciplined d ∧ Terminates2 d) ∧ 1 ≤ lat ∧ t.Follows p lat d

/-- **The challenge statement** for a design family `sem` with the latency
function `lat`. The checker's goal is `t.Statement design.sem lat ∧ lat p₀ = n`
for the latency `lat` the proof file defines, the scoring point `p₀` and the
declared number `n` (C3). -/
def Statement (sem : P → Design2) (lat : P → Nat) : Prop :=
  ∀ p, t.inRange p → t.SatisfiedAt p (lat p) (sem p)

end TxTask

/-! ## `StreamTask`: a stream in, a stream out (sorter; C8) -/

/-- **A stream transaction task** over parameters `P`. The ports are `clk`,
`rst`, `start`, `in_valid`, `in_data` (inputs) and `out_valid`, `out_data`
(outputs). After a start, the environment presents `count p` values on
`in_data`, one per cycle with `in_valid` = 1, beginning the cycle after the
start and without gaps; the design emits `spec p` of those values, one per
cycle with `out_valid` = 1 (gaps allowed), the last within the latency. -/
structure StreamTask (P : Type) where
  /-- The parameter values the statement covers. -/
  inRange : P → Prop
  /-- The clock input port (clocking only; its value is not observed). -/
  clk : String
  /-- The synchronous, active-high reset input port. -/
  rst : String
  /-- The start input port. -/
  start : String
  /-- The input valid port. -/
  inValid : String
  /-- The input data port. -/
  inData : String
  /-- The output valid port (the first output). -/
  outValid : String
  /-- The output data port. -/
  outData : String
  /-- The width of a value. -/
  width : P → Nat
  /-- The number of values per transaction. -/
  count : P → Nat
  /-- The function of the transaction: the output stream of an input stream. -/
  spec : (p : P) → List (BitVec (width p)) → List (BitVec (width p))

namespace StreamTask

variable {P : Type} (t : StreamTask P)

/-- Conjunct 1: exactly these ports, in this order. -/
def Interface (p : P) (d : Design2) : Prop :=
  inputPorts d = [(t.clk, 1), (t.rst, 1), (t.start, 1), (t.inValid, 1), (t.inData, t.width p)] ∧
    outputPorts d = [(t.outValid, 1), (t.outData, t.width p)]

/-- Conjunct 2a: the clock discipline. -/
def Disciplined (d : Design2) : Prop :=
  ClockedBy t.clk (some t.rst) d

/-- The entry or snapshot `st` binds the data port `n` to the value `v`. -/
def DataIs (p : P) (st : SvState) (n : String) (v : BitVec (t.width p)) : Prop :=
  SvState.lookup st n = some (LVec.ofBitVec v)

/-- An observation of the output stream in one cycle: `out_valid`, and the
value of `out_data` (meaningful only when valid). -/
abbrev Obs (p : P) := Bool × BitVec (t.width p)

/-- The snapshots `a, a+1, ...` show the observations `obs`: `out_valid` known,
and `out_data` known where valid. -/
def Shows (p : P) (tr : List SvState) (a : Nat) (obs : List (t.Obs p)) : Prop :=
  ∀ k o, obs[k]? = some o → ∃ st, tr[a + k]? = some st ∧ BitIs st t.outValid o.1 ∧
    (o.1 = true → t.DataIs p st t.outData o.2)

/-- The values emitted in a list of observations, in order. -/
def emitted (p : P) (obs : List (t.Obs p)) : List (BitVec (t.width p)) :=
  (obs.filter (·.1)).map (·.2)

/-- **C2 for streams, `Idle`**: from the release `c1`, every start before `c`
has had all its `count p` outputs emitted before `c`. -/
def Idle (p : P) (stim tr : List SvState) (c1 c : Nat) : Prop :=
  ∀ s, c1 ≤ s → s < c → StimBit stim s t.start true →
    ∃ obs : List (t.Obs p), s + obs.length ≤ c ∧ t.Shows p tr s obs ∧
      (t.emitted p obs).length = t.count p

/-- **The rely, up to the horizon `h`**: every entry from the release drives
`start`, `in_valid` and `in_data` with known values; `start` only when `Idle`;
`in_valid` is 1 exactly at the `count p` entries after each start. -/
def Rely (p : P) (stim tr : List SvState) (c1 h : Nat) : Prop :=
  ∀ c, c1 ≤ c → c < h →
    (∃ b, StimBit stim c t.start b) ∧
    (∃ e v, stim[c]? = some e ∧ t.DataIs p e t.inData v) ∧
    (StimBit stim c t.start true → t.Idle p stim tr c1 c) ∧
    (∀ s, c1 ≤ s → s < c → c ≤ s + t.count p → StimBit stim s t.start true →
      StimBit stim c t.inValid true) ∧
    ((∀ s, c1 ≤ s → s < c → c ≤ s + t.count p → ¬ StimBit stim s t.start true) →
      StimBit stim c t.inValid false)

/-- **The guarantee, up to the horizon `h`**: `out_valid` is known at every
cycle from the release, and 0 before the first start; for every start `s`
whose latency window ends before `h`, with input values `xs` (the `in_data`
of the `count p` entries after it), the observations from `s` to the next
start (or to `h`) emit exactly `spec xs`, none after `s + lat`. -/
def Guar (p : P) (lat : Nat) (stim tr : List SvState) (c1 h : Nat) : Prop :=
  (∀ c, c1 ≤ c → c < h → ∃ b, TraceBit tr c t.outValid b) ∧
  (∀ c, c1 ≤ c → c < h → (∀ s, c1 ≤ s → s ≤ c → ¬ StimBit stim s t.start true) →
    TraceBit tr c t.outValid false) ∧
  ∀ s (xs : List (BitVec (t.width p))), c1 ≤ s → s + lat < h → StimBit stim s t.start true →
    xs.length = t.count p →
    (∀ j v, xs[j]? = some v → ∃ e, stim[s + 1 + j]? = some e ∧ t.DataIs p e t.inData v) →
    ∀ e, s < e → e ≤ h → (∀ s', s < s' → s' < e → ¬ StimBit stim s' t.start true) →
      (e < h → StimBit stim e t.start true) →
      ∃ obs : List (t.Obs p), obs.length = e - s ∧ t.Shows p tr s obs ∧
        t.emitted p obs = t.spec p xs ∧ ∀ k o, obs[k]? = some o → lat < k → o.1 = false

/-- Conjunct 3: in every completed run, from every reset release, at every
horizon, the rely gives the guarantee. -/
def Follows (p : P) (lat : Nat) (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ c1 h, Released t.rst stim c1 h → t.Rely p stim tr c1 h → t.Guar p lat stim tr c1 h

/-- The statement at one parameter value and latency (`lat ≥ 1`). -/
def SatisfiedAt (p : P) (lat : Nat) (d : Design2) : Prop :=
  t.Interface p d ∧ (t.Disciplined d ∧ Terminates2 d) ∧ 1 ≤ lat ∧ t.Follows p lat d

/-- **The challenge statement** for a design family `sem` with the latency
function `lat`. -/
def Statement (sem : P → Design2) (lat : P → Nat) : Prop :=
  ∀ p, t.inRange p → t.SatisfiedAt p (lat p) (sem p)

end StreamTask

end SvGolf

import SvGolf.Task

/-!
# svGolf sequential task statements (TRUSTED text: the shared primitives final, the rest a DRAFT)

**Status: two parts.**

* **Final (decided 2026-11-07): the primitives the reactive kind shares.** These are the
  declarations of this file that `SvGolf/TaskReact.lean` (the kind `ReactTask`) and
  `tasks/arbiter/Spec.lean` reach, directly or through one another, and they are part of the
  trusted base:
  * the clock discipline: `ClockedBy`, `edgeClock`, `asyncReset`, `processDataNames`, and the names
    a process reads (`exprNames`, `exprListNames`, `lhsNames`, `lhsListNames`, `stmtNames`,
    `stmtOptNames`, `stmtListNames`, `itemNames`, `itemListNames`);
  * the reset release: `Released`, `StimBit`, `BitIs`;
  * txtask-v2's concrete runs (rule 2): `PowerUp`, `sigWidth`, `KnownEntry`, `KnownStim`,
    `run2At`, `RunsAt`, `ModelsPU`, `TerminatesPU`;
  * the names an assignment target writes: `lhsTargets`, `lhsListTargets`;
  * txtask-v2's rule 3: `XSafe`, `xsafeB`, `xsProc`, `xsStmt`, `xsOpt`, `xsStmts`, `xsItems`,
    `xsLhs`, `xsLhsList`, `xsWidth`, `xsWidthList`, `patOK`, `binW`, `constVal?`, `constNZ`,
    `sigSigned`, `unsignedIdx`, `scmpOp`;

  with the `Decidable` instances of `PowerUp`, `KnownEntry`, `KnownStim` and `XSafe`.
* **DRAFT of trusted text: everything else.** That is the sequential kinds and the tx/stream half
  of txtask-v2: `SeqTask`, `TxTask` and `StreamTask` with their v1 statements and their v2
  statements (`FollowsPU`, `SatisfiedAtV2`, `StatementV2`), rule 1 (`MooreOutDep`, `combDeps` and
  their helpers), `TraceBit` and `run2_eq_run2At`. They state the matmul and sorter tasks and the
  counter fixture, none of which is ranked yet.

The file is a module of its own so that it does not change `SvGolf/Task.lean`, which every task's
statement, every record's trusted-file hashes and the whole `tasks` library depend on. Only the
sequential tasks and the reactive kind import it. Proof helpers for it live in `SvGolf/Seq.lean`
(untrusted, kernel-checked).

Contents:

* `ClockedBy`: the clock discipline that replaces `Unclocked` for a clocked design.
* `SeqTask`: the cycle-exact Moore statement approved on 10/30 (warm-up fixtures such as the
  counter).
* the handshake shared by the public sequential tasks (contract decisions C1 to C5 of
  `design/sequential/CONTRACT.md`): reset release, `Idle`, start, latency, knownness;
* `TxTask` (held operands, a result at `done`: `matmul`) and `StreamTask` (a stream in, a stream
  out: `sorter`), each a bounded-latency rely/guarantee with a declared latency.
* **txtask-v2** (2026-11-05, the last section; its shared primitives final, the rest a DRAFT, as
  listed under Status): the versioned statements
  `SeqTask.StatementV2`, `TxTask.StatementV2`, `StreamTask.StatementV2`: v1's claims of every
  run from every power-up state (`ModelsPU`, rule 2), Moore outputs (`MooreOutDep`, rule 1) and
  no x-creating construct (`XSafe`, rule 3). Everything before that section is txtask-v1,
  unchanged but for the distinct-names conjunct of each `Interface` (decided 2026-11-06).

Read with `SvGolf/Task.lean` (ports, `Vals`, `HoldAll`, `Unclocked`) and the ls-sv semantics it rests
on (`LeanModels/Sv/Spec2.lean`, `Sem2.lean`).
-/

namespace SvGolf

open LeanModels.Sv

/-! ## Sequential tasks: `SeqTask` (the cycle-exact Moore form)

The shape approved on 10/30 (`design/sequential/README.md`, section 2):
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
   then the data inputs, and the output ports exactly the task's outputs; no
   two declarations share a name.
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
  data: decided 2026-11-03, `docs/sv-kernel.md`, "Statement scope
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

/-! ### Names a process reads (for the clock discipline; final) -/

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

/-- Conjunct 1: exactly these ports, names, order and widths included; no two declarations share a
name (so a port's declared width is the width `KnownEntry` reads). -/
def Interface (N : Nat) (d : Design2) : Prop :=
  inputPorts d = t.ports N ∧ outputPorts d = t.outputs N ∧ (d.decls.toList.map Decl.name).Nodup

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
`design/sequential/CONTRACT.md`; `BitIs`, `StimBit` and `Released` final, `TraceBit` a DRAFT)

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

/-! ## `TxTask`: held operands, a result at `done` (matmul; DRAFT of trusted text) -/

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
operands; the output ports exactly `done`, then the payload; no two declarations
share a name. -/
def Interface (p : P) (d : Design2) : Prop :=
  inputPorts d = (t.clk, 1) :: (t.rst, 1) :: (t.start, 1) :: t.operands p ∧
    outputPorts d = (t.done, 1) :: t.payload p ∧ (d.decls.toList.map Decl.name).Nodup

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

/-! ## `StreamTask`: a stream in, a stream out (sorter; C8; DRAFT of trusted text) -/

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

/-- Conjunct 1: exactly these ports, in this order; no two declarations share a name. -/
def Interface (p : P) (d : Design2) : Prop :=
  inputPorts d = [(t.clk, 1), (t.rst, 1), (t.start, 1), (t.inValid, 1), (t.inData, t.width p)] ∧
    outputPorts d = [(t.outValid, 1), (t.outData, t.width p)] ∧
      (d.decls.toList.map Decl.name).Nodup

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

/-! ## txtask-v2: every power-up, Moore outputs, no x-creating construct (TRUSTED text, 2026-11-05; in two parts)

**Status: in two parts** (the file's Status lists every declaration; the review summary is
`design/soundness/TXTASK-V2-REVIEW.md`). FINAL (decided 2026-11-07), because the reactive kind
uses them: the concrete runs of rule 2 (`PowerUp` to `TerminatesPU`, but for `run2_eq_run2At`),
`lhsTargets` and `lhsListTargets`, and rule 3 (`XSafe` and its helpers). DRAFT of trusted text:
`run2_eq_run2At`, the rest of rule 1 (`MooreOutDep`, `combDeps` and their helpers) and the v2
statements of `SeqTask`, `TxTask` and `StreamTask` (the last subsection). Everything above is
txtask-v1 and is unchanged, but for the distinct-names conjunct of each `Interface` (decided
2026-11-06). This section defines, for each kind, a versioned statement `StatementV2`. The tasks
state v2: `tasks/matmul/Spec.lean` (`TxTask.StatementV2`), `tasks/sorter/Spec.lean`
(`StreamTask.StatementV2`) and the counter fixture `tests/seq_counter/Spec.lean`
(`SeqTask.StatementV2`), and their references prove it.

**Why.** A soundness probe (its findings are summarized in `design/soundness/TXTASK-V2-REVIEW.md`)
found that v1 admits designs whose scored netlist is not the circuit the proof is about:

* **F1, the Mealy phantom.** A snapshot is taken after the edge and the settle WITH THE ENTRY'S
  INPUTS STILL APPLIED. An output that reads an input combinationally shows, in the snapshot, a
  value computed from the registers after the edge and the inputs before it; on the wire, the
  environment has moved the inputs by the next edge, and a consumer sees another value.
* **H1, x-optimism.** v1's claims are about the run from `initState2`, where a register without a
  reset is `x`, and ls-sv, like a simulator, resolves a decision on `x` one way (`if (x)` takes
  the else branch, IEEE 1800 §12.4). A never-reset `u <= u` read by `if (!u)` is the counter in
  that run; in the hardware `u` powers up 0 or 1, and Yosys may keep either branch (`h1_rare` was
  ACCEPTED end to end with a wrong scored netlist).

**The rulings (decided 2026-11-05).** IEEE 1800 decides DEFINED values (scheduling, the NBA
region, operators on known operands); ls-sv follows it and is never changed to accommodate the
pinned flow. An `x` is not a third value: it is a bit whose 0/1 value is not known (§6.3.1), and a
proof must hold for every resolution of it, as formal tools treat `x`. A simulator's resolution
(the else branch of `if (x)`) is not the semantics. So every run in v2 is ls-sv's semantics
(`design.sem`, `cycleStep2`) started from a CONCRETE state, on known inputs; nothing reads the
netlist or Yosys's 2-state operators.

**The v2 statement** (`SatisfiedAtV2`, per kind): v1's interface, clock discipline and latency
bound, unchanged, and

* **Rule 2, every power-up** (`TerminatesPU`, `FollowsPU`): termination and v1's behavioural
  claims, word for word, hold of every run from EVERY power-up state (`PowerUp`: every declared
  signal, 2-state ones included, holds some 0/1 value of its declared width; initializers play no
  part) on every known stimulus (`KnownStim`). This REPLACES v1's run from `initState2` (the x
  start): an uninitialized value is an unknown 0/1 value, so quantifying over every concrete start
  is the formal reading of the standard's x start. A design may decide on an unreset value, as
  long as its claims hold for every value that value can have.
* **Rule 1, Moore outputs** (`MooreOutDep`): no combinational path, control dependencies included,
  from an input port to an output port (the reset exempt for `TxTask`/`StreamTask`). It constrains
  the interface (a claimed snapshot is what the outputs show for the whole next period), not
  correctness.
* **Rule 3, no x-creating construct** (`XSafe`): structurally, no construct that can produce an
  `x` or `z` from known operands under the standard: run-time `/` and `%` by anything but a
  nonzero constant, `**` with a signed exponent unless the base is a nonzero constant, a
  dynamic-index read that can leave its range (a full-width index into a power-of-two vector is
  in range), a constant slice beyond its operand, width-mismatched bitwise and equality operands,
  an `x`/`z` literal outside a `casez`/`casex` pattern, a signed comparison that is not an order.
  With rule 2's concrete starts and known stimuli, every value a run computes is then known
  (`SvGolf/XFree.lean`, `xfree_expr`, `xfree_cycle`), so no decision of any run reads an `x`, and
  no simulator resolution of an unknown is ever taken.

What v2 does NOT close: a `unique`/`priority` case is validated by ls-sv on the snapshots, not
where it executes (round 1's W4, an ls-sv bug reported to the ls-sv lane; the source gate refuses
the qualifiers today); and ls-sv and the netlist can still differ on defined values (a Yosys or an
ls-sv bug), which only the sampled post-synthesis check looks for (obligation C).
-/

/-! ### The concrete runs (rule 2; final, but for `run2_eq_run2At`) -/

/-- **A power-up state** of `d`: every declaration, in declaration order, bound to a value of its
declared width whose every bit is `0` or `1`. 2-state declarations are included (ls-sv's
`initState2` starts them at `0`, the standard's 2-state initial value; a flip-flop powers up 0 or
1), and declaration initializers play no part (the clocked source gate refuses them). -/
def PowerUp (d : Design2) (st : SvState) : Prop :=
  st.map Prod.fst = d.decls.toList.map Decl.name ∧
    ∀ b ∈ st.zip d.decls.toList, b.1.2.width = b.2.width ∧ b.1.2.allKnown = true

instance (d : Design2) (st : SvState) : Decidable (PowerUp d st) :=
  inferInstanceAs (Decidable (st.map Prod.fst = d.decls.toList.map Decl.name ∧
    ∀ b ∈ st.zip d.decls.toList, b.1.2.width = b.2.width ∧ b.1.2.allKnown = true))

/-- The declared width of the signal `n` (its first declaration's; `Design2.declWidth` of ls-sv's
comb layer, restated here so that this file imports no proof layer). -/
def sigWidth (d : Design2) (n : String) : Option Nat :=
  (d.decls.toList.find? fun dc => dc.name == n).map Decl.width

/-- **A known stimulus entry**: every input port it binds holds a value of the port's declared
width whose every bit is `0` or `1`. An `x` on an input is a value the environment does not
know, and each of its resolutions is a known entry, so quantifying over known entries is the
formal reading of an `x` input. An input the entry does not bind keeps its value
(`applyInputs2`). -/
def KnownEntry (d : Design2) (e : SvState) : Prop :=
  ∀ n ∈ d.inputNames.toList,
    ((SvState.lookup e n).all fun v => v.allKnown && sigWidth d n == some v.width) = true

instance (d : Design2) (e : SvState) : Decidable (KnownEntry d e) :=
  inferInstanceAs (Decidable (∀ n ∈ d.inputNames.toList,
    ((SvState.lookup e n).all fun v => v.allKnown && sigWidth d n == some v.width) = true))

/-- Every entry of a stimulus is known. -/
def KnownStim (d : Design2) (stim : List SvState) : Prop := ∀ e ∈ stim, KnownEntry d e

instance (d : Design2) (stim : List SvState) : Decidable (KnownStim d stim) :=
  inferInstanceAs (Decidable (∀ e ∈ stim, KnownEntry d e))

/-- **`run2` from the state `st0`** in place of `initState2 d`: the same cycles (`runFrom2`), the
same qualified-case validation (`run2_eq_run2At`: `run2` is `run2At` from `initState2 d`). -/
def run2At (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (st0 : SvState)
    (stim : List SvState) : Res (List SvState) := do
  let tr ← runFrom2 d σ fuel st0 0 stim
  if d.processes.toList.any Process2.hasQualifiedCase then
    validateTraceChecks2 fuel d tr
  return tr

/-- `run2` is `run2At` from ls-sv's own start state. -/
theorem run2_eq_run2At (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
    run2 d σ fuel stim = run2At d σ fuel (initState2 d) stim := rfl

/-- Some fuel completes the run of `d` from `st0` under `σ` on `stim` with the trace `tr` (the
`Runs2` of `run2At`). -/
def RunsAt (d : Design2) (σ : ScheduleOracle) (st0 : SvState) (stim tr : List SvState) : Prop :=
  ∃ fuel, run2At d σ fuel st0 stim = .ok tr

/-- **Rule 2's judgment**: from every power-up state, under every schedule, on every known
stimulus, every completed run satisfies `P` (v1's `⊨₂`, whose runs start at `initState2 d`, with
the start quantified over the power-up states). -/
def ModelsPU (d : Design2) (P : List SvState → List SvState → Prop) : Prop :=
  ∀ st0, PowerUp d st0 → ∀ (σ : ScheduleOracle) (stim tr : List SvState), KnownStim d stim →
    RunsAt d σ st0 stim tr → P stim tr

/-- **Non-vacuity of `ModelsPU`**: from every power-up state, under every schedule, every known
stimulus completes (v1's `Terminates2` from the power-up states: a design that settles from the
x start but oscillates from a concrete one fails it). -/
def TerminatesPU (d : Design2) : Prop :=
  ∀ st0, PowerUp d st0 → ∀ (σ : ScheduleOracle) (stim : List SvState), KnownStim d stim →
    ∃ tr, RunsAt d σ st0 stim tr

/-! ### Rule 1: Moore outputs, by signal dependency (DRAFT of trusted text; `lhsTargets`, `lhsListTargets` final)

`MooreOutDep d exempt` says that no combinational path leads from an input port (other than the
`exempt` ones) to an output port. A path follows the combinational assignments (`combDeps`): an
assignment in an `always_comb` block or a continuous `assign` makes every signal it writes depend
on the signals its value reads, on its target (a partial write keeps the other bits) and the
target's indices, and on the condition of every enclosing `if` and the subject and items of every
enclosing `case` (control dependencies). Edge processes give no dependency: the clock edge ends a
path. The rule constrains the INTERFACE, not correctness: under it a claimed snapshot is what the
outputs show on the wire for the whole next period, so a consumer sees the claimed value. A Moore
machine written as ONE `always_comb` whose output assignments read only the state is admitted,
although the same block reads the inputs for the next state. Over-rejections, by design: a signal
assigned twice in one block takes both assignments' reads; a read masked by a constant still
counts. Not seen: a path through an asynchronous reset event (the clocked source gate refuses
asynchronous resets, `score/srcgate.py` item 6). -/

mutual
/-- The signals an assignment target writes (its index expressions are reads, not writes). -/
def lhsTargets : Lhs2 → List String
  | .ident m | .slice m _ _ | .index m _ _ => [m]
  | .concat ps => lhsListTargets ps
termination_by structural t => t

/-- `lhsTargets` of a list of targets, concatenated. -/
def lhsListTargets : List Lhs2 → List String
  | [] => []
  | t :: ts => lhsTargets t ++ lhsListTargets ts
termination_by structural ts => ts
end

/-- The names the patterns of a list of case items read. -/
def itemListPatNames : List CaseItem2 → List String
  | [] => []
  | it :: its => exprListNames it.pats.toList ++ itemListPatNames its

/-- One combinational dependency: a signal an assignment writes, and every signal its new value
may depend on. -/
abbrev DepEdge := String × List String

/-- The edges `es` under the control names `c` (an enclosing condition): each also depends on
`c`. -/
def underCtx (c : List String) (es : List DepEdge) : List DepEdge :=
  es.map fun e => (e.1, c ++ e.2)

mutual
/-- The dependencies of the assignments in a statement: an assignment `t = e` gives, for each
signal `t` writes, an edge to the names `t` mentions (its own: a partial write keeps the other
bits; its indices) and the names `e` reads; an enclosing `if` adds its condition's names, an
enclosing `case` its subject's and every item's (`underCtx`). -/
def stmtDeps : Stmt2 → List DepEdge
  | .blockingAssign t e | .nbaAssign t e =>
      (lhsTargets t).map fun m => (m, lhsNames t ++ exprNames e)
  | .ifStmt c th el => underCtx (exprNames c) (stmtDeps th ++ stmtOptDeps el)
  | .block body => stmtListDeps body.toList
  | .caseStmt s items dflt _ _ =>
      underCtx (exprNames s ++ itemListPatNames items.toList)
        (itemListDeps items.toList ++ stmtOptDeps dflt)
  | .unsupported _ _ => []
termination_by structural s => s

/-- `stmtDeps` of an optional statement. -/
def stmtOptDeps : Option Stmt2 → List DepEdge
  | none => []
  | some s => stmtDeps s
termination_by structural o => o

/-- `stmtDeps` of a list of statements, concatenated. -/
def stmtListDeps : List Stmt2 → List DepEdge
  | [] => []
  | s :: ss => stmtDeps s ++ stmtListDeps ss
termination_by structural ss => ss

/-- The dependencies of a case item's body. -/
def itemDeps : CaseItem2 → List DepEdge
  | .mk _ body => stmtDeps body
termination_by structural it => it

/-- `itemDeps` of a list of case items, concatenated. -/
def itemListDeps : List CaseItem2 → List DepEdge
  | [] => []
  | it :: its => itemDeps it ++ itemListDeps its
termination_by structural its => its
end

/-- The combinational dependencies of a process: those of an `always_comb` body and of a
continuous `assign`. An edge process writes its targets at the clock edge, which ends a
combinational path, so it contributes none. -/
def processDeps : Process2 → List DepEdge
  | .alwaysComb b => stmtDeps b
  | .assign t e => (lhsTargets t).map fun m => (m, lhsNames t ++ exprNames e)
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ _ | .unsupported _ _ => []

/-- Every combinational dependency of a design, by assignment. -/
def combDeps (d : Design2) : List DepEdge := d.processes.toList.flatMap processDeps

/-- **Rule 1, Moore outputs**: no combinational path leads from an input port outside `exempt`
to an output port. `S` is a set of signals that contains every such input, is closed along the
combinational dependencies (if an assignment depends on a signal in `S`, every signal it writes
is in `S`) and contains no output port. `SeqTask` exempts nothing; `TxTask` and `StreamTask`
exempt the reset port (see `TxTask.SatisfiedAtV2`). -/
def MooreOutDep (d : Design2) (exempt : List String) : Prop :=
  ∃ S : String → Prop,
    (∀ n ∈ d.inputNames.toList, n ∉ exempt → S n) ∧
    (∀ e ∈ combDeps d, (∃ r ∈ e.2, S r) → S e.1) ∧
    ∀ o ∈ d.outputNames.toList, ¬ S o

/-! ### Rule 3: no construct that creates an `x` from known operands (final)

Every place where ls-sv's evaluator (`evalExpr2`, `execStmt2`, the settle and the cycle) can yield
an `x` or `z` from a fully known state and known inputs, and how rule 3 rules it out (the
coverage argument is `SvGolf/XFree.lean`; the per-construct table is in
`design/soundness/TXTASK-V2-REVIEW.md`):

* an `x`/`z` digit in a literal: refused, except in a `casez`/`casex` item pattern, where the
  match is a known bit: a `z` digit, and in `casex` an `x` digit, is a wildcard; an `x` digit of a
  `casez` item is NOT a wildcard (it matches no known subject bit, IEEE 1800 §12.5.1, as in ls-sv's
  `caseBitMatches`), and the source gate refuses it (item 4);
* `/`, `%` (signed or not) by a zero divisor: all-`x` (`LVec.div`); admitted only with a divisor
  that is a nonzero known constant (a literal, through width conversions: `constNZ`);
* `**` with a signed negative exponent and a zero base: all-`x` (`LVec.pow`); admitted with an
  unsigned exponent, or a base that is a nonzero known constant;
* a dynamic-index read `v[i]` out of range: all-`x`; admitted when the index is unsigned (below)
  and every value of the index's width is in range (`2^width(i) * elemW ≤ width(v)`: a
  full-width index into a power-of-two vector);
* a SIGNED dynamic index, read or written: IEEE 1800 reads the index as a signed number, so a
  negative value is out of range (a read is `x`, a write has no effect, §11.5.1), while ls-sv
  reads every index unsigned (`toNat?` in `evalExpr2` and `resolveLhs2`), so ls-sv and the
  standard differ on known values (ls-sv's bug, W5 in the review). W5 has three forms. An index
  that mentions a signal DECLARED signed is refused here, structurally: rule 3 requires that a
  dynamic index, on either side of an assignment, mention no signal declared signed
  (`unsignedIdx`). A `$signed(…)` cast and a signed literal (`2'sb11`, signed by §11.8.1) are
  dropped by ls-sv's loader, so the loaded design shows an unsigned index and this rule cannot see
  them: the `fourstate` stage (slang's own types) refuses them until ls-sv's W5 fix (signedness
  kept through ingestion) lands, and then this structural clause is removed (decided
  2026-11-06);
* a constant slice beyond its operand's width: `x` bits (`LVec.extract`); admitted in range;
* `&`, `|`, `^`, `==`, `!=`, `==?`, `!=?` on operands of different widths: `x` (`LVec.zipWith`,
  `eqLogical`, `eqWildcard`); admitted at equal widths; `?:` arms must have equal widths (the
  value's width must not depend on the condition);
* a signed comparison node whose operator is not an order (`Expr2.scmp`, outside the extractor's
  contract): `x`; refused;
* an `unsupported` node: loud in ls-sv; refused.

Everything else is known on known operands: `+ - *`, shifts, the comparisons, `===`/`!==`,
`casez`/`casex` matches, `&&`/`||`, `!`, `~`, unary `-`/`+`, reductions, concatenation,
replication, width conversions, the 2-state conversion, `?:` on a known condition, every
assignment (the write window is clipped, an out-of-range dynamic write is a no-op), `if`/`case`,
the NBA commit, the settle. The rule is structural: `xsafeB` is a function of the design's syntax
and declared widths, evaluated by `decide`/`#guard` on a concrete design. -/

/-- A constant: a literal, through width conversions (its value). -/
def constVal? : Expr2 → Option LVec
  | .lit v => some v
  | .resize w a => (constVal? a).map (·.resizeU w)
  | .resizeSigned w a => (constVal? a).map (·.resizeSigned w)
  | _ => none

/-- A nonzero known constant: an admissible divisor (and base of `**` with a signed exponent). -/
def constNZ (e : Expr2) : Bool :=
  match constVal? e with
  | some v => v.allKnown && v.toNat != 0
  | none => false

/-- Rule 3 at a binary operator, from its operands `l`, `r` and their rule-3 widths `wl`, `wr`:
the width of the result, or `none` if the operator can create an `x` from known operands. -/
def binW (op : BinOp) (l r : Expr2) (wl wr : Option Nat) : Option Nat :=
  match op with
  | .add | .sub | .mul => do let a ← wl; let b ← wr; pure (max a b)
  | .div | .sdiv | .rem | .srem => do
      let a ← wl; let b ← wr; if constNZ r then pure (max a b) else none
  | .pow _ se => do let a ← wl; let _ ← wr; if !se || constNZ l then pure a else none
  | .shl _ | .shr _ | .ashl _ | .ashr _ => do let a ← wl; let _ ← wr; pure a
  | .and | .or | .xor => do let a ← wl; let b ← wr; if a = b then pure a else none
  | .eq | .ne => do let a ← wl; let b ← wr; if a = b then pure 1 else none
  | .wildEq | .wildNe => do let a ← wl; let b ← wr; if a = b then pure 1 else none
  | .caseEq | .caseNe | .casez | .casex => do let _ ← wl; let _ ← wr; pure 1
  | .land | .lor | .lt | .le | .gt | .ge | .slt | .sle | .sgt | .sge => do
      let _ ← wl; let _ ← wr; pure 1

/-- Whether the signal `n` is declared signed. -/
def sigSigned (d : Design2) (n : String) : Bool :=
  (d.decls.toList.find? fun dc => dc.name == n).any Decl.isSigned

/-- A dynamic index rule 3 reads as unsigned: it mentions no signal declared signed. -/
def unsignedIdx (d : Design2) (i : Expr2) : Bool :=
  (exprNames i).all fun n => !sigSigned d n

/-- The order comparisons, the operators of a signed comparison node. -/
def scmpOp : BinOp → Bool
  | .lt | .le | .gt | .ge => true
  | _ => false

mutual
/-- **Rule 3 for an expression**: `some w` when no construct in `e` can create an `x` from known
operands, `w` being the width of its value on a state that binds every signal at its declared
width; `none` otherwise. -/
def xsWidth (d : Design2) : Expr2 → Option Nat
  | .lit v => if v.allKnown then some v.width else none
  | .ident n => sigWidth d n
  | .unary .lnot a => (xsWidth d a).map fun _ => 1
  | .unary _ a => xsWidth d a
  | .resizeSigned w a => (xsWidth d a).map fun _ => w
  | .squash2 a => xsWidth d a
  | .binary op l r => binW op l r (xsWidth d l) (xsWidth d r)
  | .scmp op l r => if scmpOp op then (do let _ ← xsWidth d l; let _ ← xsWidth d r; pure 1) else none
  | .logical _ l r => do let _ ← xsWidth d l; let _ ← xsWidth d r; pure 1
  | .ternary c t f => do
      let _ ← xsWidth d c; let a ← xsWidth d t; let b ← xsWidth d f; if a = b then pure a else none
  | .concat parts => xsWidthList d parts.toList
  | .slice b lo w => do let a ← xsWidth d b; if lo + w ≤ a then pure w else none
  | .index b i ew => do
      let a ← xsWidth d b; let k ← xsWidth d i
      if unsignedIdx d i = true ∧ 2 ^ k * ew ≤ a then pure ew else none
  | .repl n a => (xsWidth d a).map (· * n)
  | .reduce _ a => (xsWidth d a).map fun _ => 1
  | .resize w a => (xsWidth d a).map fun _ => w
  | .unsupported _ _ => none
termination_by structural e => e

/-- `xsWidth` of a list of expressions: the sum of their widths. -/
def xsWidthList (d : Design2) : List Expr2 → Option Nat
  | [] => some 0
  | e :: es => do let a ← xsWidth d e; let b ← xsWidthList d es; pure (a + b)
termination_by structural es => es
end

/-- A case pattern under rule 3: a literal of any digits in a `casez`/`casex` item (the match is a
known bit: a `z` digit, and in `casex` an `x` digit, is a wildcard; an `x` digit of a `casez` item
matches no known subject bit, and the source gate refuses it), otherwise an expression rule 3
admits. -/
def patOK (d : Design2) (mode : CaseMode) (p : Expr2) : Bool :=
  match mode, p with
  | .casez, .lit _ | .casex, .lit _ => true
  | _, _ => (xsWidth d p).isSome

mutual
/-- Rule 3 for an assignment target: its dynamic indices, admitted and unsigned (an out-of-range
write has no effect, in ls-sv and in the standard, so its range is not checked). -/
def xsLhs (d : Design2) : Lhs2 → Bool
  | .ident _ | .slice _ _ _ => true
  | .index _ i _ => (xsWidth d i).isSome && unsignedIdx d i
  | .concat ps => xsLhsList d ps
termination_by structural t => t

/-- `xsLhs` of a list of targets. -/
def xsLhsList (d : Design2) : List Lhs2 → Bool
  | [] => true
  | t :: ts => xsLhs d t && xsLhsList d ts
termination_by structural ts => ts
end

mutual
/-- **Rule 3 for a statement**: every expression in it, in every branch. -/
def xsStmt (d : Design2) : Stmt2 → Bool
  | .blockingAssign t e | .nbaAssign t e => xsLhs d t && (xsWidth d e).isSome
  | .ifStmt c th el => (xsWidth d c).isSome && xsStmt d th && xsOpt d el
  | .block body => xsStmts d body.toList
  | .caseStmt s items dflt mode _ => (xsWidth d s).isSome && xsItems d mode items.toList && xsOpt d dflt
  | .unsupported _ _ => false
termination_by structural s => s

/-- `xsStmt` of an optional statement. -/
def xsOpt (d : Design2) : Option Stmt2 → Bool
  | none => true
  | some s => xsStmt d s
termination_by structural o => o

/-- `xsStmt` of a list of statements. -/
def xsStmts (d : Design2) : List Stmt2 → Bool
  | [] => true
  | s :: ss => xsStmt d s && xsStmts d ss
termination_by structural ss => ss

/-- Rule 3 for the items of a case of mode `mode`: their patterns and bodies. -/
def xsItems (d : Design2) (mode : CaseMode) : List CaseItem2 → Bool
  | [] => true
  | .mk pats body :: its =>
      (pats.toList.all fun p => patOK d mode p) && xsStmt d body && xsItems d mode its
termination_by structural its => its
end

/-- Rule 3 for a process. -/
def xsProc (d : Design2) : Process2 → Bool
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ | .alwaysComb b => xsStmt d b
  | .assign t e => xsLhs d t && (xsWidth d e).isSome
  | .unsupported _ _ => false

/-- **Rule 3, decided**: no process of `d` has a construct that can create an `x` from known
operands. -/
def xsafeB (d : Design2) : Bool := d.processes.toList.all (xsProc d)

/-- **Rule 3**: no construct of `d` can create an `x` or a `z` from known operands. -/
def XSafe (d : Design2) : Prop := xsafeB d = true

instance (d : Design2) : Decidable (XSafe d) := inferInstanceAs (Decidable (xsafeB d = true))

/-! ### The v2 statements (DRAFT of trusted text) -/

namespace SeqTask

variable (t : SeqTask)

/-- **Rule 2 for `SeqTask`**: v1's claim (`Follows`), word for word, of every run from every
power-up state on every known stimulus. -/
def FollowsPU (N : Nat) (d : Design2) : Prop :=
  ModelsPU d fun stim tr =>
    ∀ (c0 : Nat) (ps : List (Bool × t.Ins N)), t.StartOK N ps →
      (∀ j p, ps[j]? = some p → ∃ e, stim[c0 + j]? = some e ∧ t.Drives N e p) →
      ∀ j a, (t.scan N (t.init N) ps)[j]? = some a →
        ∃ st, tr[c0 + j]? = some st ∧ t.ObsOK N st a

/-- **The v2 statement at one parameter value**: the interface and the clock discipline (v1);
termination and the claims from every power-up (rule 2); rule 1 with no input exempt (the claim
starts AT the reset snapshot, whose wire reading is taken with the reset released, so an output
gated by the reset would show another value there); rule 3. -/
def SatisfiedAtV2 (N : Nat) (d : Design2) : Prop :=
  t.Interface N d ∧ (t.Disciplined d ∧ TerminatesPU d) ∧ t.FollowsPU N d ∧ MooreOutDep d [] ∧
    XSafe d

/-- **The v2 challenge statement** for a design family `sem : Nat → Design2`. -/
def StatementV2 (sem : Nat → Design2) : Prop :=
  ∀ N, t.inRange N → t.SatisfiedAtV2 N (sem N)

end SeqTask

namespace TxTask

variable {P : Type} (t : TxTask P)

/-- **Rule 2 for `TxTask`**: v1's claim (`Follows`: from every release, at every horizon, the
rely gives the guarantee), word for word, of every run from every power-up state on every known
stimulus. -/
def FollowsPU (p : P) (lat : Nat) (d : Design2) : Prop :=
  ModelsPU d fun stim tr =>
    ∀ c1 h, Released t.rst stim c1 h → t.Rely p stim tr c1 h → t.Guar p lat stim tr c1 h

/-- **The v2 statement at one parameter value and latency**: the interface, the clock discipline
and `lat ≥ 1` (v1); termination and the claims from every power-up (rule 2); rule 1 with the reset
port exempt; rule 3. Exempting `rst` is sound here: every claimed snapshot has `rst` = 0, and its
wire reading (the outputs during the next period, the next entry applied) differs only if the
next entry does not deassert `rst`, which ends the claims (C1); an asynchronous reset, which v1
admits, behaves the same way on the wire. -/
def SatisfiedAtV2 (p : P) (lat : Nat) (d : Design2) : Prop :=
  t.Interface p d ∧ (t.Disciplined d ∧ TerminatesPU d) ∧ 1 ≤ lat ∧ t.FollowsPU p lat d ∧
    MooreOutDep d [t.rst] ∧ XSafe d

/-- **The v2 challenge statement** for a design family `sem` with the latency function `lat`. -/
def StatementV2 (sem : P → Design2) (lat : P → Nat) : Prop :=
  ∀ p, t.inRange p → t.SatisfiedAtV2 p (lat p) (sem p)

end TxTask

namespace StreamTask

variable {P : Type} (t : StreamTask P)

/-- **Rule 2 for `StreamTask`**: as for `TxTask`, v1's claim of every run from every power-up
state on every known stimulus. -/
def FollowsPU (p : P) (lat : Nat) (d : Design2) : Prop :=
  ModelsPU d fun stim tr =>
    ∀ c1 h, Released t.rst stim c1 h → t.Rely p stim tr c1 h → t.Guar p lat stim tr c1 h

/-- **The v2 statement at one parameter value and latency**: as for `TxTask`. -/
def SatisfiedAtV2 (p : P) (lat : Nat) (d : Design2) : Prop :=
  t.Interface p d ∧ (t.Disciplined d ∧ TerminatesPU d) ∧ 1 ≤ lat ∧ t.FollowsPU p lat d ∧
    MooreOutDep d [t.rst] ∧ XSafe d

/-- **The v2 challenge statement** for a design family `sem` with the latency function `lat`. -/
def StatementV2 (sem : P → Design2) (lat : P → Nat) : Prop :=
  ∀ p, t.inRange p → t.SatisfiedAtV2 p (lat p) (sem p)

end StreamTask

end SvGolf

# txtask-v2: the diff for review (2026-11-06, revision 3)
**Superseded (a note of 2026-11-10; the rest of this file is unchanged history).** This is the review of
revision 3. The `TxTask` and `StreamTask` statements became final on 2026-11-08 (`SeqTask`'s stays a draft) and
were amended on 2026-11-09: rule 1 exempts nothing (`MooreOutDep d []`, so the quotes of `MooreOutDep d [t.rst]`
below are revision 3's), `TxTask.Guar` asks `done` = 0 from the release up to the first start, and `Disciplined`
refuses an asynchronous reset (`ClockedBy t.clk none`). The current text is `SvGolf/TaskSeq.lean`, whose Status
lists it; the tasks' `REVIEW.md` files review it.

**Status: DRAFT of trusted text, for the maintainers' review.** Branch `svgolf-txtask-v2`. Revision 2
implements the decisions of 2026-11-05 on round 1 (the first version of this file, and round
1's adversarial review, which found W1 to W4 and the over-rejection O1). Revision 3 closes what the
adversarial round on revision 2 found (section 9: a signed dynamic index admitted by rule 3, ls-sv's
W5; a contradiction between rule 3 and the `fourstate` stage on out-of-range writes; and two claims
of this file that were wrong), or records why it is out of v2's scope. Section 10 is an independent
review of revision 3: its claims re-measured, and three findings that remain open (the first, a
never-reset register that only holds its value, is a question for the maintainers). Section 11 records the
decisions of 2026-11-06 on section 8's questions as implemented: never-loaded registers refused in
every clocked task, rule 3's Python twin before the proof, the trusted-text wording. Nothing ranks.
Labels:
**MEASURED** = run on this branch, **READ** = read off the source, **DERIVED** = argued, **JUDGED** =
opinion.

## 0. The decisions this revision implements

* IEEE 1800 decides DEFINED values (scheduling, the NBA region, operators on known operands). ls-sv
  follows it and is never changed for Yosys/ABC; where the pinned flow deviates on defined values,
  svGolf disallows the design.
* An `x` is not a third value: it is a bit whose 0/1 value is not known, and a proof must hold for
  every resolution, as formal tools treat `x`. A simulator's resolution (`if (x)` takes the else
  branch) is not the semantics. Every run in the statement is ls-sv's semantics (`design.sem`) on
  concrete states; nothing reads the netlist or Yosys's 2-state operators.
* Rule 1 (Moore outputs) stays as drafted. Round 1's rule 2 (`KnownDecisions`: every decision on known
  bits) and the planned reset-refinement rule are REPLACED by the maintainers' approach, "requiring such
  programs work in either case": a new rule 2 (every power-up) and a new rule 3 (no x-creating
  construct).
* W4 (a `unique`/`priority` case checked on the wrong state) is ls-sv's bug, a dependency here.
* Obligation C (every known reference bit equals the netlist's on every trace) stays the sampled
  post-synthesis check.
* Revision 3 applies the same decisions to the attack on revision 2: where ls-sv deviates from
  IEEE 1800 on a defined value (a signed dynamic index, W5), the statement disallows the construct
  wherever the loaded design shows it, and the rest is a dependency on ls-sv's fix.

## 1. What changes

| file | trusted? | change |
|---|---|---|
| `SvGolf/TaskSeq.lean` | yes (draft) | the txtask-v2 section is rewritten: the concrete runs (`PowerUp`, `KnownEntry`, `KnownStim`, `run2At`, `RunsAt`, `ModelsPU`, `TerminatesPU`), rule 1 (unchanged, with a plain definition paragraph), rule 3 (`xsWidth`, `binW`, `constNZ`, `patOK`, `xsStmt`, `xsProc`, `xsafeB`, `XSafe`) and per kind `FollowsPU`, `SatisfiedAtV2`, `StatementV2`. Round 1's `KnownDecisions`, `decisionBits`, `DecKnown`, `preEdgeStates2`, `SnapDecKnown`, `EdgeDecKnown` are deleted (nothing uses them). Every txtask-v1 definition above the section is byte-identical. |
| `SvGolf/TaskSeq.lean`, revision 3 | yes (draft) | rule 3's dynamic-index clauses ask for an unsigned index (`sigSigned`, `unsignedIdx`, in `xsWidth`'s `.index` case and `xsLhs`), and the rule-3 docstring lists the signed index. Nothing else in the file changes. |
| `SvGolf/XFree.lean` | no (new) | the x-free lemma of rule 3: `xfree_expr`, `xfree_stmt`, `xfree_cycle`, `xfree_run`, `xfree_runsAt`; revision 3 changes one case (`xfree_expr`, `.index`: the range fact is the second half of the new condition). |
| `SvGolf/Seq.lean` | no | each v1 reduction split into a claim from a start state (`SeqTask.claim_of_cycle`, `TxTask.guar_of_phases`, `StreamTask.guar_of_phases`, over `RunFrom`, a run from any start) and the v1 theorem, now a corollary at `initState2`. |
| `SvGolf/SeqV2.lean` | no | rewritten: the v2 reductions (`SeqTask.satisfiedAtV2_of_cycle`, `TxTask.satisfiedAtV2_of_phases`, `StreamTask.satisfiedAtV2_of_phases`: v1's data, the shape holding at every power-up state), `TerminatesPU.of_invariant`, `powerUp_cons`/`powerUp_nil`, the power-up enumeration `powerUps` with `mem_powerUps`, rule 1's checker. Round 1's rule-2 helpers are deleted. |
| `tests/seq_counter/reference/cnt.lean`, `tasks/matmul/reference/matmul_g1.lean`, `tasks/sorter/reference/sorter_ins.lean` | no | the v2 section rewritten (designs unchanged); the sorter's first 903 lines are unchanged except its header item 5, reworded in place. |
| `tasks/{matmul,sorter}/Properties.lean`, `properties.json` | no (proved restatement; site text) | `Terminates` and `UnderProtocol` quantify over every power-up state and known stimulus; `DecisionsKnown` becomes `NoXCreating` (rule 3); the cards follow. |
| `tests/seq_counter/negative/Refute.lean` | no | the probe's twins refuted against revision 2; the shared refutation `cnt_not_followsPU`. |
| `tests/seq_counter/negative/Table.lean` | no (new) | the maintainers' acceptance table, section 4; revision 3 adds fixtures 12 to 16 (section 9). |
| `score/fourstate.py`, `score/tests/fourstate/{ok_oob_write,oob_signed_write}.sv` | checker (`fourstate` stage) | revision 3: rule (d) admits a WRITE through a bit/element select of a packed vector whose unsigned index can only pass the top of the range (an out-of-range write has no effect), so the stage agrees with rule 3 (section 9, finding 3); a signed write index stays refused with its own reason; two selftest fixtures; the docstring's claim that every task bans run-time `/` and `%` corrected. |
| `check/SvEval.lean`, `check/postsynth.py`, `check.py` | checker | the clocked post-synthesis check runs ls-sv from concrete power-up states (section 6). |
| `tests/checker/test_clocked_post.py`, `tests/seq_tx/x_cared.sv` | checker tests | two expected rejection messages follow the concrete starts (section 7). |
| `SvGolf.lean`, `tests.lean`, three `Spec.lean` docstrings | aggregators, docs | imports and wording. |
| `score/score.py`, `check.py` (`never_loaded`), `tests/seq_counter/never_loaded/`, `tests/checker/test_clocked_post.py` | checker, tests | 2026-11-06: never-loaded registers refused at `score` from the flow's own log (section 11.1 to 11.4). |
| `check/clocked_rules.py` (new; stage `clocked_rules`), `tests/checker/test_xsafe_twin.py`, `tests/seq_counter/xsafe/`, `tests/run.py` | checker, tests | 2026-11-06: rule 3's Python twin before the proof, and its agreement with `xsafeB` (11.5); the never-loaded advisory. |
| `SvGolf/TaskSeq.lean`, three `Spec.lean` | yes (draft), docstrings only | 2026-11-06: W5's three forms, the casez wording, no stale revision labels (11.6). |

## 2. The statement, rule by rule (the exact text, docstrings dropped)

Per kind, v2 is v1's interface, clock discipline and latency bound (unchanged), and the three rules:

```lean
namespace SeqTask

variable (t : SeqTask)

def FollowsPU (N : Nat) (d : Design2) : Prop :=
  ModelsPU d fun stim tr =>
    ∀ (c0 : Nat) (ps : List (Bool × t.Ins N)), t.StartOK N ps →
      (∀ j p, ps[j]? = some p → ∃ e, stim[c0 + j]? = some e ∧ t.Drives N e p) →
      ∀ j a, (t.scan N (t.init N) ps)[j]? = some a →
        ∃ st, tr[c0 + j]? = some st ∧ t.ObsOK N st a

def SatisfiedAtV2 (N : Nat) (d : Design2) : Prop :=
  t.Interface N d ∧ (t.Disciplined d ∧ TerminatesPU d) ∧ t.FollowsPU N d ∧ MooreOutDep d [] ∧
    XSafe d

def StatementV2 (sem : Nat → Design2) : Prop :=
  ∀ N, t.inRange N → t.SatisfiedAtV2 N (sem N)

end SeqTask

namespace TxTask

variable {P : Type} (t : TxTask P)

def FollowsPU (p : P) (lat : Nat) (d : Design2) : Prop :=
  ModelsPU d fun stim tr =>
    ∀ c1 h, Released t.rst stim c1 h → t.Rely p stim tr c1 h → t.Guar p lat stim tr c1 h

def SatisfiedAtV2 (p : P) (lat : Nat) (d : Design2) : Prop :=
  t.Interface p d ∧ (t.Disciplined d ∧ TerminatesPU d) ∧ 1 ≤ lat ∧ t.FollowsPU p lat d ∧
    MooreOutDep d [t.rst] ∧ XSafe d

def StatementV2 (sem : P → Design2) (lat : P → Nat) : Prop :=
  ∀ p, t.inRange p → t.SatisfiedAtV2 p (lat p) (sem p)

end TxTask

namespace StreamTask

variable {P : Type} (t : StreamTask P)

def FollowsPU (p : P) (lat : Nat) (d : Design2) : Prop :=
  ModelsPU d fun stim tr =>
    ∀ c1 h, Released t.rst stim c1 h → t.Rely p stim tr c1 h → t.Guar p lat stim tr c1 h

def SatisfiedAtV2 (p : P) (lat : Nat) (d : Design2) : Prop :=
  t.Interface p d ∧ (t.Disciplined d ∧ TerminatesPU d) ∧ 1 ≤ lat ∧ t.FollowsPU p lat d ∧
    MooreOutDep d [t.rst] ∧ XSafe d

def StatementV2 (sem : P → Design2) (lat : P → Nat) : Prop :=
  ∀ p, t.inRange p → t.SatisfiedAtV2 p (lat p) (sem p)

end StreamTask
```

### Rule 2: every power-up (`ModelsPU`, `TerminatesPU`)

```lean
def PowerUp (d : Design2) (st : SvState) : Prop :=
  st.map Prod.fst = d.decls.toList.map Decl.name ∧
    ∀ b ∈ st.zip d.decls.toList, b.1.2.width = b.2.width ∧ b.1.2.allKnown = true

instance (d : Design2) (st : SvState) : Decidable (PowerUp d st) :=
  inferInstanceAs (Decidable (st.map Prod.fst = d.decls.toList.map Decl.name ∧
    ∀ b ∈ st.zip d.decls.toList, b.1.2.width = b.2.width ∧ b.1.2.allKnown = true))

def sigWidth (d : Design2) (n : String) : Option Nat :=
  (d.decls.toList.find? fun dc => dc.name == n).map Decl.width

def KnownEntry (d : Design2) (e : SvState) : Prop :=
  ∀ n ∈ d.inputNames.toList,
    ((SvState.lookup e n).all fun v => v.allKnown && sigWidth d n == some v.width) = true

instance (d : Design2) (e : SvState) : Decidable (KnownEntry d e) :=
  inferInstanceAs (Decidable (∀ n ∈ d.inputNames.toList,
    ((SvState.lookup e n).all fun v => v.allKnown && sigWidth d n == some v.width) = true))

def KnownStim (d : Design2) (stim : List SvState) : Prop := ∀ e ∈ stim, KnownEntry d e

instance (d : Design2) (stim : List SvState) : Decidable (KnownStim d stim) :=
  inferInstanceAs (Decidable (∀ e ∈ stim, KnownEntry d e))

def run2At (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (st0 : SvState)
    (stim : List SvState) : Res (List SvState) := do
  let tr ← runFrom2 d σ fuel st0 0 stim
  if d.processes.toList.any Process2.hasQualifiedCase then
    validateTraceChecks2 fuel d tr
  return tr

theorem run2_eq_run2At (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
    run2 d σ fuel stim = run2At d σ fuel (initState2 d) stim := rfl

def RunsAt (d : Design2) (σ : ScheduleOracle) (st0 : SvState) (stim tr : List SvState) : Prop :=
  ∃ fuel, run2At d σ fuel st0 stim = .ok tr

def ModelsPU (d : Design2) (P : List SvState → List SvState → Prop) : Prop :=
  ∀ st0, PowerUp d st0 → ∀ (σ : ScheduleOracle) (stim tr : List SvState), KnownStim d stim →
    RunsAt d σ st0 stim tr → P stim tr

def TerminatesPU (d : Design2) : Prop :=
  ∀ st0, PowerUp d st0 → ∀ (σ : ScheduleOracle) (stim : List SvState), KnownStim d stim →
    ∃ tr, RunsAt d σ st0 stim tr
```

* **What it says.** v1's behavioural claim (`Follows`), word for word, and termination, for every run
  from EVERY power-up state (every declared signal, 2-state ones and initializers included, holding
  some 0/1 value of its declared width) on every known stimulus (every input an entry binds holds a
  0/1 value of its declared width). It replaces v1's run from `initState2` (the x start). An
  uninitialized value is an unknown 0/1 value, so quantifying over every concrete start is the formal
  reading of the standard's x start; an `x` driven on an input is one too, so the stimulus is
  quantified over known entries, which are its resolutions.
* **What it allows.** A design may decide on an unreset value, as long as the claims hold for every
  value it can have (fixtures 1, 4, 5 and the x-pessimistic fixture 0, which v1 rejected).
* **What it catches.** Every design that depends on how ls-sv resolves an unknown start value: the
  probe's H1 twins, W1 (fixture 2), W3 (fixture 6), a never-reset `bit` (fixture 7), a case on an
  unreset selector (fixture 8). Section 4.
* **Same semantics, other start.** `run2At` is `run2` with `initState2 d` replaced by `st0`
  (`run2_eq_run2At : run2 d σ fuel stim = run2At d σ fuel (initState2 d) stim := rfl`): ls-sv is not
  changed, and every run is the same `cycleStep2` (DERIVED from the definitions; READ).
* **Termination is from every power-up too.** `Follows` is about completed runs, so without it a
  design that settles from the x start but oscillates from a concrete one would satisfy the claims
  vacuously from those starts (DERIVED).

### Rule 1: Moore outputs (`MooreOutDep`), as drafted in round 1

```lean
def lhsTargets : Lhs2 → List String
  | .ident m | .slice m _ _ | .index m _ _ => [m]
  | .concat ps => lhsListTargets ps
termination_by structural t => t

def lhsListTargets : List Lhs2 → List String
  | [] => []
  | t :: ts => lhsTargets t ++ lhsListTargets ts
termination_by structural ts => ts
end

def itemListPatNames : List CaseItem2 → List String
  | [] => []
  | it :: its => exprListNames it.pats.toList ++ itemListPatNames its

abbrev DepEdge := String × List String

def underCtx (c : List String) (es : List DepEdge) : List DepEdge :=
  es.map fun e => (e.1, c ++ e.2)

mutual
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

def stmtOptDeps : Option Stmt2 → List DepEdge
  | none => []
  | some s => stmtDeps s
termination_by structural o => o

def stmtListDeps : List Stmt2 → List DepEdge
  | [] => []
  | s :: ss => stmtDeps s ++ stmtListDeps ss
termination_by structural ss => ss

def itemDeps : CaseItem2 → List DepEdge
  | .mk _ body => stmtDeps body
termination_by structural it => it

def itemListDeps : List CaseItem2 → List DepEdge
  | [] => []
  | it :: its => itemDeps it ++ itemListDeps its
termination_by structural its => its
end

def processDeps : Process2 → List DepEdge
  | .alwaysComb b => stmtDeps b
  | .assign t e => (lhsTargets t).map fun m => (m, lhsNames t ++ exprNames e)
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ _ | .unsupported _ _ => []

def combDeps (d : Design2) : List DepEdge := d.processes.toList.flatMap processDeps

def MooreOutDep (d : Design2) (exempt : List String) : Prop :=
  ∃ S : String → Prop,
    (∀ n ∈ d.inputNames.toList, n ∉ exempt → S n) ∧
    (∀ e ∈ combDeps d, (∃ r ∈ e.2, S r) → S e.1) ∧
    ∀ o ∈ d.outputNames.toList, ¬ S o
```

`MooreOutDep d exempt` says no combinational path leads from an input port outside `exempt` to an
output port. A path follows the combinational assignments (`combDeps`): an assignment in an
`always_comb` block or a continuous `assign` makes every signal it writes depend on the signals its
value reads, on its own target (a partial write keeps the other bits) and the target's indices, and
on the condition of every enclosing `if` and the subject and items of every enclosing `case` (control
dependencies). Edge processes give no dependency: the clock edge ends a path. `SeqTask` exempts
nothing, `TxTask`/`StreamTask` exempt `rst` (round 1's argument, unchanged; until 2026-11-09, when they too came
to exempt nothing: the claims up to a horizon cover the snapshot before an entry that asserts `rst`, which a
reset-gated output would hide on the wire). It constrains the
interface (a claimed snapshot is what the outputs show on the wire for the whole next period), not
correctness. It catches the probe's F1 (`f1m_refuted`).

### Rule 3: no x-creating construct (`XSafe`)

```lean
def constVal? : Expr2 → Option LVec
  | .lit v => some v
  | .resize w a => (constVal? a).map (·.resizeU w)
  | .resizeSigned w a => (constVal? a).map (·.resizeSigned w)
  | _ => none

def constNZ (e : Expr2) : Bool :=
  match constVal? e with
  | some v => v.allKnown && v.toNat != 0
  | none => false

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

def scmpOp : BinOp → Bool
  | .lt | .le | .gt | .ge => true
  | _ => false

def sigSigned (d : Design2) (n : String) : Bool :=
  (d.decls.toList.find? fun dc => dc.name == n).any Decl.isSigned

def unsignedIdx (d : Design2) (i : Expr2) : Bool :=
  (exprNames i).all fun n => !sigSigned d n

mutual
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

def xsWidthList (d : Design2) : List Expr2 → Option Nat
  | [] => some 0
  | e :: es => do let a ← xsWidth d e; let b ← xsWidthList d es; pure (a + b)
termination_by structural es => es
end

def patOK (d : Design2) (mode : CaseMode) (p : Expr2) : Bool :=
  match mode, p with
  | .casez, .lit _ | .casex, .lit _ => true
  | _, _ => (xsWidth d p).isSome

mutual
def xsLhs (d : Design2) : Lhs2 → Bool
  | .ident _ | .slice _ _ _ => true
  | .index _ i _ => (xsWidth d i).isSome && unsignedIdx d i
  | .concat ps => xsLhsList d ps
termination_by structural t => t

def xsLhsList (d : Design2) : List Lhs2 → Bool
  | [] => true
  | t :: ts => xsLhs d t && xsLhsList d ts
termination_by structural ts => ts
end

mutual
def xsStmt (d : Design2) : Stmt2 → Bool
  | .blockingAssign t e | .nbaAssign t e => xsLhs d t && (xsWidth d e).isSome
  | .ifStmt c th el => (xsWidth d c).isSome && xsStmt d th && xsOpt d el
  | .block body => xsStmts d body.toList
  | .caseStmt s items dflt mode _ => (xsWidth d s).isSome && xsItems d mode items.toList && xsOpt d dflt
  | .unsupported _ _ => false
termination_by structural s => s

def xsOpt (d : Design2) : Option Stmt2 → Bool
  | none => true
  | some s => xsStmt d s
termination_by structural o => o

def xsStmts (d : Design2) : List Stmt2 → Bool
  | [] => true
  | s :: ss => xsStmt d s && xsStmts d ss
termination_by structural ss => ss

def xsItems (d : Design2) (mode : CaseMode) : List CaseItem2 → Bool
  | [] => true
  | .mk pats body :: its =>
      (pats.toList.all fun p => patOK d mode p) && xsStmt d body && xsItems d mode its
termination_by structural its => its
end

def xsProc (d : Design2) : Process2 → Bool
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ | .alwaysComb b => xsStmt d b
  | .assign t e => xsLhs d t && (xsWidth d e).isSome
  | .unsupported _ _ => false

def xsafeB (d : Design2) : Bool := d.processes.toList.all (xsProc d)

def XSafe (d : Design2) : Prop := xsafeB d = true

instance (d : Design2) : Decidable (XSafe d) := inferInstanceAs (Decidable (xsafeB d = true))
```

* **What it says.** Every expression of every process has a rule-3 width (`xsWidth d e = some w`),
  which exists only when no construct in it can produce `x`/`z` from known operands, and every case
  pattern is such an expression or a literal of a `casez`/`casex` item. It is structural: `xsafeB` is
  a Boolean function of the design's text and declared widths, which `decide` evaluates on a
  concrete design and `simp` on a parametric one (the three references).
* **Constants** (fixture 4). A divisor (and the base of `**` with a signed exponent) is admitted when it
  is a known nonzero constant: a literal, through `resize`/`resizeSigned` (`constVal?`, `constNZ`).
  Anything else (a parameter-free expression, a signal) is refused. MEASURED: the extractor gives
  `q / 2'd3` as `.binary .div (.resize 2 (.ident "q")) (.lit 3)`, which passes.
* **Dynamic indices** (fixtures 10, 12 to 15). A read `v[i]` of `elemW`-bit elements is admitted
  when the index is unsigned and `2^width(i) * elemW ≤ width(v)`: every value the index can have is
  in range (a full-width index into a power-of-two vector). A write index must be an admitted,
  unsigned expression; its range is not checked, because an out-of-range write has no effect, in
  ls-sv (`resolveLhs2`) and in the standard (IEEE 1800-2023 §11.5.1), so no `x` is created
  (fixture 14). "Unsigned" (`unsignedIdx`, revision 3) is structural: the index mentions no signal
  declared signed. A signed index can be negative, which IEEE 1800 reads as out of range (a read is
  `x`, a write has no effect) and ls-sv reads as an unsigned number (`toNat?`): the two disagree on
  known values (MEASURED, fixtures 12 and 13), ls-sv's bug W5 (section 7). It is a sufficient
  condition for what the LOADED design shows, and only that: ls-sv's lowering drops a `$signed(…)`
  cast (`instExpr2`'s `.cast` arm, READ; MEASURED: `m[$signed(i)]` loads as `m[i]` with `i`
  unsigned, fixture 15), so a cast inside an index is invisible to the statement and is W5 too.
  It also refuses an index IEEE 1800 types as unsigned although it mentions a signed signal
  (`a[i + u]`, `i` signed, `u` unsigned: MEASURED, `xsafeB` false, `fourstate` passes it), an
  over-rejection recorded in section 7.
* **The x-free lemma** (`SvGolf/XFree.lean`, kernel-checked, axioms `propext`, `Classical.choice`,
  `Quot.sound`, MEASURED). A *known state* binds every signal to a 0/1 value of its declared width.
  * `xfree_expr`: on a known state, an expression with `xsWidth d e = some w` evaluates to a known
    value of width `w` (induction over `evalExpr2`/`evalExprs2`, one case per constructor and per
    operator);
  * `xfree_stmt`: every statement rule 3 admits keeps the state known and issues known NBA updates
    (induction over `execStmt2`/`execCase2`/`execStmts2`);
  * `xfree_combSettle`, `xfree_resetPass`, `xfree_edgePass`, `xfree_commit`, `xfree_apply`,
    `xfree_cycle`, `xfree_run`, `xfree_runsAt`: the settle, both passes, the commit, the input
    application of a known entry, a cycle and a run; `KnownState.of_powerUp`: a power-up state is
    known.
  * So every snapshot of every run of a rule-3 design from a power-up state on a known stimulus is
    known, every condition, subject, pattern, index and right-hand side the run evaluates is evaluated
    on a known state, and by `xfree_expr` its value is known: **no decision of any run in the statement
    reads an `x`, and no execution trace is needed** (DERIVED from the lemmas' statements).

### Rule 3's coverage: every way ls-sv's evaluator yields `x` from known inputs and state

READ off `LeanModels/Sv/Basic.lean`, `Semantics.lean` and `Sem2.lean` (`evalExpr2`, `evalBinOp`,
`evalUnaryOp`, `execStmt2`, `resolveLhs2`, `writeConcatLhs2`, `commitNba2`, `combSettle2`,
`cycleStep2`); each "admitted" row is a case of `xfree_expr`/`xfree_stmt`, so the table is checked by
the kernel, not only read.

| construct (ls-sv function) | `x`/`z` from known operands and state when | rule 3 (`xsWidth`, `binW`, `patOK`, `xsStmt`) |
|---|---|---|
| literal (`Expr2.lit`) | it has an `x`/`z` digit | refused, except as a `casez`/`casex` item pattern (`patOK`): there the match is a known bit (a `z` digit, and in `casex` an `x` digit, is a wildcard; an `x` digit of a `casez` item is not, and matches no known subject bit, in ls-sv's `caseBitMatches` and in IEEE 1800 §12.5.1; the source gate refuses that digit, item 4, and `load_sv` with it: MEASURED, section 10) |
| `/`, `%`, signed `/`, `%` (`LVec.div`, `sdiv`, `rem`, `srem`) | the divisor is 0 | admitted only when the divisor is a nonzero known constant (`constNZ`: a literal through `resize`/`resizeSigned`) |
| `**` (`LVec.pow`) | signed exponent negative and base 0 | admitted with an unsigned exponent, or a base that is a nonzero known constant |
| dynamic index read `v[i]` (`Expr2.index`) | the index is out of range | admitted when the index is unsigned (`unsignedIdx`) and `2^width(i) * elemW ≤ width(v)`: every value of the index is in range (a full-width index into a power-of-two vector) |
| signed dynamic index, read or write (`Expr2.index`, `Lhs2.index`) | never in ls-sv, which reads it unsigned (`toNat?`); IEEE 1800 reads a negative index as out of range (`x` read, no write), so ls-sv deviates on defined values (W5) | refused: the index mentions no signal declared signed (`unsignedIdx`, revision 3); a `$signed` cast is dropped by ls-sv's lowering and invisible here (W5) |
| constant slice `v[lo +: w]` (`Expr2.slice`, `LVec.extract`) | `lo + w > width(v)`: the bits beyond are `x` | admitted in range |
| `&`, `\|`, `^` (`LVec.zipWith`) | the operand widths differ: all-`x` | admitted at equal widths |
| `==`, `!=` (`eqLogical`) | the operand widths differ | admitted at equal widths |
| `==?`, `!=?` (`eqWildcard`) | the operand widths differ | admitted at equal widths (a known right operand has no wildcard bit) |
| `?:` (`LVec.ternary`) | never on a known condition (the arms' merge needs an unknown one) | arms of equal widths (so the value's width does not depend on the condition) |
| signed comparison node (`Expr2.scmp`) | its operator is not `<`, `<=`, `>`, `>=` (outside the extractor's contract): `x` | refused unless an order |
| `unsupported` node | loud, never a value | refused |
| `+`, `-`, `*`, unary `-`, `+` (`add`, `sub`, `mul`, `neg`, `pos`) | never (the collapse needs an unknown bit) | admitted |
| shifts (`shl`, `shr`, `ashl`, `ashr`) | never (an unknown amount needs an unknown bit) | admitted |
| `<`, `<=`, `>`, `>=`, signed forms (`relOp`, `signedRelOp`) | never | admitted |
| `===`, `!==`, `casez`/`casex` matches (`eqCase`, `matchesCase`) | never (always a known bit) | admitted |
| `&&`, `\|\|`, `!` (`Expr2.logical`, `truthy`, `lnot`) | never on known operands | admitted |
| `~`, reductions, concatenation, replication (`not`, `evalRedOp`, `concatMany`, `replVec`) | never | admitted |
| width conversions, 2-state conversion (`resizeU`, `resizeSigned`, `toTwoState`) | never (zero/sign fill, x to 0) | admitted |
| blocking/nonblocking write, any target (`insertAt`, `resolveLhs2`, `writeConcatLhs2`) | never: the window is clipped, an out-of-range or unknown dynamic write is a no-op, a concatenated target's parts are in range | admitted (a dynamic write index must itself pass, and be unsigned) |
| `if`, `case` (every mode), `unique`/`priority` (`execStmt2`, `execCase2`) | never: they choose, they do not produce values | admitted; patterns as above |
| NBA commit, settle, reset phase, edge phase, input application (`commitNba2`, `combSettle2`, `resetPass2`, `edgePass2`, `applyInputs2`) | an input bound to an `x` or at the wrong width | the stimulus is known (rule 2's `KnownStim`) |
| start state (`initState2`) | every undeclared-initializer signal is `x` | replaced by every power-up state (rule 2's `PowerUp`) |

## 3. What each rule catches, and why all three are needed

* **Rule 2 alone does not stop an `x` made inside a run.** W2 (`d / d`, fixture 3), an out-of-range
  read (fixture 10a) and `s === 1'bx` (fixture 9) pass rule 2 from every power-up state (MEASURED,
  `#guard boundedPU` in `Table.lean`): ls-sv makes the `x` (0/0, `a[3]`) or tests against it, and its
  x-optimistic branch is the counter's. Only rule 3 refuses them.
* **Rule 3 alone does not stop a decision on an unreset value.** The H1 twins, W1, W3 and fixtures 7
  and 8 have no x-creating construct (MEASURED: `xsafeB` true for the twins, `#guard` in
  `Refute.lean`); the `x` of v1's run is the start state's, which rule 2 replaces.
* **Rules 2 and 3 together**: every value of every run is known (`xfree_runsAt`), so no simulator
  resolution of an unknown is ever taken, and the claims hold, in ls-sv's semantics, from every
  power-up state (DERIVED). Revision 2 said "for every power-up the hardware can have"; that claimed
  more than the rules give. That ls-sv's semantics of the loaded design is the standard's on
  DEFINED values is not something these rules show: it is ls-sv's faithfulness (its lowering and
  evaluator against IEEE 1800, differentially tested by ls-sv), and on the scored netlist it is
  obligation C (sampled). The attack on revision 2 found one such deviation, the signed dynamic
  index (W5), which rule 3 now refuses where the loaded design shows it (section 9).
* **Rule 1** is independent of both: F1 has neither an unreset register nor an x-creating construct
  (MEASURED: `f1m` passes `xsafeB`, `#guard` in `Refute.lean`; fails `MooreOutDep`, `f1m_refuted`).

## 4. The acceptance table (MEASURED verdicts)

`tests/seq_counter/negative/Table.lean` (hand-built twins of the `.sv` fixtures, MEASURED equal to the
loaded designs by `reprStr`, see below; the `.sv` files are in the session scratchpad, not on the
branch). "kernel" = a kernel-checked theorem; "bounded" = a kernel-checked theorem that from EVERY
power-up state (`puRun`, with `puRun_spec` and `mem_powerUps`) the run on one stimulus (reset, count
twice, hold, reset while `en` is high, count) shows the counter, widened by `#guard` (interpreted) to
every stimulus of three entries beginning with a reset under both schedules (`boundedPU`). Neither
"bounded" form is a proof of `FollowsPU` (every stimulus): a full acceptance proof is a reference
proof's work, which the counter's `cnt.lean` is (section 5).

| # | fixture | v1 (x start) | v2 verdict | rule | how v2's verdict is shown | gate / `fourstate` today |
|---|---|---|---|---|---|---|
| 0 | `u ^ u`, `u` unreset, `q + (1 ^ (u ^ u))` | REJECT (x-pessimistic: `q = x`) | **ACCEPT** | | rules 1, 3 kernel (`f0_moore`, `f0_xsafe`); rule 2 bounded (`f0_everyPU`) | pass / pass |
| 1 | `t = u; t = 0; if (t)` | accept | **ACCEPT** | | rules 1, 3 kernel; rule 2 bounded (`f1_everyPU`) | pass / pass |
| 2 | W1: `t = u; if (!t) ...; t = 0` | accept | **REJECT** | 2 | kernel `f2_refuted`: power-up `u = 0` saturates at 1 | pass / pass |
| 3 | W2: `(d / d) != 1` | accept | **REJECT** | 3 | kernel `f3_refuted` (`¬ XSafe`: a signal divisor) | pass / pass |
| 4 | `q / 2'd3` | accept | **ACCEPT** | | rules 1, 3 kernel (`constNZ`); rule 2 bounded (`f4_everyPU`) | pass / pass |
| 5 | O1: unreset `b` behind `busy` | accept | **ACCEPT** (round 1 rejected) | | rules 1, 3 kernel; rule 2 bounded (`f5_everyPU`) | pass / pass |
| 6 | W3 at `N = 2`: reset sets `g` from `q - p == 2` | accept | **REJECT** | 2 | kernel `f6_refuted`: power-up `q = 2, p = 0` counts by 2 | pass / pass |
| 7 | `bit u` never reset, `if (u) q <= 0` | accept (2-state start 0) | **REJECT** | 2 | kernel `f7_refuted`: power-up `u = 1` holds `q` | pass / pass |
| 8 | `case (s)` unreset, default arm counts | accept (`x` matches no item) | **REJECT** | 2 | kernel `f8_refuted`: power-up `s = 1` holds `q` | pass / pass |
| 9 | `if (s === 1'bx)`, `s` unreset | REJECT (`x === x` is 1) | **REJECT** | 3 | kernel `f9_refuted` (`¬ XSafe`: an `x` literal outside a `casez`/`casex` pattern) | REFUSED (x literal) / not reached |
| 10a | `a[i]`, `a` 3 bits, `i` 2 bits | accept | **REJECT** | 3 | kernel `f10a_refuted` (`¬ XSafe`) | pass / REFUSED (rule (d)) |
| 10b | `a[i]`, `a` 4 bits, `i` 2 bits | accept | **ACCEPT** | | rules 1, 3 kernel; rule 2 `#guard` (`boundedPU f10b 1 2`) | pass / pass |
| 11 | W4: `unique case` violated before an edge | accept | depends on ls-sv's W4 fix | (termination, after the fix) | `#guard`: the run completes; `validateProcessChecks2` at the edge's state gives `CaseCheck:unique` | REFUSED (`unique`) / not reached |
| | probe H1 `h1x`, `h1r` | accept | **REJECT** | 2 | kernel `h1x_refuted`, `h1r_refuted` (power-up `u = 0`) | pass / pass |
| | probe F1 `f1m` | accept | **REJECT** | 1 | kernel `f1m_refuted` | pass / pass |
| 12 | signed read index `m[i]`, `i = 2'b11` after reset (attack finding 2) | accept | **REJECT** (revision 2 ACCEPTED: rules 1, 3 and rule 2 bounded, MEASURED) | 3 | kernel `f12_refuted` (`¬ XSafe`: the index mentions a signed signal); rule 2 alone passes it (`#guard`) | pass / REFUSED (rule (d), signed index) |
| 13 | signed write index `t[i] = 1` (finding 2) | accept | **REJECT** (revision 2 ACCEPTED, MEASURED) | 3 | kernel `f13_refuted`; rule 2 alone passes it (`#guard`) | pass / REFUSED (rule (d), signed write index) |
| 14 | unsigned write index out of range, `t[k]`, `t` 3 bits, `k` 2 bits (finding 3) | accept | **ACCEPT** | | rules 1, 3 kernel (`f14_xsafe`, `f14_moore`); rule 2 `#guard` (`boundedPU f14 1 2`) | pass / pass (REFUSED before revision 3's write exception) |
| 15 | `m[$signed(i)]`, `i` unsigned (finding 2) | accept | **ACCEPT, wrongly: depends on ls-sv's W5 fix** | | kernel `f15_xsafe`: the loaded design is fixture 12 with `i` unsigned (the cast is dropped); rule 2 `#guard` | pass / REFUSED (rule (d), signed index) |
| 16 | `q + ((a + b) >> 1)`, 1-bit `a = b = 1` (finding 1, the context width) | `N = 2`: accept | **ACCEPT at `N = 2`**, REJECT at `N = 1` (as IEEE 1800) | 2 at `N = 1` | `N = 2`: rules 1, 3 and rule 2 on every power-up (kernel, `f16_everyPU`); `N = 1`: kernel `f16n1_refuted` (power-up zeros, `q = 0` after `reset; en`) | pass / pass |

Every v1 column entry is MEASURED by `#guard boundedInit` (ls-sv's run from `initState2`, every
stimulus of two or three entries beginning with a reset), except fixture 11's (its own `#guard`);
the hand-built twins are MEASURED equal to the loaded `.sv` fixtures (`reprStr (design.sem N)`, `load_sv` with the counter task's probe points, all
eleven loadable ones of fixtures 0 to 11 true, and all six of fixtures 12 to 16, at `N = 1` and, for
16, at `N = 2`); the gate and `fourstate` columns by `score/srcgate.py --clock clk` and
`score/fourstate.py --task tests/seq_counter` (scoring point `N = 8`) on the `.sv` files. Axioms of
every theorem in the table: `propext`, `Quot.sound`, and `Classical.choice` for the run refutations
(MEASURED, `#print axioms`).

**Fixtures 12, 13 and 15 against the standard** (MEASURED, 2026-11-06): Icarus 12 on the source
holds `q` at 0 for all three at `N = 1, 2, 8` (the index is -1: `x` read, no write), ls-sv from the
zero power-up counts (`svgolf-eval --trace --start zeros`), and the Yosys netlist from Verilator's
zero start (`randReset 0`) holds `q` at 0 (19, 15 and 18 mismatching cycles of 29; the netlist
is 0 GE, a constant). Fixtures 14, 16 and the packed-array form of finding 5 (`data[i]`, `data`
`logic [3:0][1:0]`): Icarus, ls-sv and the netlist agree (0 mismatches of 29, 77.993 GE: the
counter's netlist), and fixture 16 at `N = 1` holds `q` in Icarus and ls-sv alike.

**Fixture 9, decided.** From every concrete start `s === 1'bx` is 0, so ls-sv's runs from the power-up
states are the counter, and rule 2 alone would accept it (MEASURED, `#guard`). It is rejected,
because a case equality against an `x` literal tests a simulator value that no concrete run has:
rule 3 admits an `x`/`z` literal only as a `casez`/`casex` item pattern, where the digit is a wildcard,
which is the source gate's own line (item 4: "every x/z literal digit outside a casez/casex item
wildcard", MEASURED refusal of this fixture). v1, from the x start, rejected it for the opposite
reason (`x === x` is 1).

**Fixture 5's price.** At the counter's scale the reset of `b` costs nothing: the pinned clocked flow
gives the same netlist with and without it (MEASURED: `score.py --seq`, 77.993 GE, 8 flops, both; Yosys
merges `b` with `busy`). The price of resetting data registers that v2 no longer asks for is round 1's
measurement (MEASURED there): the sorter's 64 cell bits 78.3 GE (6.1%) at (8, 8), matmul's `a_sh`/`b_sh`
429.7 GE (2.1%) at (4, 8, 32). Neither reference pays it (the sorter's algorithm needs zeroed cells;
matmul decides on no datapath bit).

**Fixture 11 (W4), the dependency.** ls-sv validates a `unique`/`priority` case on the snapshots
(`validateTraceChecks2`), not in the state where it executes, so W4's violation (both items match only
in the state the edge reads) is invisible: the run completes and v2's rules see nothing (MEASURED,
`#guard`). The fix is ls-sv's (reported to the ls-sv lane): validate at the state the body runs on.
After it, the violating run ends loud, so no run completes on that stimulus and `TerminatesPU` refutes
the design (DERIVED). Until then the source gate's refusal of the qualifiers is what closes it.

## 5. The three references prove revised v2 (designs unchanged)

**How** (each reference's last section; the shared part is `SvGolf/SeqV2.lean`):
* **Rule 2.** The v1 reductions already took, for the reset cycle, ANY state of the phase model's
  shape (`Shape`: the register widths, any values, `x` included), so their claim holds from any start
  state of the shape. Revision 2 makes that literal: the claim is proved over `RunFrom` (a run from
  any start), v1 is its instance at `initState2`, and v2 its instance at each power-up state.
  The only new obligation per reference is that every power-up state has the shape (`sh_powerUp`,
  `mm_powerUp`, `so_powerUp`: the declarations peeled one by one, `powerUp_cons`) and termination from
  every power-up (the existing cycle lemma under `TerminatesPU.of_invariant`). No cycle lemma, phase
  model or invariant changed.
* **Rule 1.** As in round 1: FF-only, `MooreOutDep.of_noComb`.
* **Rule 3.** `simp` over `xsafeB` at symbolic parameters, with the window facts the slices need
  (`Lib.rowMajor_window_le`, `rowMajor_le`): the counter in one call; matmul's control and PEs
  (`ctrl_xsafe`, `pe_xsafe`); the sorter's top cell, output register and cell family.

**MEASURED** (`check.py <task> <ref>.sv <ref>.lean --postsynth full`, each through the shared Lean
slot, this branch):

| reference | result | solution | comparator axioms | leanchecker | post-synthesis (concrete starts) | score (unchanged) |
|---|---|---|---|---|---|---|
| counter `cnt` | accepted, stage `done` | 3.75 s | `propext`, `Quot.sound`, `Classical.choice` | exit 0, 16.4 s | 0 mismatches at N=8 | 78.326 GE, 312.8 µm², 1789 ps, 8 flops |
| `matmul_g1` | accepted, stage `done` | 13.15 s | the same | exit 0, 19.3 s | 0 mismatches at (2,4,8) and (4,8,32) | 87173.6 µm², 4 × 10696 ps, 20783.15 GE, 802 flops |
| `sorter_ins` | accepted, stage `done` | 7.37 s | the same | exit 0, 20.3 s | 0 mismatches at (3,4) and (8,8) | 5512.8 µm², 16 × 2523 ps, 1288.82 GE, 81 flops |

matmul's first run failed at `solution` (`pe_xsafe`: `simp` left the sign-bit slices' condition
`i*N*W + W - 1 + 1 ≤ N*N*W`, which its facts did not match); fixed with the two facts in that form,
then accepted (the run above).

**Revision 3, re-run** (MEASURED, 2026-11-06, the committed state: rule 3's unsigned-index clause and
`fourstate`'s write exception; designs and proof files unchanged, none of the three has a dynamic
index, so their rule-3 `simp` calls never meet the new clause):

| reference | result | solution | comparator axioms | leanchecker | post-synthesis (concrete starts) | score (unchanged) |
|---|---|---|---|---|---|---|
| counter `cnt` | accepted, stage `done` | 2.25 s | `propext`, `Quot.sound`, `Classical.choice` | exit 0, 16.9 s | 0 mismatches at N=8 (zeros, seed:1, seed:2) | 78.326 GE, 312.8 µm², 1789 ps, 8 flops |
| `matmul_g1` | accepted, stage `done` | 8.53 s | the same | exit 0, 16.4 s | 0 mismatches at (2,4,8) and (4,8,32) | 87173.6 µm², 4 × 10696 ps, 20783.15 GE, 802 flops |
| `sorter_ins` | accepted, stage `done` | 5.42 s | the same | exit 0, 16.3 s | 0 mismatches at (3,4) and (8,8) | 5512.8 µm², 16 × 2523 ps, 1288.82 GE, 81 flops |

The heartbeat table below is revision 2's (the reference files are unchanged; not re-measured).

**The effort** (MEASURED; heartbeats in thousands, the unit of `maxHeartbeats`, from a heartbeat mark
before every declaration, synchronous elaboration against each check's staged `Submission.Design`;
round 1's numbers from its review, same method):

| reference | file lines v1 → round 1 → rev. 2 | v2 section lines | v2 section heartbeats (round 1) | of which every power-up (lines, heartbeats) | of which rule 3 (lines, heartbeats) | v1 part heartbeats |
|---|---|---|---|---|---|---|
| counter | 310 → 399 → 360 | 44 | 1192 | 15 lines; `sh_powerUp` 181, `cnt_terminatesPU` 102 | 4 lines; `cnt_xsafe` 529 | 11613 (with the instantiation) |
| matmul | 751 → 905 → 848 | 103 | 6777 (8863) | 27 lines; `mm_powerUp` 915, `mm_terminatesPU` 146 | 46 lines; `pe_xsafe` 2806, `ctrl_xsafe` 1826, `mm_xsafe` 133, `mm_pe_mem'` 99 | 143552 |
| sorter | 912 → 1051 → 979 | 76 | 5463 (5108) | 25 lines; `so_powerUp` 623, `so_terminatesPU` 378 | 21 lines; `so_xsafe` 3662 | 126968 |

So the every-power-up obligation costs each reference two short lemmas, about 0.3 to 1.1 million
heartbeats, under 1% of the proof; rule 3 is the larger part of the v2 section. No new
`set_option maxHeartbeats`. The library side: `SvGolf/Seq.lean` +110 lines net (`RunFrom` and the
split reductions), `SvGolf/SeqV2.lean` rewritten (248 lines), `SvGolf/XFree.lean` new (the x-free
lemma).

**`lake build`** (MEASURED, 141 jobs): every module this branch changes builds, among them `SvGolf`,
`tasks` (with both `Properties.lean`), `svgolf-eval`, `tests.seq_counter.negative.Refute` and
`.Table` (24 s). The build fails in `tests/{add,mul,clmul}/negative/Refute.lean`, which this branch does
not touch (section 7). Revision 3 (MEASURED): `lake build SvGolf tasks svgolf-eval
tests.seq_counter.Spec tests.seq_counter.negative.Refute tests.seq_counter.negative.Table`, 134
jobs, green, `Table` 30 s; every new theorem's axioms are `propext`, `Quot.sound` and, for the run
refutation `f16n1_refuted`, `Classical.choice`.

## 6. The post-synthesis stage: ls-sv from concrete starts

**What used the x-start run** (READ): the clocked post-synthesis check (`check/postsynth.py`,
`run_clocked`) ran the realized stimulus through `svgolf-eval --trace`, which ran `run2` from
`initState2` (all-`x` registers), and rejected any `x`/`z` in a cared output. Nothing else in the
checker uses it (the comb check runs one-cycle vectors from fresh starts with every input driven).

**The change.**
* `svgolf-eval --trace --start zeros|seed:<n>` (`check/SvEval.lean`): the run is `run2At` (the
  statement's own, imported from `SvGolf.TaskSeq`) from the power-up state with every bit 0, or with
  bits drawn from a 64-bit LCG seeded with `n` (declaration by declaration, bit by bit). Without
  `--start` it is `run2` as before. A `START` line records which.
* `run_clocked`, per seed: seed 0 starts the Verilator model with `randReset(0)` (every flop 0, the
  `--x-initial unique` start) and ls-sv from `zeros`; seeds 1 and 2 start the model with
  `randReset(2)` and its seeded random state, and ls-sv from `seed:<seed>`. The netlist's flops are not
  named after the registers, so the random starts are not the same state, and neither, in general,
  is seed 0 (revision 2 called it the same state, which is wrong): the netlist has only the flops
  Yosys keeps, and Yosys replaces an uninitialized flop whose next value is always one constant or
  its own value by that constant, which fixes that register's power-up to the constant (MEASURED on
  the attack's `f1_nested_width.sv`: the netlist keeps one flop of 21, `q[3]`, 6 GE; `a`, `b`
  and `y` became constants, so the netlist's "zero" start has `y = 8`, and its one mismatch with
  ls-sv from zeros is at cycle 2, where `q` shows `y`'s power-up value; DERIVED: Yosys's `opt_dff`).
  An uninitialized flop whose next value is ONLY its own value (`u <= u`) is not replaced by a
  constant: `opt_dff` removes its D path ("Handling D = Q … (removing D path)", MEASURED), its
  output becomes an undefined value, and Yosys resolves each use of it separately (section 10,
  finding A).
  Under rule 2 the cared outputs must agree whatever the two power-ups are, so a mismatch there
  means a cared output depends on the power-up, which rule 2 refuses, or that the netlist is not
  ls-sv's design for any power-up (section 10, finding A); the post-synthesis rejection
  message ("the netlist (…) is not ls-sv (…)") then names the symptom, not a disagreement from one
  state. Each seed's record carries `netlist_randreset`
  and `lssv_start`. The `x`/`z` rejection of a cared output stays (with rule 3 it cannot fire on a
  proved design; it still catches a design outside rule 3 that slips through).

**MEASURED** (`run_clocked` directly, full mode, `N = 8`, the counter's oracle, gate, extraction and
the clocked score flow as in `check.py`):

| design | before (ls-sv from `initState2`) | after (concrete starts) |
|---|---|---|
| `cnt.sv` (reference) | accepted | accepted, 0 mismatches |
| fixture 0 `u ^ u` | **REJECTED**: 921 failures, "ls-sv: q is x/z in a cared position" | **accepted**, 0 mismatches |
| fixture 5 | accepted | accepted |
| fixture 7 (`bit u`), W1, W3 | accepted | accepted |

The last row is the sampled nature of obligation C, not a hole in v2: the three power-ups draw `u = 0`
for fixture 7 (MEASURED: bits of the generator at seeds 0 to 2), W1's saturation needs `q = 255`
(the stimulus reaches 143, as in round 1), W3's trigger is 2^-8 per run. v2's statement rejects all
three (rule 2, kernel theorems).

**Obligation C stays sampled.** v2 closes the mechanisms found (the probe's H1 and F1, round 1's W1,
W2, W3, the 2-state power-up, the x-pessimism over-rejection); it does not close the whole gap between
ls-sv's semantics and the scored netlist. Every known reference bit equal to the netlist's on every
trace is still checked only on the post-synthesis stimulus (three power-ups, the oracle's
transactions), and W4 waits for ls-sv.

## 7. Dependencies, and what v2 does not close

* **W4 (ls-sv).** A `unique`/`priority` case is validated on the snapshots, not where it executes
  (section 4, fixture 11). v2 depends on ls-sv's fix; until then the source gate refuses the
  qualifiers.
* **W5 (ls-sv), new in revision 3: a signed dynamic index is read as unsigned.** `evalExpr2`'s
  `.index` arm and `resolveLhs2`'s `.index` arm take the index's `toNat?` (READ,
  `LeanModels/Sv/Sem2.lean`), so a signed index whose value is negative selects a bit IEEE 1800
  calls out of range (§11.5.1: a read is `x`, a write has no effect), and the lowering drops a
  `$signed(…)` cast in value position (`instExpr2`'s `.cast` arm, `LeanModels/Sv/Param2.lean`, READ).
  MEASURED (fixtures 12, 13, 15 and the attack's `a1`, `c1`, `s2`, `s9`): ls-sv counts where Icarus
  and the Yosys netlist hold `q`. A defined-value deviation of ls-sv from the standard, to be
  reported to the ls-sv lane: the fix is to keep the index's signedness in `Expr2.index`/`Lhs2.index`
  (or refuse a signed dynamic index loudly at ingestion, AGENTS rule 3). Until then rule 3 refuses a
  dynamic index that mentions a signal declared signed, which covers what the loaded design shows
  (fixtures 12, 13), and the `fourstate` stage (rule (d), slang's own types) refuses every signed
  index, the cast included (fixture 15, MEASURED); the statement alone does not refuse fixture 15.
  The cast is not the only signedness the loaded design loses: an index whose `?:` arms are signed
  literals (`m[en ? 2'sb11 : 2'sb01]`, signed by §11.8.1 with no signed signal and no cast) loads as
  `m[en ? 2'b11 : 2'b01]` and passes rule 3, and ls-sv counts where Icarus and the netlist hold `q`
  (section 10, finding C, MEASURED); `fourstate` (d) refuses it.
* **`fourstate` (e) for undriven variables** (section 10, finding B). Rule 2 reads a variable no
  process writes as a power-up value that never changes; Yosys reads it as undefined and resolves
  it freely (MEASURED: a counter that compares a reset copy of an undriven `u` with `u` passes rules
  1 to 3 and its netlist holds `q` at 0). Only `fourstate`'s undriven-net check refuses it. It is
  also the never-loaded rule's dependency (section 11): a register bit no write reaches gets no
  flop at all, so the flow's log shows no removal; the bit is undriven, and only this check
  refuses it (`tests/seq_counter/never_loaded/partial.sv`, MEASURED).
* **Obligation C (sampled).** Section 6. v2 closes the mechanisms found, not the whole `x` gap: a Yosys
  or ls-sv disagreement on DEFINED values is still found only where the post-synthesis stimulus
  reaches it (and, by the maintainers' ruling, is then a construct svGolf disallows, not an ls-sv change).
* **Asynchronous resets** (round 1, unchanged): rule 1 does not see a path through an asynchronous
  reset event; the clocked gate refuses asynchronous resets.
* **Rule 3 is structural, not semantic.** It refuses some designs whose `x`-creating construct can
  never fire (a divisor that is a nonzero signal by an invariant; an index kept in range by an
  invariant). Such a design must make the bound structural (a power-of-two vector, a constant
  divisor). A semantic rule 3 (an invariant proving the divisor nonzero) would admit more and needs a
  proof per design; not drafted (JUDGED: structural is what a gate can check). Two more
  over-rejections, recorded (revision 3, MEASURED): an index that mentions a signed signal but that
  IEEE 1800 types as unsigned (`a[i + u]`, `i` signed, `u` unsigned: `xsafeB` false, `fourstate`
  passes; a narrower rule would compute the standard's expression signedness, §11.8.1, on the
  loaded tree, whose literals no longer carry it: not drafted); and an indexed part select whose
  base is scaled by an unsized constant (`data[i*2 +: 2]`, the attack's finding 5: the unsized `2`
  makes the base 32 bits wide, ls-sv's lowering pads the window with `x` literals, and both rule 3
  and `fourstate` refuse it; a narrower rule needs a value-range analysis of the index, not
  drafted). The packed-array form `logic [3:0][1:0] data; data[i]` is accepted by both (MEASURED).
* **Not wired into a gate** (superseded 2026-11-06: a Python twin refuses before the proof, section
  11.5). `xsafeB` is a Lean function of the loaded design; the checker evaluates it
  only through the proof (the conjunct). A pre-proof refusal would need `check.py` to evaluate it at
  the probe points, or a Python twin in `score/fourstate.py`. Not done (the maintainers' question 4); the
  banlists of the three tasks are still empty, so a run-time `/` in a clocked submission is refused
  only at the proof (the attack's finding 4, MEASURED: `q <= d / {7'b0, en}` passes the gate and
  `fourstate`, and `xsafeB` is false). `fourstate`'s docstring said every task bans run-time `/` and
  `%`; aes_sbox, clmul and the clocked tasks do not (MEASURED, `task.json`), and the docstring now
  says so. Where `fourstate` and rule 3 overlap they now agree on the attack's cases: both refuse a
  signed index and an index whose type leaves a read's range, both admit an unsigned write index
  past the top of the range (revision 3's write exception, fixture 14); `fourstate` is stricter on a
  `$signed` cast (W5), rule 3 on a mixed-sign index (above).
* **The comb negatives' build failure (not this branch's).** Revision 2's measurement; revision 3
  built only the targets it touches (`SvGolf`, `tasks`, `svgolf-eval`, `tests.seq_counter.Spec`,
  `.negative.Refute`, `.negative.Table`: green, MEASURED) and did not rerun the full build (nothing
  under `LeanModels/` changed since, READ: the merges since revision 2 touched `svgolf/` only).
  `lake build` of this branch fails in
  `tests/{add,mul,clmul}/negative/Refute.lean`: `load_design_sv2` refuses their `only_n16.sv` at the
  defaults (`PDesign.int32Agrees`). MEASURED on this branch after merging `svgolf-prep` (which merged
  lean-surfaces `master` and its ls-sv changes since round 1's green build); DERIVED not this
  branch's: none of the three imports a file this branch changes (they import `SvGolf.Comb`,
  `SvGolf.LoadSv`, their task's `Spec`). For `svgolf-prep`.
* **Two checker tests changed their expected message** (MEASURED: `tests/checker/test_clocked_post.py`,
  5 tests, OK, through the Lean slot). `tests/seq_tx/x_cared.sv` (C never cleared) and the sorter
  mutant whose tokens are not reset were rejected at post-synthesis with "is x/z in a cared position"
  (ls-sv's x start). From concrete starts they are still rejected, with "the payload is not the task's
  result" and "out_valid: the netlist (0) is not ls-sv (1)" (the netlist's and ls-sv's power-ups
  differ, and the mutant's outputs depend on it).
* **Not run:** `tests/run.py` (the attacks, negatives and baselines of every task) on this revision.
  In its place for the `fourstate` change (MEASURED): `score/fourstate.py --selftest` passes (29
  rows, two new), and every design `tests/expected.json` expects `fourstate` to refuse (17: the
  `_example` negatives and attacks, add, aes_sbox, the five clmul attacks whose expected message is
  "run-time index") is still refused, with that message where one is expected.

## 8. For the maintainers

Each question carries its decision of 2026-11-06 (section 11 records what implementing them
changed).

1. **Known stimuli.** Rule 2 quantifies over power-up states AND over stimuli whose bound inputs are
   known values of their declared widths (`KnownStim`), on the reading that an `x` on an input is an
   unknown 0/1 value whose resolutions are known entries. v1 quantified over every stimulus, `x`
   inputs and wrong widths included. Keep the restriction (it is what makes every run of the
   statement concrete), or also require the claims on `x` inputs (a simulator's resolution again)?
   **Decided 2026-11-06: stimuli stay known-input.** An input is a 0/1 wire, so every 0/1 sequence
   covers every resolution of an unknown input.
2. **Fixture 9.** Decided as REJECT by rule 3 (an `x` literal is admitted only as a `casez`/`casex`
   pattern, the gate's own line). The alternative is to admit `x`/`z` literals as operands of `===`,
   `!==` and as case items, where the result is always a known bit: `s === 1'bx` would then be 0 in
   every run and the fixture would be accepted. Confirm.
   **Decided 2026-11-06: fixture 9 stays rejected.** It observes a simulator value no hardware has.
3. **Rule 3 is structural.** Divisors must be literal nonzero constants and dynamic reads in range by
   their index's width; a design that keeps them safe by an invariant must restate the bound
   structurally. Confirm, or ask for a semantic variant (a proof obligation per construct).
   **Decided 2026-11-06: rule 3 stays structural.** A cheap sufficient condition (AGENTS.md rule 4).
4. **Gating rule 3 before the proof** (section 7): add a `fourstate`/banlist twin of `xsafeB` (cheap
   refusals for players), or leave it to the proof conjunct.
   **Decided 2026-11-06: yes.** A Python twin of `xsafeB` refuses before the proof with a clear
   message; the Lean rule stays the authority (section 11.5: `check/clocked_rules.py`).
5. **The x-start run is gone from the statement.** v2 keeps neither `Terminates2` nor v1's `Follows`
   from `initState2`: a design that is correct from every power-up but not from the x start (fixture
   0) is accepted. Confirm that nothing should still require the x-start run.
   Not decided separately; the rulings of 2026-11-06 restate rule 2 as "the claims hold from EVERY
   0/1 power-up (2-state included) on every known-input stimulus", with no x-start run.
6. **`matmul` and `sorter` state v2 on this branch** (as in round 1): keep, or revert the two
   `Spec.lean` lines until the rules are settled.
   **Decided 2026-11-06: matmul and sorter state v2.** They stay unranked previews.
7. **Signed indices (revision 3).** Rule 3 refuses a dynamic index that mentions a signal declared
   signed; the `$signed` cast is ls-sv's W5. Keep the structural clause (simple, over-rejects a
   mixed-sign index), or ask for the standard's signedness computation on the loaded tree?
   **Decided 2026-11-06: the structural clause stays until ls-sv's W5 fix (signedness through
   ingestion) lands; then it is removed.** Until then it covers what the loaded design shows.
8. **`fourstate`'s write exception (revision 3).** The stage now admits an unsigned write index past
   the top of a packed vector's range (the write has no effect; IEEE 1800, ls-sv and Yosys agree,
   MEASURED on fixture 14 and the attack's `c3`), so it agrees with rule 3. It changes a stage every
   task runs (only ever admitting more). Keep, or revert and make rule 3 refuse such writes too?
   **Decided 2026-11-06: the exception stays.** IEEE 1800 ignores such a write.
9. **Registers that only hold their value (section 10, finding A).** Rule 2 admits a decision on an
   unreset register whose value is proved not to matter. The pinned flow does not keep a register
   whose next value is only its own (`u <= u`): it removes it and resolves each use of the
   undefined value separately, so such a design can pass every stage with a netlist that is wrong
   on a rare input. By the ruling that svGolf disallows what the pinned flow does not implement,
   which rule: a structural refusal of a register whose every write is its own value, a refusal
   of any design whose synthesis removes a flop without an initial value by `D = Q`, or a reset on
   every register a decision reads?
   **Decided 2026-11-06: never-loaded registers are refused in every clocked task.** The pinned
   Yosys removes a flop whose next value is always its own and resolves each read of the undefined
   value separately, which breaks the one-power-up-value-per-register correlation the semantics
   has: the svGolf-side disallowance of a Yosys deviation (section 11).

## 9. The attack on revision 2 (2026-11-06), and what revision 3 does

The attack built 22 fixtures on the counter's interface, compared ls-sv from the zero power-up
(`svgolf-eval --trace --start zeros`) with the Yosys netlist from Verilator's zero start
(`randReset 0`), took Icarus on the source as the standard's reference, and ranked five findings.
Each, re-measured on this branch (fixtures and notes in the session scratchpad):

| # | finding (the attack's severity) | verdict | revision 3 |
|---|---|---|---|
| 1 | ls-sv drops the context width through `>>` and `\|` (HIGH) | NOT CONFIRMED: ls-sv computes the context width; the one mismatch is a power-up, which rule 2 covers | fixture 16 (kernel, both `N = 2` and `N = 1`); two claims of this file corrected (sections 3, 6) |
| 2 | rule 3 admits a signed dynamic index (MEDIUM) | CONFIRMED, and a deviation of ls-sv from IEEE 1800 on defined values (W5) | rule 3 asks for an unsigned index; fixtures 12, 13 rejected (kernel); fixture 15 (`$signed` cast) depends on W5 |
| 3 | rule 3 admits an out-of-range write, `fourstate` refuses it (MEDIUM) | CONFIRMED, an over-rejection by `fourstate` | `fourstate`'s write exception; fixture 14 accepted (rules 1, 3 kernel) |
| 4 | run-time `/`, `%` in a clocked task refused only by rule 3 (LOW) | CONFIRMED, not a wrong acceptance | recorded (the maintainers' question 4); `fourstate`'s docstring corrected |
| 5 | `data[i*2 +: 2]` over-rejected by rule 3 and `fourstate` (LOW) | CONFIRMED | recorded (section 7), with the packed-array form both accept |

**Finding 1, not confirmed.** The attack's `f1_nested_width.sv`: `y <= (a + b) >> 1` with `y` 5 bits,
`a = b = 4'd8` at reset, `y` never reset, `q <= {3'b0, y}`; reported "ls-sv `q = 0`, netlist `q = 8`".
* ls-sv computes `a + b` at 5 bits (READ: the envelope gives `Binary width=5 op=+` over `Resize 5`
  operands, and `instExpr2`'s shift arm extends its left operand to the context; MEASURED:
  `svgolf-eval` shows `q = 8` for `f1` and `q = 16` for `f2_ctx_or.sv` from the third cycle on).
* The attack's driver found one mismatch, at cycle 2, the cycle where `q` shows `y`'s power-up value.
  ls-sv's zero start has `y = 0`; the netlist has no `y` flop: it keeps one flop of 21 (`q[3]`,
  6 GE), Yosys having replaced `a`, `b` and `y` by the constants they are only ever given (MEASURED,
  the netlist). Its "zero" start is a power-up with `y = 8`, not the zero one (section 6).
* With `y` reset and `a`, `b` moving (`a + 3`, `b + en` each cycle, so the sum's fifth bit is set on
  most cycles: `q = 17, 21, 25, …`): ls-sv equals Icarus on all 13 cycles run and the netlist on all
  29 (0 mismatches), for both `>>` and `|` (MEASURED).
* Fixture 16 states the context width in the table: `q + ((a + b) >> 1)` with 1-bit `a = b = 1` is
  the counter at `N = 2` (accepted: rules 1, 3 and rule 2 on every power-up, kernel) and holds `q` at
  `N = 1` (kernel refutation), as Icarus does.
* What the finding does show is two overclaims of revision 2, corrected: "rules 2 and 3 together
  give the claims for every power-up the hardware can have" (section 3: they give them in ls-sv's
  semantics; the hardware link is ls-sv's faithfulness and obligation C), and "seed 0 starts the
  netlist and ls-sv in the same state" (section 6). The attack's general point stands: no v2 rule
  shows ls-sv faithful to the standard on defined values, and finding 2 is a case where it is not.

**Finding 2, confirmed: W5.** ls-sv reads every dynamic index unsigned and drops `$signed` casts
(section 7). MEASURED: Icarus and the netlist hold `q` at 0 on fixtures 12, 13 and 15, ls-sv counts.
Revision 2's rules accepted fixtures 12 and 13 (`xsafeB` true, `mooreOutDepB` true, `boundedPU`
true on the loaded designs) and the attack's `a1`, `c1`. Revision 3's rule 3 refuses fixtures 12, 13
and the attack's `a1`, `c1`, `s5` (`a[i + j]`, both signed) and `s8` (`a[en ? i : j]`), and admits
the cast forms (fixture 15, the attack's `s2` read and `s9` write), whose loaded designs show no
signed signal: those wait for W5, and `fourstate` refuses them meanwhile (MEASURED). The probes
`logic [0:3] m; m[i]` (an ascending range) and `logic [7:4] m; m[i + 3'd4]` (a nonzero lsb label),
added this round, load with an `unsupported` node in ls-sv (MEASURED): loud, not a hole.

**Finding 3, confirmed: an over-rejection by `fourstate`, fixed there.** The attack's `c3`
(`q[idx] <= 1`, a 4-bit `idx` into the 8-bit `q`) and fixture 14 are correct designs: an
out-of-range write has no effect in the standard (IEEE 1800-2023 §11.5.1: a part select "completely
out of the address bounds … shall have no effect on the data stored when written", quoted in
`docs/sv-xcelium-audit.md`, READ; a bit select is its one-bit case, DERIVED; Icarus agrees,
MEASURED), in ls-sv (`resolveLhs2`, READ) and in the netlist (MEASURED: 0
mismatches on both; Icarus agrees). Rule 3 admits them and always did (it does not check a write
index's range); `fourstate`'s rule (d) refused them with a read's reason. Rule (d) now admits a
write through a bit/element select of a packed vector whose unsigned index can only pass the top
of the range; a signed write index stays refused (its own message: the standard reads it as
negative, ls-sv as unsigned); a part-select write keeps the old rule (ls-sv has no run-time-base
part-select write: it refuses one loudly, `arrayPartTarget`, READ); a select inside a written
target's index is still a read (selftest `oob_signed_write.sv`). The other direction (rule 3 refusing
such writes to match the old `fourstate`) would have refused correct designs for no semantic reason.

**Finding 4, confirmed, recorded.** `q <= d / {7'b0, en}` passes the gate and `fourstate`, and rule 3
refuses it (`xsafeB` false, the attack's measurement): rule 3 does its job and is the only guard
before the proof conjunct. A gate twin is the maintainers' question 4. Outside v2's scope but observed
while correcting `fourstate`'s docstring: aes_sbox and clmul (comb tasks) admit run-time `/` and `%`
too, with no `fourstate` rule for a zero divisor; whether their statements can be proved for a
design that divides by a zero signal was not measured.

**Finding 5, confirmed, recorded.** The counter form (`if (en && data[i*2 +: 2] == 2'b01)`, `i` 2
bits): rule 3 refuses it (the loaded tree pads the window with `x` literals and computes the base
in 34 bits, READ from the print) and so does `fourstate` (a 32-bit base). `logic [3:0][1:0] data;
data[i]` is accepted by both, and ls-sv, Icarus and the netlist agree on it (MEASURED).

**What did not change.** The attack's defence-in-depth list (multiple drivers, undriven and partial
registers, out-of-range part selects, wildcard patterns, signed comparison, division and mixed-sign
arithmetic, `casez`, and the benign unreset register overwritten before use) holds as it reported;
no fixture of it is in the table.

## 10. Independent review of revision 3 (2026-11-06)

A reviewer who wrote none of revisions 1 to 3 re-checked revision 3 against the maintainers' decisions of
2026-11-05. Fixtures, probes and logs are in the session scratchpad (`txv2r2/review4/`), not on the
branch. `git merge svgolf-prep`: already up to date.

**Re-measured, holds.**
* Full `lake build` (141 jobs) fails only in `tests/{add,mul,clmul}/negative/Refute.lean`
  (`PDesign.int32Agrees`), as section 7 says. Every module this branch changes is up to date, and
  its replayed `#print axioms` lines (`xfree_*`, the `SeqV2` lemmas, every theorem `Refute.lean` and
  `Table.lean` print) name `propext`, `Classical.choice`, `Quot.sound` or fewer (MEASURED).
* `check.py <task> <ref>.sv <ref>.lean --postsynth full`, the three references: accepted, stage
  `done`, comparator axioms `propext`, `Quot.sound`, `Classical.choice`, 0 post-synthesis mismatches
  at every point under the starts `zeros`, `seed:1`, `seed:2`, and section 5's scores (MEASURED).
  The reference designs are unchanged since `svgolf-prep` (READ, `git diff`).
* The acceptance table, a sample re-run (MEASURED): `f7_refuted` and `f6_refuted` re-elaborated
  as new theorems, `¬ XSafe f12`, `XSafe f0`, `XSafe f14` and `puRun f5 1 stimA` by `decide
  +kernel`; `xsafeB` and `mooreOutDepB` on fixtures 0 to 16 give the table's verdicts; `boundedPU`
  widened to every 4-entry stimulus holds for fixtures 0, 1, 5, 10b, 14; the hand-built twins of
  fixtures 2, 7, 8, 12, 15 equal the loaded `.sv` files (`reprStr`); 26 theorems of the two files
  whose axioms the files do not print use the three or fewer.
* Rule 2 (READ): `FollowsPU` and `TerminatesPU` of all three kinds quantify over every `PowerUp`
  state (every declaration, 2-state ones included, any 0/1 value of its width) and every known
  stimulus, and v1's claims are restated word for word; `SatisfiedAtV2` has no conjunct over
  `initState2`; the one caller of `svgolf-eval --trace` (`clocked_seed`) always passes `--start`.
* Rule 3 (READ): every `x`/`z` source of `evalExpr2`, `evalBinOp`, the `LVec` operators,
  `execStmt2`, `resolveLhs2`, `writeConcatLhs2`, `commitNba2`, `applyInputs2` and the cycle is a row
  of section 2's table, and `xfree_*` proves the coverage (no `sorry`, no axiom of its own).
* Nothing in the v2 statement reads the netlist or a Yosys operator (READ: `SvGolf/TaskSeq.lean`
  imports `SvGolf.Task`; Yosys appears only in docstrings).

**Finding A: a register that only holds its value, decided both ways, is accepted with a wrong
netlist.** The fixture `ux4_200.sv`, on the counter's interface:

```systemverilog
logic u, inc;
always_ff @(posedge clk) u <= u;
always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
always_ff @(posedge clk) begin
  if (rst)     q <= '0;
  else if (en) q <= q + inc;
end
```

`inc` is 1 for `u = 0` and for `u = 1`, so from every power-up the design is the counter.
* The statement (MEASURED, interpreted on the loaded design): rules 1 and 3 hold at `N = 8`
  (`mooreOutDepB`, `xsafeB`); at `N = 8`, from `u = 0` and from `u = 1`, reset and 210 counts show
  the counter (the claim can depend on nothing else: `q` is reset, `inc` settles, every entry binds
  `rst` and `en`, DERIVED). Its twin with the guard `q == 3` passes `boundedPU` at `N = 2` and the
  every-power-up run of reset and six counts. No proof was written: the design is the counter for
  each value of `u` (DERIVED), so a proof along `cnt.lean`'s lines with a case split on `u` should
  exist (DERIVED, not attempted).
* v1 rejected the construct: from the x start `inc` is `x` at the guard (MEASURED: the `q == 3`
  twin's run from `initState2` fails the claim, and `boundedInit` is false for `ux2.sv`). Rule 2 is
  what admits it.
* Every stage but the proof passes (MEASURED, `check.py --unproved --postsynth full`): the gate,
  `fourstate`, the design, the score (86.991 GE, 351.59 µm²) and the post-synthesis check (321
  cycles from each of three power-ups, 0 mismatches).
* The scored netlist holds `q` at 200 where ls-sv and the counter go on to 201 (MEASURED: ls-sv
  from `zeros` against Verilator from `randReset(0)`, reset and 210 counts, every cycle from 202
  differs). The `q == 3` twin is rejected at post-synthesis (1618 failures); `ux2.sv` (`q + (u ? 1 :
  0) + (u ? 0 : 1)`) and `ux3.sv` (two `if (u)` in an `always_comb`) give 0 GE netlists that hold
  `q` at 0.
* Mechanism (MEASURED, the Yosys log): `opt_dff` reports "Handling D = Q on `$procdff…` (removing D
  path)" for `u`; the flop is gone, its output is undefined, and the uses of `u` are resolved
  separately, so that `inc` is 0 at the guard, which no value of `u` gives. Rule 2 takes an unreset
  register to hold ONE unknown 0/1 value; the pinned flow keeps that for a register it keeps, not
  for one whose next value is only its own. Fixture 0 (`u ^ u`) is the same construct and agrees
  with its netlist because Yosys folds `u ^ u` before it resolves anything (DERIVED).
* So v2 admits a mechanism v1 refused, and only the sampled obligation C stands in front of it,
  which the rare guard passes. The options are the maintainers' question 9 (none drafted here).

**Finding B: an undriven variable is read as a constant.** `ud.sv`: `logic u` with no driver,
`p <= u` at reset, `else if (p != u) q <= '0`. Rules 1 to 3 accept it (MEASURED: `xsafeB`,
`mooreOutDepB`, `boundedPU` at `N = 1`, `puRun`); the netlist holds `q` at 0 (15 of 29 cycles
differ, MEASURED); `fourstate` (e) refuses it ("Wire cnt.\u is used but has no driver", MEASURED).
Rule 2 reads a variable no process writes as a power-up value that never changes, Yosys as
undefined. Closed by `fourstate` only, now a listed dependency (section 7). JUDGED: the statement
could refuse it itself (every signal read is an input or written by some process).

**Finding C: W5 is wider than the `$signed` cast.** `sl.sv`: `m[en ? 2'sb11 : 2'sb01]` (signed by
§11.8.1: both arms are signed; no signed signal, no cast). It loads as `m[en ? 2'b11 : 2'b01]`,
passes rules 1 to 3 (`boundedPU` included), and ls-sv counts, while Icarus 12 and the netlist hold
`q` at 0 (the index is -1; 16 of 29 cycles differ from the netlist) (MEASURED). `fourstate` (d)
refuses it (MEASURED). The variant `m[2'sb11 >>> en]` loads with an `unsupported` node (loud). The
fix is W5's: keep slang's signedness of the index in `Expr2.index`/`Lhs2.index`. Section 7 now says
so; the rule-3 docstring in `SvGolf/TaskSeq.lean` still names only the cast (trusted text, not
changed by this review).

**Finding D, wording (fixed here, docs only).** Section 6 said Yosys replaces a flop whose next
value is its own by a constant (finding A: it removes it); the coverage table said an `x` digit of
a `casez` item is a wildcard (it is not; ls-sv and IEEE 1800 §12.5.1 match it against no known bit,
and the gate refuses it: `czx.sv` is refused by `load_sv`, MEASURED). `SvGolf/XFree.lean`'s module
docstring said rules 2 and 3 make every run "a run of the hardware's 0/1 semantics", the overclaim
section 3 corrected; reworded. The same `casez` wording is in `TaskSeq.lean` (the rule-3 docstring
and `patOK`'s), not changed (trusted text).

**Finding E, not done.** W5 is not yet reported to the ls-sv lane (READ: the session has W4's
message, not W5's); the "revision 2" labels of `TaskSeq.lean`'s v2 section and the three
`Spec.lean` docstrings predate revision 3; `tests/run.py` was not run by this review either.

## 11. The decisions of 2026-11-06, implemented

Section 8 records each decision with its reason. This section records what implementing them
changed: the never-loaded-register rule (11.1 to 11.4), rule 3's Python twin (11.5), the trusted
text (11.6) and the dependencies (11.7); 11.8 is the test record. Fixtures are on the branch:
`tests/seq_counter/never_loaded/` and `tests/seq_counter/xsafe/` (the second a copy of the `.sv`
files of sections 4, 9 and 10, which were in the session scratchpad until now).

### 11.1 The rule: never-loaded registers are refused in every clocked task

The ruling (decided 2026-11-06): the pinned Yosys removes a flop whose next value is always its own
(`opt_dff`: "Handling D = Q ... (removing D path)", and the never-active-enable case) and then
resolves each READ of the now undefined value separately, which breaks the
one-power-up-value-per-register correlation the semantics has (finding A, `ux4_200.sv`: correct
both ways in ls-sv, wrong netlist). svGolf disallows the design, as it disallows every Yosys
deviation from the semantics. The same mechanism is the async FIFO's MG-1; an undriven variable
(finding B) is its combinational analogue, which `fourstate` (e) refuses (11.7).

How the checker applies it, to every clocked kind (`CLOCKED_KINDS`: seq, tx, stream here; the
`react-family` kind of branch `svgolf-react` is in that branch's `CLOCKED_KINDS` and scores through
the same `score_clocked`, so it inherits both checks at the merge, READ; its arbiter reference
`rr_mask.sv` logs no removal at the scoring point or any postsynth point and passes the twins,
MEASURED):

* **The authority is the pinned flow's own report.** The clocked score record gains
  `flop_removals` (`score/score.py`, `flop_removals`), read off the synthesis log of the scored run
  (the log was written before and discarded; nothing in the scored script changes). `check.py`
  `never_loaded` refuses at the `score` stage, at the scoring point and at every postsynth point it
  synthesizes, when the log shows a removal that leaves reads undefined (11.2). The message names
  the register, quotes the log line and states the rule: "never-loaded register at N=8: `u`. The
  pinned Yosys removes the flip-flop (its log: `Handling D = Q on _21_ ($dff) from module cnt
  (removing D path).`) and resolves each read of its now undefined value separately, while ls-sv
  gives a register one power-up value for every read, so the proved and the scored circuits
  differ. Rule (txtask-v2, decided 2026-11-06): in every clocked task, a design is refused where the
  pinned flow removes a flip-flop while reads of it remain (its next value is always its own, its
  enable is never active, or the only value it is loaded with is undefined), or connects the reads of
  an array lane no write loads to an undefined value; reset it, load it with a value other than its
  own, or remove it." (Reworded on 2026-11-06, section 12.2, L3: the rule's sentence said that every
  register must be loaded, which is wider than what the check refuses.)
* **Names.** The canonical flow numbers every non-port wire and cell, so the scored log names a
  cell (`_21_`, or `$auto$ff.cc:266:slice$142` for a flop an earlier pass split). A DIAGNOSTIC run
  (`score.undefined_registers`, never scored) repeats the two-stage flow with `canon.ys`'s two
  `rename` lines dropped; its netlist keeps the design's names and assigns `x` to exactly the
  registers left undefined (`assign u = 1'hx;`, MEASURED on every refused fixture). It runs only
  when the scored log shows a removal or an ambiguous constant (below).
* **An early message, not a refusal.** `check/clocked_rules.py` (stage `clocked_rules`, before
  any Lean stage) warns about a register every write of which is its own value (`u <= u`), one
  `warnings` line. It cannot refuse: where every read folds away before the flow looks at the flop,
  the flow removes the flop as unread and the netlist is the design's. The acceptance table's
  ACCEPTED fixtures 0 (`u ^ u`) and 1 (`t = u; t = 0`) are such designs (MEASURED: their logs show
  no removal; accepted with the warning, as `never_loaded/ok_hold_folded.sv` is).

### 11.2 The inventory: every pass of the scored script that removes a flop or undefines its output

READ off Yosys 0.53 (`53c22ab7c0ced80861c7536c5dae682c30fb5834`, the pinned build's sha) for the
passes `score/canon.ys` and `score/svgolf_seq.ys` run (`proc`; `synth -flatten`: `opt_expr`,
`opt_clean`, `opt -nodffe -nosdff`, `fsm` (until 2026-11-06: the flow now runs `synth -nofsm`, section
12.2), `opt`, `wreduce`, `peepopt`, `alumacc`, `share`,
`memory -nomap`, `opt -fast -full`, `memory_map`, `opt -full`, `techmap`, `opt -fast`,
`abc -fast`; then `dfflegalize`, `abc`, `opt_clean`). After a D-path removal no clock, enable or
reset is left, and `FfData::emit` "turns [the flop] into a const driver" of its initial value
(`kernel/ff.cc:545`), which is `x` without one (contract C1: none). Verdicts: **REFUSED** (breaks
the correlation), **KEPT** (one value for every read), **n/a** (no flop removed, or refused earlier).

| pass: message or condition | what happens to the flop and its reads | verdict | fixture (MEASURED) |
|---|---|---|---|
| `opt_dff`: "Handling D = Q on C (T) from module M (removing D path)." (`opt_dff.cc:567`; D = Q and no sync reset) | flop gone, Q driven by `x`; each read resolved separately | **REFUSED** | `hold.sv` (finding A's `ux4_200`), `hold_if.sv` (`if (en) u <= u`), `never_true.sv` (loaded only when `q == 300`, which Yosys folds); table fixtures 2, 7, 8, the probe's H1 twins, the review's `ux*` |
| `opt_dff`: "Handling never-active EN on C (T) ... (removing D path)." (`:495`; no sync reset) | as above | **REFUSED** | `never_active_en.sv` (enable `q - q != 0`, constant only after `abc -fast`) |
| `opt_dff`: "Handling const CLK on C (T) ... (removing D path)." (`:519`) | as above | **REFUSED** | none: the clocked gate admits only `always_ff @(posedge clk)` on the task's clock port |
| `opt_dff` `run_constbits`: "Setting constant V-bit at position I on C (T) ..." (`:820`; D a constant, every reset value equal to it or undefined, no initial value) | Q driven by that constant for every read: a power-up the semantics has | **KEPT** for 0 and 1; **REFUSED** for `x` | `ok_const0.sv`, `ok_const1.sv`, `ok_reset_hold.sv`; `x`: `never_active_en.sv`'s `a`, `b` (copies of the removed `u`). The message prints `val ? 1 : 0` over `State::Sx` (= 2), so an `x` reads "1-bit" (READ); the names-kept run decides (an `x`-assigned register) |
| `opt_dff`: "Handling D = Q ... (conecting SRST instead)" (`:537`), "Handling never-active EN ... (connecting SRST instead)" (`:486`) | flop kept, loaded only by its reset | KEPT (not a removal) | (`ok_reset_hold.sv` goes through `Adding EN` and then the constant row) |
| `opt_dff`: "Adding SRST/EN signal", "Removing never-active SRST/ARST/CLR/SET/async load", "Removing always-active EN", "Handling always-active SRST/ARST/CLR/SET/async load", "Converting CLR/SET to ARST", "Changing const-value async load", "Handling AD = Q", a zero-width flop (`:274`) | flop kept, or replaced by a defined value (its reset value, a function of its asynchronous inputs); asynchronous controls and latches are refused before (clocked gate; `fourstate` (e)) | n/a | every reference logs only "Adding SRST/EN" |
| `opt_dff -sat` | not in the flow (`synth` passes no `-sat`) | n/a | |
| `opt_merge`: cells of one type, parameters, inputs and initial value merged ("Removed a total of N cells."; per cell only at debug level) | two registers share one flop: their power-ups become equal, an admissible power-up; each read reads one value | **KEPT** | `ok_merge.sv` |
| `opt_clean`: a flop no one reads removed ("Removed N unused cells") | nothing reads it | **KEPT** | `ok_unused.sv`, `ok_hold_folded.sv`, table fixtures 0 and 1 |
| `wreduce` (`run_cell_dff`): "Removed top N bits (of M) from FF cell M.C (T)." / "Removed cell M.C (T)." | a bit with D constant 0 (initial and reset value 0 or undefined): Q := 0; a bit whose D equals the next lower bit's (initial and reset values equal): Q := that bit's Q; a bit no one reads: removed. One value per bit in each case | **KEPT** | `ok_signext.sv` (`w <= {en, en}`); the zero case is the constant row's (`opt_dff` runs first) |
| `dfflegalize -cell $_DFF_P_ x` | every flop becomes a plain `$_DFF_P_` (enables and sync resets become gates); an initial value it cannot keep is a Yosys error (not scored); no flop removed, no undefined value created | n/a | |
| `opt_expr -undriven` (in `opt -full`) | an undriven signal becomes `x`: the combinational analogue | refused earlier by `fourstate` (e) | `partial.sv` (bit 1 of `u` never written: no flop, an undriven bit), the review's `ud.sv` |
| `memory -nomap` (`opt_mem`): "M.A: removing const-x lane I" (`opt_mem.cc:117`; no write loads bit lane I of array A with a value: no write port left, or every enabled write's data is x there) | no flop is built: every READ of the lane is connected to `x` before `memory_map`, so `opt_dff` logs nothing; each read resolved separately | **REFUSED** (section 12, finding F1; this row said until then that an unwritten word reaches `memory_map` and the first row, which is false for a lane no write loads, MEASURED) | `mem_rom_const.sv` (no write), `mem_dead_write.sv` (a write under a condition Yosys folds to false) |
| `memory -nomap` (`opt_mem`): "removing const-0 lane", "removing const-1 lane" | every read of the lane the constant: the power-up with that lane constant in every word, one value for every read | **KEPT** | `ok_mem_const0.sv` |
| `memory_map` | an array's words become flops; a word the write index cannot reach (the lane loaded in other words) has D = Q | the first row (REFUSED) | `mem_unreached_word.sv` (`m[{1'b0, q[0]}]` into four words, `m[3]` read) |
| the frontend's memory-to-registers ("Replacing memory \m with list of registers", constant-index writes) | one register per word; a word no write reaches is an undriven wire | refused earlier by `fourstate` (e) | `mem_word_undriven.sv` |
| `fsm` (`fsm_detect`, `fsm_extract`, `fsm_recode`, `fsm_map`): "Mapping FSM `C' from module `M'." | re-implements a state register from the state codes it extracts (one-hot for `auto`): the new flops power up in codes that are no value of the register, and a value that is no extracted state has no code | **n/a since 2026-11-06: the pass does not run** (the clocked flow's `synth -nofsm`, decided 2026-11-06, section 12.2: a state register keeps its own flip-flops; the log check stays as a backstop that should never fire); until then **REFUSED**, with or without a reset on the register (section 12, finding F2; before that an open finding, below) | `fsm_unreset.sv`, `fsm_reset.sv`, `fsm_reset_controller.sv` (the review's reset controller): pass the rule now, netlist the design's from every power-up, but stop at `postsynth` on a lint of a dead techmap wire (MEASURED, section 12.2); `ok_fsm_bits.sv` (read through its bits: never marked) accepted |
| `proc` (canonicalization), `abc`, `abc -fast`, `peepopt`, `alumacc`, `share`, `techmap` | no flop removed (`abc` runs without `-dff`); `proc_rmdead` drops a never-taken branch, so a register whose every write is dead gets no flop: undriven, the `opt_expr` row | n/a | |

**Open finding, closed in section 12 (finding F2; the text as it stood).** `fsm_detect` marks and
`fsm_recode` one-hot recodes a never-reset state register that is read only by comparisons with
constants (MEASURED, a scratch probe on the counter's interface: three states, "mapping auto
encoding to `one-hot`"). The recoded flop's power-up codes outside the one-hot set are no value of
the original register, and a two-hot code makes two state comparisons true at once, which no single
value gives (DERIVED). A probe with every 2-bit value a state was not marked ("Circuit seems to be
self-resetting"), and no fixture with a wrong netlist was built. A state register with a reset is
loaded at the reset, after which the codes are the states'. (Section 12: the adversarial round built
the wrong-netlist fixture, and the last sentence does not make the design safe: a register without
a reset that samples the state at the reset edge keeps the pre-reset code's effect, `fsm_reset.sv`,
MEASURED.)

### 11.3 The fixtures, MEASURED

`tests/seq_counter/never_loaded/` (first line `// expect: <stage>[: <message>]`;
`tests/checker/test_clocked_post.py` runs each through `check.py --unproved`, full postsynth, a fake
Lean for the design stage). "ls-sv vs netlist": ls-sv from the zero power-up against the scored
netlist from Verilator's zero start, reset and 210 counts (section 10's comparison, a scratch script).

| fixture | the scored log | names run | verdict (stage) | ls-sv vs netlist |
|---|---|---|---|---|
| `hold.sv` (= `ux4_200`) | D = Q on `_21_` | `u` | REFUSED (`score`), the twin warns | 10 of 212 cycles differ, from cycle 202 (`q` held at 200) |
| `hold_if.sv` | D = Q | `u` | REFUSED (`score`), the twin warns | the same |
| `never_true.sv` | D = Q | `u` | REFUSED (`score`) | the same |
| `never_active_en.sv` | never-active EN, one "1-bit" (an `x`) | `a`, `b`, `u` | REFUSED (`score`) | the same |
| `partial.sv` | (not reached) | | REFUSED (`fourstate` (e): "Wire cnt.\u [1] is used but has no driver") | |
| `ok_const0.sv`, `ok_const1.sv`, `ok_reset_hold.sv` | "Setting constant 0-bit" / "1-bit" (a 1) / "0-bit" | none `x`-assigned | accepted (`unproved`) | 0 differ |
| `ok_merge.sv`, `ok_signext.sv`, `ok_unused.sv` | none of 11.2's refused rows | | accepted | 0 differ |
| `ok_hold_folded.sv` (table fixture 0's construct) | none | | accepted, the twin warns | |

The acceptance table (section 4) through the same `check.py --unproved` run (MEASURED): the
ACCEPTED fixtures 0, 1, 5, 10b, 14 and 16 still pass every non-proof stage (5, 14 and 16 log
"1-bit" constants; the names run shows them 1); the rule-2 rejects 2, 7 and 8 and the probe's H1
twins (`h1_xopt`, `h1_rare`, `h1_bit`) are now refused at `score`, as are the review's `ux`,
`ux2`, `ux3`, `ux4_200`, `ux4_3`; 10a, 12, 13, 15, `ud`, `sl` at `fourstate` as before, 9 at the
source gate. The three references log no removal at all (MEASURED: their logs show only "Adding
SRST/EN"). Fixture 4 (ACCEPTED by the statement) fails at `postsynth`: Verilator's lint stops on
`%Warning-UNDRIVEN: Bits of signal are not driven: '_14_.Y'[6:0]`, a dead public-named wire of
the techmapped divider in the scored netlist. Not this rule's (the netlist and the postsynth code
are unchanged; DERIVED) and not fixed here: the clocked postsynth check fails closed on a run-time
`/` by a constant, which rule 3 admits; for the maintainers.

### 11.4 The cost (MEASURED)

* The log parse: 0.21, 0.29 and 0.46 ms per synthesized point (the counter's, the sorter's (8, 8)
  and matmul's (4, 8, 32) synthesis logs, 18, 24 and 37 KiB).
* The names run, only when a removal or a "1-bit" constant is logged: one more canonicalization
  and synthesis, 0.15 s for the counter, 0.31 s for the sorter at (8, 8), 2.92 s for matmul at
  (4, 8, 32). The references log neither: 0 s.
* The source-level twin: milliseconds (`clocked_rules.check`'s `seconds`).

### 11.5 Rule 3's Python twin (question 4)

`check/clocked_rules.py` `xsafe_findings`, in the `clocked_rules` stage (every clocked kind, before
any Lean stage, at every probe point, on the pinned extractor's envelope: the tree
`load_design_sv2` ingests). The Lean `xsafeB` stays the authority; the twin refuses only what
ls-sv's lowering certainly turns into a construct `xsWidth` refuses (READ, `Param2.lean`
`instExpr2`, `instDivOperand2`, `dynPartRead`, `fitExpr2`), each with its own message:

| construct | why the loaded design fails `xsafeB` | message (abridged) |
|---|---|---|
| run-time `/`, `%` (`u/`, `s/`, `u%`, `s%`, `/`, `%`) whose divisor reads a signal | the divisor is never lowered to a literal: `constNZ` is false (`binW`) | "run-time division `(d / d)` by a divisor that reads `d`: a divisor of 0 gives x ..." |
| `**` with a signed exponent (`u**s`, `s**s`) whose base reads a signal | the same, for the base | "power ... with a signed exponent and a base that reads a signal ..." |
| a run-time bit/element select, read or written, whose index mentions a signal declared signed | the lowered `Expr2.index`/`Lhs2.index` keeps the name: `unsignedIdx` is false | "run-time index in `a[(i + u)]`: the index mentions `i`, declared signed ... (W5)" |
| a run-time bit select `v[i]` of a declared vector (lsb 0, known element width) by a plain signal with `2^width(i) * elemW > width(v)` | `xsWidth`'s `.index` case | "run-time index in `a[i]`: the 2-bit index can address element 3, past the 3 elements of `a` ..." |
| a run-time indexed part-select read `v[i +: W]`, `v[i -: W]` | `dynPartRead` pads the vector with `x` literals (`LVec.xVec`) | "run-time indexed part select `data[i +: 2]`: ls-sv's lowering reads the window over the vector padded with x bits ..." |
| an `x`/`z` literal outside a `casez`/`casex` item, or a casez/casex item narrower than an identifier subject | `xsWidth (.lit v)` needs `allKnown`; a narrower item is lowered under a `resize`, outside `patOK`'s literal case | "an x/z literal ... admits an x or z digit only in a casez/casex item pattern at the case's width ..." |

Everything else is the proof's: an operator at unequal widths (the lowering always fits the
operands), a constant divisor written as an expression, a constant select out of range
(`fourstate` (c)), an `Unsupported` node (the `design` stage). Sound for refusals by construction:
the walk enters only code live at the point (the top module's processes and `GenerateFor` bodies
with an iteration), not `GenerateIf` branches or instances.

**Agreement (MEASURED, `tests/checker/test_xsafe_twin.py`, REAL Lean, in `tests/run.py`'s
`comparator` step).** The twin, and `xsafeB (d.sem N)` of the design `load_sv` loads from the same
file, at N = 1, 2, 3, 8, on the 68 fixtures of `tests/seq_counter/xsafe/` (the acceptance table's
`.sv` files, the probe's twins, the attacks on revisions 2 and 3, the review of revision 3).
T = admitted at the four points, F = refused at all four (no fixture's verdict depends on N);
U = the loaded design has an `Unsupported` node at every point.

| fixtures | twin | `xsafeB` | |
|---|---|---|---|
| `a1_signed_idx`, `c1_signed_wridx`, `f12_sidx_read`, `f13_sidx_write`, `s5_signed_sum`, `s8_ternary`, `s10_mixed` | F (signed index) | F | agree |
| `b1_partsel_up`, `b2_partsel_dn`, `b3_partsel_scaled`, `f17_scaled_ps` | F (indexed part select) | F | agree |
| `c2_rt_div`, `f3_w2` | F (run-time divisor) | F | agree |
| `f10_oob` | F (index range) | F | agree |
| `a3`–`a6`, `c3`, `d1`–`d4`, `e1`, `e2`, `f0`, `f1_mealy`, `f1_nested_width`, `f1_tover`, `f1r`, `f2_ctx_or`, `f2_w1`, `f2r`, `f3_ctx_concat`, `f4`–`f8`, `f5_guard_rst`, `f10_pow2`, `f14`, `f15_cast_idx`, `f16`, `f17w`, `h1_bit`, `h1_rare`, `h1_xopt`, `s2_cast_idx`, `s9_wr_cast`, `sl`, `slu`, `ud`, `ux`, `ux2`, `ux3`, `ux4_200`, `ux4_3` (44) | T | T | agree |
| `g1_asc`, `g2_offset`, `g3_asc_write`, `s7_signed_partsel`, `sl2` | T | F, U | the `design` stage refuses them first (an ascending range, a nonzero lsb label, a signed part-select base, `2'sb11 >>> en`) |
| `a2_multidrv` | T | (`load_sv` refuses: two drivers) | the loader refuses it (and `fourstate`'s slang analysis) |
| `b4_inside`, `czx`, `f9_eqx`, `f11_w4` | (gate) | (gate) | the source gate refuses them |

So (at these commits; section 12, finding F3, found two unsound refusals this table did not hold,
a constant written with `$bits`, now fixed): 0 unsound refusals; 58 agree at every point; the 5 that differ are refused by an earlier
stage, as are the 5 neither side reaches. Table.lean's hand-built twins give the loaded designs'
verdicts (`f9` and `u4`, which no envelope has: false and true). Fixture 15 and `s2`, `s9`, `sl`
are admitted by both and wait for W5 (11.7); `fourstate` refuses them meanwhile. The twin's walk:
35 s for the 68 extractions, milliseconds per design after extraction (`seconds` in the stage's
record).

Through `check.py --unproved` (MEASURED), the twin is the first refusal for `f3_w2`, `c2_rt_div`
(finding 4: `q <= d / {7'b0, en}` now refused before the proof), `b1_partsel_up` and `s10_mixed`
(the mixed-sign index `fourstate` admits); the other refused fixtures stop at `fourstate` first.
The three references, the counter, and the matmul and sorter attacks pass the twin (MEASURED).

### 11.6 The trusted text (docstrings only)

`SvGolf/TaskSeq.lean`: the rule-3 docstring names every W5 form (an index that mentions a signal
declared signed is refused structurally; a `$signed` cast and a signed literal are dropped by ls-sv's
loader, so `fourstate` refuses them until W5's fix lands, and then the structural clause is removed);
the casez wording of that docstring and of `patOK`'s (an `x` digit of a casez item is not a
wildcard, and the gate refuses it; finding D's remainder); the "revision 2" labels of its contents
list and v2 section header, and of the three `Spec.lean` files, removed (finding E's remainder).
No definition changed. MEASURED: `lake build SvGolf tasks svgolf-eval tests.seq_counter.Spec
tests.seq_counter.negative.Refute tests.seq_counter.negative.Table`, 134 jobs, green.

### 11.7 Dependencies

* **W4 (ls-sv).** A `unique`/`priority` case is validated on the snapshots, not where it executes;
  until ls-sv's fix the source gate refuses the qualifiers (section 7).
* **W5 (ls-sv).** A signed dynamic index is read unsigned. Rule 3 refuses an index that mentions a
  signal declared signed (decided 2026-11-06: until ls-sv's fix, signedness kept through ingestion,
  lands; then that clause is removed); a `$signed` cast and a signed literal are invisible in the
  loaded design and refused only by `fourstate` (d) until then (fixture 15, `s2`, `s9`, `sl`).
* **`fourstate` (e)'s undriven check.** Rule 2 reads a variable no process writes as a constant
  power-up value, Yosys as undefined (finding B, `ud.sv`), and a register bit no write reaches gets no
  flop, so the never-loaded rule never sees it (`never_loaded/partial.sv`), and nor does it see an array
  word Yosys's frontend turns into an undriven register (`never_loaded/mem_word_undriven.sv`, section
  12). These are refused only by `fourstate` (e) ("is used but has no driver"): the never-loaded rule
  and rule 2 depend on it.
* **Distinct declaration names (the loader).** `KnownEntry` reads an input's width from the FIRST
  declaration of its name (`sigWidth`), `Interface` from the port's own declaration (`inputPorts`). A
  `Design2` with an earlier, differently wide declaration of a port's name has no known entry that
  drives the port at its width, and `FollowsPU` then holds vacuously (DERIVED; found while porting these
  rules to `ReactTask` on branch `svgolf-react`, whose `Interface` asks for distinct names, its
  `tasks/arbiter/README.md` section 7). The three kinds here do not ask for it: they rely on the
  pipeline, which yields no such design (DERIVED: a redeclaration is illegal SystemVerilog, and the
  pinned extractor keeps one declaration of a redeclared port name, MEASURED on a counter that redeclares
  `en` as `logic [2:0]`). Recorded here, then closed (decided 2026-11-06, section 12.2, M3): each of the
  three kinds' `Interface` now asks for distinct declaration names, as `ReactTask.Interface` does.
* **Obligation C stays sampled.** The never-loaded rule closes one Yosys deviation the sampled
  check missed (finding A passed 321 cycles from each of three power-ups), and section 12 two more
  (an array lane no write loads; a state register the fsm pass re-implemented, which the flow's
  `synth -nofsm` has removed since, section 12.2); others (a
  defined-value disagreement) are still found only where the post-synthesis stimulus reaches them.

### 11.8 Tests (MEASURED, 2026-11-06, this branch at the commits above)

`tests/run.py --only matmul,sorter`, one Lean-slot acquisition per step (`seq_counter` is not a
`tasks/` task: its checks are `tests/checker/test_clocked.py` and `test_clocked_post.py` in `unit`,
and `test_xsafe_twin.py` in `comparator`):

| step | checks | failed | time | |
|---|---|---|---|---|
| layout | 25 | 0 | 0 s | |
| build | 1 | 1 | 59 s | already broken: `tests/{add,mul,clmul}/negative/Refute.lean` (`load_design_sv2` refuses `only_n16.sv`, section 7); every other module builds |
| unit | 24 | 0 | 523 s | `fourstate.py --selftest` (27 rows) and every `tests/checker` test of the step, `test_clocked_post.py` with the never-loaded fixtures among them |
| comparator | 3 | 0 | 240 s | `test_comparator.py`, `test_bv_decide.py`, `test_xsafe_twin.py` (55 s) |
| leaderboard | 2 | 0 | 5 s | |
| modes, canon, drafts, negatives, baselines, validate, sandbox | 0 | 0 | | nothing of these steps applies to matmul and sorter |
| references | 10 | 0 | 140 s | `matmul_g1` and `sorter_ins` accepted; full postsynth 0 failures at every point; scores unchanged (87173.6064 µm², 4 × 10696 ps, 802 flops; 5512.7872 µm², 16 × 2523 ps, 81 flops) |
| ppa | 11 | 0 | 13 s | |
| attacks | 13 | 7 | 216 s | the 6 matmul attacks pass; the 7 sorter attacks are rejected at their expected stage (`solution`), but `tests/expected.json` pins the Lean error's line, 2 lines off (`155:26`/`132:90`, the run gives `157:26`/`134:90`): already broken (READ: `svgolf-prep` has the same `expected.json` entries and the same `sorter_ins.lean` lines 132 to 157; no commit here touches either; refreshed on 2026-11-06, section 12.2, L1) |

Also: `lake build SvGolf tasks svgolf-eval tests.seq_counter.Spec
tests.seq_counter.negative.Refute tests.seq_counter.negative.Table`, 134 jobs, green;
`score/fourstate.py --selftest` PASS after its docstring edit. The worktree had no copy of the
pinned sky130 liberty (`score/lib/`, not in git): the first run of `test_clocked_post.py` failed
every clocked check at `ppa` for that reason; a copy with the pinned sha256 (`ef34f999…`) was put
there before the runs above.

## 12. The adversarial round on the rules of section 11 (2026-11-06)

An adversarial round attacked section 11's rules on branch `svgolf-react` (which merges this
branch) with the pinned flow (Yosys 0.53, `53c22ab`), `svgolf-eval --trace --start`, Icarus on the
scored netlist from forced flop power-ups, and `check.py --unproved` (full post-synthesis, a fake
Lean for the design stage). Each finding was re-measured before any fix; the counter fixtures are
on this branch (`tests/seq_counter/never_loaded/`, `tests/seq_counter/xsafe/`), the arbiter
fixtures in the session scratchpad.

| # | finding (the attack's severity) | verdict | fix |
|---|---|---|---|
| F1 | an array lane no write loads bypasses the never-loaded rule (HIGH) | CONFIRMED | refused at `score` (`score.MEM_UNDEFINED`) |
| F2 | a never-reset state register recoded by the `fsm` pass (HIGH) | CONFIRMED, and a reset does not close it | every FSM the flow re-implements refused at `score` (`score.FSM_MAPPED`); superseded (decided 2026-11-06, section 12.2): the clocked flow runs `synth -nofsm`, the refusal a backstop |
| F3 | the rule-3 twin refuses a constant built with `$bits` (MEDIUM, plausible) | CONFIRMED (`xsafeB` true, MEASURED), and `fourstate` (d) refuses the select form too | the twin reads `$bits`/`$size`/`$high` of a signal as a constant; `fourstate` (d) reads a query-function index as constant |
| F4 | the reactive post-synthesis check (i) rejects a correct design whose output depends on an unreset register (MEDIUM) | CONFIRMED | branch `svgolf-react` (the reactive kind is there); the transaction kinds' analogue recorded below |
| low | the never-loaded twin is silent on `u <= u & u` and similar (LOW) | CONFIRMED (an advisory gap; the log refuses all four) | the advisory recognizes the forms |

No finding shows ls-sv deviating from IEEE 1800: in each, ls-sv's run is the design's from every
power-up and the pinned flow's netlist is not (F1, F2), or a checker stage is wrong (F3, F4).

**F1, confirmed.** `mem_rom_const.sv` (an unpacked array no process writes, read at a constant
index, decided both ways) and `mem_dead_write.sv` (written only under `q == 300`, which Yosys folds
to false), on the counter's interface:
* the scored log shows `cnt.m: removing const-x lane 0` and none of section 11.2's lines:
  `flop_removals` was empty, so `never_loaded` did not fire; `fourstate` passes (a kept memory is no
  undriven wire); the twin passes (a constant index builds no `x` default) (MEASURED);
* ls-sv from `zeros`, `seed:1`, `seed:2`: reset and 210 counts give q = 210, no `x`, both schedules
  agree; the netlist under Icarus from all-zero, all-one and two random flop power-ups: q = 200
  (MEASURED);
* the statement (MEASURED, `load_sv` and the statement's functions): `xsafeB` and `mooreOutDepB` true
  at N = 1, 2, 3, 8 with no `Unsupported` node; the counter's claim on reset and 210 counts, both
  schedules, holds from each of the four power-ups of `m[0]`, `m[1]`; `boundedPU` at N = 2 true;
* the arbiter twins (the reference plus the array, guard `tick == 2^17 - 1`): ls-sv from `zeros` and
  `seed:1` over 131100 entries of `req` all ones, no violation; the netlist from all-zero, all-one and
  random power-ups violates G3 and G4 at entry 131071; `xsafeB` true at N = 1, 2, 3, 5, 8
  (MEASURED). The arbiter's post-synthesis long segment (70000 entries) never reaches the guard.
* Mechanism (READ, `passes/opt/opt_mem.cc` at the pinned sha): `opt_mem` finds a bit lane no
  enabled write loads with a defined value (no write port left, or every write's data is `x` there),
  logs "removing const-x lane" and connects every read of the lane to `State::Sx` before
  `memory_map` builds any flop. Section 11.2's memory row was incomplete, not wrong everywhere: a
  word the write index cannot reach while the lane is loaded in other words does reach
  `memory_map` and the D = Q row (`mem_unreached_word.sv`, refused before this round, MEASURED), and
  an array written only at constant indices becomes registers in the frontend, its unwritten word an
  undriven wire that `fourstate` (e) refuses (`mem_word_undriven.sv`, MEASURED).
* Fix: `score.flop_removals` gains `memory_undefined` (the const-x lines) and `never_loaded` refuses
  them: "never-loaded memory at N=8: `m`. No write loads a bit lane of the array with a value, and
  the pinned Yosys connects every read of that lane to an undefined value before it builds any
  flip-flop (its log: `cnt.m: removing const-x lane 0`) ...". The const-0 and const-1 lanes give
  every read one value, a power-up the semantics has: kept (`ok_mem_const0.sv`: the netlist counts
  to 210 from all four power-ups, MEASURED); the const-1 lines are recorded too
  (`memory_constant_one`), since the netlist's all-zero start then differs from ls-sv's.

**F2, confirmed, and a reset does not close it.** `fsm_unreset.sv` (a never-reset 2-bit `s`, three
loaded states and a hold for the fourth value, read only by comparisons whose xor is 1 for every
value of `s`):
* the log: "Found FSM state register cnt._0_", "mapping auto encoding to `one-hot`"; the FSM keeps
  the three states it finds in the next-state mux tree (the fourth value has no code); `flop_removals`
  was empty (MEASURED);
* ls-sv: q = 210 from `zeros`, `seed:1`, `seed:2`; the netlist (11 flops): q = 200 from all zeros and
  from one random power-up, 210 from all ones and the other (MEASURED); `xsafeB`, `mooreOutDepB` true
  at the four points, and the claim on reset and 210 counts holds from each of the four values of `s`
  (MEASURED); the arbiter twin: the netlist from all zeros violates G3 and G4 at entry 131071, ls-sv
  never (MEASURED).
* Section 11.2's open finding ended "A state register with a reset is loaded at the reset, after
  which the codes are the states'." True of the state register, not of the design:
  `fsm_reset.sv` resets `s` and adds a never-reset `r` that samples the xor of the four comparisons
  every cycle (1 for every value of `s`); ls-sv: q = 210 from `zeros`, `seed:1`, `seed:2`; the netlist
  (12 flops): q = 209 from all zeros and from one random power-up (MEASURED): the reset edge loads `r`
  from the pre-reset code.
* Fix (superseded on 2026-11-06 by `synth -nofsm`, section 12.2; the text as it stood): `score.flop_removals`
  gains `fsm_mapped` (fsm_map's "Mapping FSM `C' from module `M'."), and
  `never_loaded` refuses every one, naming the register from the names-kept run's `$fsm$<register>`
  cell: "state register re-implemented as a state machine at N=8: `s`. ... Rule (txtask-v2,
  2026-11-06: svGolf disallows a design where the pinned Yosys deviates from the semantics): refused
  in every clocked task. The flow recodes only a register whose every reader compares the whole
  register with a constant (`s == 2'd1`, a `case (s)`); read it otherwise, a bit of it for example".
  JUDGED: a narrower rule admitting a reset state register would have to show that no register
  samples the pre-reset code at the reset edge; not drafted. The cost to a golfer (an independent
  review, 2026-11-06, MEASURED on the pinned flow's scored log at N = 8): an ordinary reset controller,
  a 2-bit `s` reset to 0 with the three states it reaches decoded by `case (s)` and read as `s != 2'd3`
  beside a reset `q`, is mapped ("Mapping FSM") and so refused, though it is correct from every
  power-up and nothing samples its pre-reset code (DERIVED); whether the rule should stay this wide is
  for the maintainers. (Decided 2026-11-06, section 12.2: the fsm pass is off in the clocked flow.)
* The cost (MEASURED): none of the four clocked references maps an FSM or removes a memory lane at
  its scoring point or any post-synthesis point (`cnt` at N = 8; `rr_mask` at N = 3, 5, 8;
  `matmul_g1` at (2, 4, 8) and (4, 8, 32); `sorter_ins` at (3, 4) and (8, 8)); nor does any of the 141
  clocked `.sv` fixtures of `svgolf-react`'s tree at its task's scoring point (126 synthesized; the
  gate or the flow refuses 15). `ok_fsm_bits.sv` (a reset 2-bit state read through `s[0] & s[1]`) is not
  marked and is accepted.

**F3, confirmed.** `t1_bits_sidx.sv` (`sq[$bits(sq) - 1]`, `sq` signed) and `t2_bits_div.sv`
(`q + ($bits(q) / $bits(q))`): the twin refused both at N = 1, 2, 3, 8 (a signed run-time index; a
divisor that reads `q`), and `xsafeB` of the loaded designs is true at all four points (MEASURED,
real Lean): ls-sv folds `$bits` (`Param.lean` `evalInt`), so `t1`'s select loads as the constant
slice `(sq, 7, 1)` and `t2`'s divisor as a literal. ls-sv and the netlist both count to 210
(MEASURED). So section 11.5's "0 unsound refusals" did not hold for constants written with `$bits`.
Fix: the twin's name walk (`idents`) skips the argument of `$bits`, `$size` and `$high` applied to a
signal, the forms `evalInt` folds; any other argument (which `evalInt` refuses: an `Unsupported` node)
stays a read. MEASURED: on the 130 envelopes of the existing clocked fixtures (tests/seq_counter,
tests and tasks of matmul, sorter, arbiter) the twin's verdicts and advisories are unchanged;
`t1`, `t2` are admitted and `t3_bits_idx.sv` (the unsigned control) still is.
* Re-measuring through `check.py --unproved` found one more stage wrong on the same construct: the
  `fourstate` stage, which runs before the twin, refused `t1` and the attack's control
  `t3_bits_idx.sv` (`q[$bits(q) - 1]`) as run-time 32-bit indices that can leave the vector
  (MEASURED): rule (d) took an index as constant only when it reads no signal name
  (`banlist._is_const`), and `$bits(q)` names `q`. Both are constant selects (IEEE 1800-2023
  §20.6.2: `$bits` of a fixed-size argument is a constant; §20.7, the array queries). Fix
  (`score/fourstate.py` `_is_index_const`, the banlist untouched): an index is also constant when
  slang evaluates it to a known constant and its every run-time name is the argument of a type or
  array query function. MEASURED: `fourstate.py --selftest` PASS with two new rows
  (`ok_query_index.sv`, which the old rule refused three times, passes; `query_runtime_index.sv`,
  `v[$bits(v) - 1 - i]`, is still refused); the verdicts on the 308 `.sv` fixtures of every task
  (137 clocked, 171 combinational) are unchanged; `t1` and `t3` now pass, `t2` passed before.

**The low finding, confirmed.** `u <= u & u`, `u <= u ^ 1'b0`, `u <= u | 1'b0`, `u <= u ? u : u`: the
log shows "Handling D = Q" for all four and `never_loaded` refuses them; the twin's advisory was
silent (MEASURED). `is_own_value` now recognizes the same-width `Resize`, `&`/`|` of two own values,
`&` with all ones, `|`/`^` with zero, and `?:` with two own arms (`hold_and.sv` warns and is refused,
MEASURED on the four).

**F4 (branch `svgolf-react`) and the transaction kinds' analogue.** The reactive check compared the
netlist with ls-sv bit for bit at every seed, though seeds 1 and 2 start the two from different
power-ups and a reactive guarantee admits several outputs: a correct arbiter whose mask is not reset
was rejected ("seed 2, cycle 1: gnt: the netlist (100) is not ls-sv (001)", both legal grants). Fixed
on that branch (section 12.4). The same reasoning applies to `clocked_seed`'s check (i) for tx-family and
stream-family, whose claims allow any latency up to the declared one (TaskSeq.lean C3: "Finishing
earlier is legal, and so is a data-dependent latency within `lat`"): a design whose `done`/`out_valid`
timing depends on an unreset register can be correct and is compared bit for bit across two
different power-ups (DERIVED; no fixture built). The transaction harness drives the stimulus from the
netlist's own `done` (a transaction's operands are held until it shows 1), so a fix needs ls-sv's run
judged on its own transactions; not changed here; for the maintainers.

### 12.1 Tests (MEASURED, 2026-11-06, this branch)

One step per acquisition of the shared Lean slot:

| run | result | time |
|---|---|---|
| `tests/checker/test_clocked_post.py` | 6 tests OK; `test_never_loaded_registers` runs the 21 fixtures of `never_loaded/` (the 9 new ones each at its expected stage and message: `mem_rom_const`, `mem_dead_write` and `mem_unreached_word` at `score` as never-loaded, `fsm_unreset` and `fsm_reset` at `score` as a re-implemented state register, `hold_and` at `score` with the twin's warning, `mem_word_undriven` at `fourstate`, `ok_fsm_bits` and `ok_mem_const0` accepted) | 103 s |
| `tests/checker/test_xsafe_twin.py` (real Lean) | OK: 71 fixtures, 0 unsound refusals, every disagreement an `Unsupported` row (`g1_asc`, `g2_offset`, `g3_asc_write`, `s7_signed_partsel`, `sl2`, as in section 11.5); `t1_bits_sidx`, `t2_bits_div`, `t3_bits_idx` admitted by both at N = 1, 2, 3, 8 | 98 s |
| `tests/run.py --only matmul,sorter`, step `references` | 10 checks, 0 failed: `matmul_g1` and `sorter_ins` accepted, full postsynth 0 failures at every point, scores unchanged (87173.6064 µm², 4 × 10696 ps, 802 flops; 5512.7872 µm², 16 × 2523 ps, 81 flops) | 244 s |
| `tests/run.py --only matmul,sorter`, step `layout` | 25 checks, 0 failed | 0 s |
| `score/fourstate.py --selftest`, `score/test_score.py` | PASS (29 rows, two new); 17 tests OK | |

The counter reference is `test_clocked_post.py`'s (accepted, scored twice the same). Before the fixes
(MEASURED, `check.py --unproved` on `svgolf-react`, which had merged this branch at `8673171`): the
counter forms of F1 and F2 and their arbiter twins `unproved` (every stage but the proof passes),
`fsm_reset.sv` rejected at `postsynth` (seed 0, cycle 1: the sampled check happens to reach it),
`t1` at `fourstate`, `t2` at `clocked_rules`, the unreset-mask arbiter at `postsynth`.

### 12.2 The decisions of 2026-11-06 on the review of this section

An independent review of this section's fixes (2026-11-06) found no soundness hole and left seven
items; the maintainers decided each the same day:

| item | the review's finding | decided 2026-11-06 | reason | where |
|---|---|---|---|---|
| M1 | branch `svgolf-react`'s refusal register has no row for the arbiter's 17 attacks and 2 negatives, nor for this round's refusals | add the rows there and regenerate `REFUSALS.md` | a refusal the register does not name is undocumented for a golfer and for the site | branch `svgolf-react` |
| M2 | the FSM rule refuses every state register the fsm pass maps, an ordinary reset controller among them | the clocked flow runs `synth -nofsm`; the "Mapping FSM" refusal stays as a backstop | the re-encoding gives a power-up state that is no state of the design, a Yosys deviation; turning the pass off removes it for every design instead of refusing a common correct construct (clocked tasks are not ranked yet) | below |
| M3 | `SeqTask`, `TxTask` and `StreamTask` can hold vacuously for a hand-built `Design2` that declares a port name twice (section 11.7) | each `Interface` asks for distinct declaration names, as `ReactTask.Interface` does | the statement closes the gap itself instead of resting on the pipeline | below |
| L1 | the sorter attacks' pins in `tests/expected.json` are 2 lines off | refresh them from a measured run | the attacks are rejected at their stage; only the pinned lines drifted | below |
| L3 | the never-loaded message says every register must be loaded; the rule as built refuses only a flop the pinned flow removes while reads remain | the narrower rule stands; the message and the docs describe it | it is exact for the mechanism (a flop the flow removes while reads remain, or a const-x array lane) | below |
| L4 | stale text (the arbiter's status in `tasks.lean` and its `Spec.lean`, `txtask-v1` in two refusal-register rows) | fix it | stale text misstates the statement or overclaims | below; the arbiter's texts on `svgolf-react` |
| L5 | the tx/stream post-synthesis check (i) compares bit for bit across two power-ups (F4's analogue, above) | recorded, not fixed | an over-rejection of correct designs, not an admission of wrong ones | |

**M2, as built.**

* `score/svgolf_seq.ys`: `synth -flatten -nofsm -top @TOP@`. READ (Yosys 0.53, `53c22ab`, `help synth`):
  `-nofsm` "do not run FSM optimization"; the coarse script runs `fsm (unless -nofsm)` and nothing else
  reads the flag. The combinational flow is untouched (`svgolf.ys`, `canon.ys`, `ge.json`: no change;
  `test_comb_flow_unchanged`). The clocked script's sha256 is now `d06e4351…` (`score/PPA.md`), and
  `score/measured/matmul.json` and `sorter.json` were measured again (`points.py measure --records`):
  every number is equal, only the flow's `script_sha256` changed, and `points.py check` passes
  (MEASURED).
* `never_loaded` keeps the `FSM_MAPPED` check as a backstop, with its own message ("... runs `synth
  -nofsm`, yet its log shows ... This check is a backstop that should never fire"),
  `test_the_fsm_backstop`.
* **(a) The references score exactly as before** (MEASURED: the old script against the new on the same
  canonical RTLIL, every score field and the netlist's bytes): `cnt` at N = 8; `matmul_g1` at (2, 4, 8),
  (2, 8, 32), (4, 8, 32); `sorter_ins` at (3, 4), (4, 8), (8, 8), (16, 8); `rr_mask` (branch
  `svgolf-react`'s file) at N = 3, 5, 8: identical at every point. Of the 147 clocked `.sv` fixtures of
  both trees at their task's scoring point (15 refused alike by the gate or the flow), exactly two give
  another netlist, `fsm_unreset.sv` (11 flops, now 8) and `fsm_reset.sv` (12, now 9): the two whose old
  log maps an FSM. (An independent re-run, 2026-11-06, MEASURED: also every probe point of the four
  references, identical, and the reset controller `fsm_reset_controller.sv`, added with this change,
  is the third fixture whose old log maps an FSM: 11 flops, now 10.)
* **(b) The FSM fixtures' netlists are the designs'** (MEASURED: the scored netlist under Icarus from 5
  forced flop power-ups, all 0, all 1 and three random, against ls-sv, `svgolf-eval --trace`, from 5,
  `zeros` and `seed:1` to `seed:4`, both schedules, at every cycle of one stimulus: a reset, 230 counts,
  100 cycles of random `en`, a second reset, 5 counts, 100 random; 437 cycles): `fsm_reset_controller.sv`
  (the review's reset controller, 10 flops), `fsm_unreset.sv` (8: `s` is unread once the comparisons'
  xor folds to 1), `fsm_reset.sv` (9) and `ok_fsm_bits.sv` (10) agree with ls-sv at every cycle from
  every pair of starts; so does F2's arbiter twin (`a_s1`, the session scratchpad, on `svgolf-react`'s
  arbiter task, 16 flops), over 601 cycles of random requests and over 131101 cycles past its `tick`
  guard (ls-sv from `zeros` and `seed:1`). The same harness on the old flow finds F2: `fsm_unreset.sv`
  differs from ls-sv at 130 of the 437 cycles from three of the five power-ups, `fsm_reset.sv` at 330
  from two.
* **Still refused, at `postsynth`** (MEASURED, `check.py --unproved`, full post-synthesis):
  `fsm_reset_controller.sv`, `fsm_unreset.sv` and `fsm_reset.sv` pass the never-loaded rule, but their
  `case (s)` now reaches the netlist as a techmapped `$pmux`, which leaves a dead wire (`\_24_.B_AND_S`
  in the controller's netlist: partly undriven, read by no cell, MEASURED on the netlist text), and
  Verilator's lint, every warning fatal, stops on `%Warning-UNDRIVEN` ("the scored netlist does not
  compile"): the over-rejection section 11.3 records for a techmapped divider. A PROBE, with UNDRIVEN
  waived in the checking process only (nothing in the tree changed): all three pass every stage but the
  proof, post-synthesis 0 mismatches over 3 seeds. So the decision's aim, an ordinary reset controller
  accepted, needs one more change, a post-synthesis lint that waives an undriven bit no cell reads. Not
  made here (it changes what the stage accepts, in the combinational flow too, and is not decided): for
  the maintainers. The fixtures expect `postsynth` until then.

**L3, as built.** The rule's sentence in `check.py` `never_loaded` (both the register and the memory
message) and the twin's advisory (`check/clocked_rules.py`) now say what is refused: "in every clocked
task, a design is refused where the pinned flow removes a flip-flop while reads of it remain (its next
value is always its own, its enable is never active, or the only value it is loaded with is undefined),
or connects the reads of an array lane no write loads to an undefined value". A register nobody loads
whose every read folds away (section 11.1, `ok_hold_folded.sv`) is accepted, as before; the message
no longer suggests otherwise. Section 11.1's quotation is updated; the fixtures' `expect` lines match
the messages' unchanged first sentences (MEASURED, section 12.3).

**M3, as built.** The trusted text (`SvGolf/TaskSeq.lean`): `SeqTask.Interface`, `TxTask.Interface`
and `StreamTask.Interface` each gain `ReactTask.Interface`'s conjunct, distinct declaration names,

```
(d.decls.toList.map Decl.name).Nodup
```

and their docstrings say so; the module docstring, the `SeqTask` overview's conjunct 1 and the v2
section's "everything above is txtask-v1 and is unchanged" name this one change. No other definition
changed, and `SatisfiedAtV2` keeps its shape (the conjunct sits inside `Interface`). With it,
`KnownEntry`'s width (the first declaration of a name) is the port's own (section 11.7). Untrusted
text that follows it: the references' interface theorems (`cnt_interface`, `mm_interface`,
`so_interface`) add the names' `Nodup` by kernel `decide` on the literal list of names;
`tasks/matmul/Properties.lean` and `tasks/sorter/Properties.lean` restate `Interface` with the conjunct
(`statement_iff_properties` unchanged), and the INTERFACE cards of their `properties.json` say it;
`SvGolf/Seq.lean`'s `CombTask.toSeq_interface` and `toSeq_satisfiedAt_iff` add the conjunct on the
combinational side, which does not ask for it (no combinational statement changes).
MEASURED: `lake build SvGolf tasks svgolf-eval tests.seq_counter.Spec
tests.seq_counter.negative.Refute tests.seq_counter.negative.Table`, 134 jobs, green, every `#print
axioms` among `propext`, `Classical.choice`, `Quot.sound`; the counter reference proved by `check.py`
with real Lean (stage `done`, the comparator's axioms `propext`, `Quot.sound`, `Classical.choice`),
`matmul_g1` and `sorter_ins` accepted by `tests/run.py`'s `references` step, scores unchanged
(87173.6064 µm², 4 × 10696 ps, 802 flops; 5512.7872 µm², 16 × 2523 ps, 81 flops).

**L1, as built.** MEASURED (`tests/run.py --only matmul,sorter`, step `attacks`, real Lean, before the
refresh): the 6 matmul attacks pass; the 7 sorter attacks are rejected at their expected stage
(`solution`) with the expected error, at `Solution.lean:157:26` (four) and `134:90` (three), where
`tests/expected.json` pinned `155:26` and `132:90`. The seven pins now carry the measured positions; the
rest of each message is unchanged (section 12.3 for the run after the refresh).

**L4, as built (the part on this branch).** `docs/sv-refusals.json` rows `sg-tx-guar` and
`sg-stream-guar` named `TxTask.Statement` and `StreamTask.Statement` "(txtask-v1)"; they now name
`TxTask.StatementV2` and `StreamTask.StatementV2` (txtask-v2), whose `Guar` claims hold in every run
from every power-up state on every known stimulus. `svgolf/REFUSALS.md` regenerated with
`tools/gen_sv_refusals.py --write` (`docs/sv-refusals.md` byte-identical); `--check` passes (MEASURED).
The two arbiter texts (`tasks.lean`'s status line, the arbiter `Spec.lean`'s sentence on the scored
netlist) are on branch `svgolf-react`.

### 12.3 Tests (MEASURED, 2026-11-06, this branch after the commits of 12.2)

One run per acquisition of the shared Lean slot (the unit-level checks batched in one):

| run | result | time |
|---|---|---|
| `lake build SvGolf tasks svgolf-eval tests.seq_counter.Spec tests.seq_counter.negative.Refute tests.seq_counter.negative.Table` | 134 jobs, green; every `#print axioms` among `propext`, `Classical.choice`, `Quot.sound` | 93 s |
| `check.py tests/seq_counter …/cnt.sv …/cnt.lean --postsynth full` (real Lean) | `done`: proved, the comparator's axioms `propext`, `Quot.sound`, `Classical.choice`, full postsynth 0 mismatches | 51 s |
| `tests/run.py --only matmul,sorter`, step `references` | 10 checks, 0 failed: both accepted, full postsynth 0 failures at every point, scores unchanged (87173.6064 µm², 4 × 10696 ps, 802 flops; 5512.7872 µm², 16 × 2523 ps, 81 flops) | 155 s |
| `tests/run.py --only matmul,sorter`, step `attacks` | 13 checks, 0 failed (before the refresh of L1: 6 passed, the 7 sorter pins 2 lines off) | 251 s |
| `tests/checker/test_clocked_post.py` | 7 tests OK; `test_never_loaded_registers` runs the 22 fixtures of `never_loaded/` (`fsm_unreset`, `fsm_reset` and `fsm_reset_controller` at `postsynth`, the dead-wire lint, 12.2), `test_the_fsm_backstop` new | 92 s |
| `tests/checker/test_xsafe_twin.py` (real Lean) | OK, 71 fixtures, verdicts as in section 12.1 | 61 s |
| `score/fourstate.py --selftest`; `score/test_score.py` | PASS (29 rows); 18 tests OK (`test_no_fsm_pass` new) | 6 s |
| `score/points.py check --task matmul --task sorter`; `tools/gen_sv_refusals.py --check`; `tools/docs_check.py` | ok (0 problems); ok (210 ls-sv entries, 69 svGolf entries); 89 marked blocks ok | 6 s |

### 12.4 F4 on branch `svgolf-react` (MEASURED, 2026-11-06)

**F4, confirmed.** `a_nomask` is the arbiter reference `rr_mask.sv` with `mask <= '1` dropped from
the reset branch (the grant is still reset). It is correct from every power-up: the first grant
after a release is the lowest requester of `req & mask`, or else of `req`, and from the first
non-zero grant on the mask is the reference's thermometer (DERIVED). ls-sv from `zeros`, `seed:1`,
`seed:2`, `seed:3`, 40 segments (20863 entries), N = 8: no violation of G0 to G4, both schedules
agree; the netlist under Icarus from all-zero, all-one and three random power-ups, 20000 random
entries: no violation (MEASURED). `check.py --unproved` rejected it at `postsynth`: "1 failures at
N=3 ... seed 2, cycle 1: gnt: the netlist (100) is not ls-sv (001)" (MEASURED): at that entry clients
0 and 2 request, and the two grants are both legal, chosen by two different power-ups of `mask`
(Verilator's `randReset(2)` start for the netlist, `seed:2` for ls-sv). The invariant the check
relied on, "a design whose claims hold from every power-up shows the same outputs from both" (the
reactive check's comment in `check/postsynth.py`), holds only where the claims fix the outputs, and
a reactive guarantee admits several. (The attack also placed that sentence in
`SvGolf/TaskReact.lean`'s docstring: NOT reproduced, READ, it is not there.)

**Fix** (`check/postsynth.py`, the reactive check only): the netlist is compared with ls-sv bit for
bit only where the two start from the same state, seed 0 when `zero_starts_agree` holds (the scored
log shows no register and no array lane replaced by the constant 1, the two KEPT removals that make
the netlist's all-zeros start differ from ls-sv's `zeros`); from the other starts both runs are held
to the guarantee (oracle.py `violations` on ls-sv's outputs as on the netlist's), after the
knownness and σ_src = σ_rev checks of every output. Each seed's record says which (`compared`).
What this gives up: at seeds 1 and 2 a disagreement of the netlist with ls-sv that breaks no claim
on the sampled stimulus is no longer reported (obligation C is sampled bit for bit at seed 0 for the
reactive kind, the guarantee at all three).

MEASURED after the fix, `postsynth.run_clocked` directly (no Lean) at tasks/arbiter's three points
(N = 3, 5, 8), three seeds each: `a_nomask` accepted, 0 failures, seed 0 compared bit for bit and
seeds 1 and 2 by the guarantee; the reference `rr_mask.sv` likewise; the attacks `a04_fixed`,
`a11_noreset`, `a12_stale_mask` still rejected, on G4, G0 and G4.

Tests on this branch after the merge of section 12's commit and the fix (MEASURED, 2026-11-06, one
step per acquisition of the shared Lean slot):

| run | result | time |
|---|---|---|
| `tests/checker/test_clocked_post.py` | 10 tests OK, the new `test_an_unreset_mask_passes_the_reactive_check` among them (tasks/arbiter, three points, three seeds, 0 failures; seed 0 bit for bit, seeds 1 and 2 by the guarantee) and the 21 never-loaded fixtures | 133 s |
| `tests/checker/test_xsafe_twin.py` (real Lean) | 2 tests OK: the counter's 71 fixtures and the arbiter's 20, the twin sound and in agreement with `xsafeB` | 176 s |
| `tests/run.py --only arbiter`, step `references` | 5 checks, 0 failed: `rr_mask` accepted, 210519, 210683, 211527 cycles over 3 seeds at N = 3, 5, 8, 0 failures; 769.488 µm², 2826 ps, 16 flops (unchanged) | 128 s |
| `tests/run.py --only arbiter`, step `attacks` | 17 checks, 0 failed (each attack at its expected stage and message) | 416 s |
| `check.py --unproved` on the round's fixtures | the arbiter forms of F1 (`a_m4`, `a_m5`) refused at `score` ("never-loaded memory at N=8: `m`"), of F2 (`a_s1`) at `score` ("state register re-implemented as a state machine at N=8: `s`"); `a_nomask` accepted (`unproved`, every non-proof stage); the counter forms likewise; `t1`, `t2` accepted | |

### 12.5 The decisions of 12.2 on branch `svgolf-react` (MEASURED, 2026-11-06)

After the merge of this branch's 12.2 and 12.3 (one conflict, in this file: the F4 section is now 12.4):

* **M2 and M3, carried to the arbiter.** The reactive kind scores and post-synthesizes with the same clocked
  flow, so the merge already runs `synth -nofsm` for it, and `ReactTask.Interface` already had the
  distinct-names conjunct; what changed is text: the arbiter README (a state register re-implemented by
  the fsm pass is no longer possible; txtask-v2's kinds ask for distinct names too) and the docstring of
  `check/postsynth.py` `zero_starts_agree`. F2's arbiter twin (`a_s1`, a never-reset 2-bit state read only
  by comparisons whose xor is 1) now passes `score` with the reference's netlist at `N = 8` (16 flops, the
  same area; no flop removal) and stops at `postsynth` on the dead-wire lint of 12.2 at `N = 3`
  (`\_59_.B_AND_S`, partly undriven, read by no cell; MEASURED, `check.py --unproved --postsynth full`).
* **M1.** `tools/gen_sv_refusals.py --check` failed with 19 names no row cites. New rows of
  `docs/sv-refusals.json`: `sg-react-guar` (the `ReactTask` guarantee, like `sg-tx-guar`: the 15 attacks
  rejected at `postsynth` and the negatives `bit_ring`, `reset_edge`), and a new group "Clocked tasks"
  with `sg-clocked-edge` (an edge process other than `always_ff @(posedge <clock>)`, the asynchronous reset
  among them: `a13_async`; READ: no branch had such a row, so it is new), `sg-clocked-rules` (the rule-3
  twin), `sg-never-loaded` (`a16_xopt`), `sg-never-loaded-mem` and `sg-fsm-backstop`; the pipeline table
  gains the `clocked_rules` stage and the clocked parts of `source` and `score`. `svgolf/REFUSALS.md` and
  `docs/sv-refusals.md` (its svGolf count row only) regenerated with `--write`.
* **L4, the arbiter's part.** `tasks.lean` gives the task's status (ready, not ranked; the statement a draft
  for the maintainers' review; the reference proved). The arbiter `Spec.lean`'s "The scored netlist is the
  circuit these runs are about" now says that the runs are ls-sv's and that obligation C (the netlist
  agrees with them on defined values) is sampled by the post-synthesis check, not proved; the same
  sentence describes the never-loaded rule as built (L3). A docstring of trusted text: no definition changed.

Tests (one step per acquisition of the shared Lean slot; the unit-level checks batched in one):

| run | result | time |
|---|---|---|
| `lake build SvGolf tasks svgolf-eval tests.arbiter.negative.Refute` | 136 jobs, green; every `#print axioms` among `propext`, `Classical.choice`, `Quot.sound` | 18 s |
| `tests/run.py --only arbiter`, step `references` | 5 checks, 0 failed: `rr_mask` accepted, full postsynth 210519, 210683, 211527 cycles over 3 seeds at `N = 3, 5, 8`, 0 failures; 188.979 GE, depth 17, 769.488 µm², 2826 ps, 16 flops (unchanged, `tests/expected.json`) | 103 s |
| `tests/run.py --only arbiter`, step `attacks` | 17 checks, 0 failed: `a13_async` at `source`, `a16_xopt` at `score` (the never-loaded message of L3), the other 15 at `postsynth` | 430 s |
| `tests/run.py --only arbiter`, step `negatives` | 2 checks, 0 failed: `bit_ring`, `reset_edge` at `solution` | 43 s |
| `tests/checker/test_clocked_post.py` | 11 tests OK | 150 s |
| `tests/checker/test_xsafe_twin.py` (real Lean) | 2 tests OK: the counter's 71 fixtures and the arbiter's 20, the twin and `xsafeB` in agreement | 197 s |
| `tools/gen_sv_refusals.py --check` (and `--strict`); `--emit-svgolf` against `svgolf/REFUSALS.md` (`cmp`); `tools/docs_check.py`; `score/time_limits.py --check` | ok (210 ls-sv entries, 75 svGolf entries, 171 names); identical; 89 marked blocks ok; ok | |
| `tests/site/test_site.py`; `score/test_score.py`; `score/fourstate.py --selftest` | 54 tests OK; 18 tests OK; PASS | 52 s |

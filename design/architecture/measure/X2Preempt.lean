/-
# X2: process atomicity versus preemption on E-core-0 (a measurement instrument)

**Historical, not ported.** Pinned to the commit it measured (`edce9ef8`, arch-x1, the E-core-0 it copies).
It does not typecheck against master's `CaseMode`, and nothing builds it (`compile-measure.sh` builds the
current instruments only).

ARCH-NOTE §7 X2 (§4.7 granularity). Run as

  lake env lean --run svgolf/design/architecture/measure/X2Preempt.lean <batch.json> [<from> <to>]

`<batch.json>` is written by `x2_rows.py batch`: the comb rows of the Xcelium goldens (envelope, parameter overrides,
signals, stimulus, pinned Xcelium cycles). One line `X2ROW <json>` is printed per row.

**What is copied.** The executor is a copy of agent A's E-core-0 (`LeanModels/Sv/Kernel/Core0.lean` on `arch-x1`,
commit `edce9ef8`, and `Elab.ofDesign2` from `Core0Obs.lean`), imported by nothing and importing none of A's files: typed
values and writes (`Val.ofLVec`, `Val.write`, LRM 6.11), the flat view read by `evalPure2`, an assign's activation
(`activate`), an `always_comb` body's statements (`execBody`: blocking assignments to static windows, `if`,
`case`/`case inside`, `begin … end`; NBA, dynamic or concatenated targets refused), the sensitivity (`Elab.sens`: an
`always_comb` is not sensitive to what it writes, LRM 9.2.2.2.1), triggering (`Elab.triggered`), the input events of a
slot (`Elab.applyInputs`, `Config.nextSlot`, `Config.start`). The store is an array indexed by declaration (E-core-0 is
flat: every `VarId` is `⟨[], i⟩`), so that configurations can be compared.

**The three policies.** All of them explore EVERY legal choice, breadth first, from the same slot start.
* `atomic` is E-core-0 itself (`step`): any ready process may run next, and it runs as ONE activation; the processes
  whose sensitivity saw a change between the store before and after the activation become ready.
* `stmt` adds preemption between statements (LRM 4.7: "statements … do not have to be executed as one event"; a
  process can be suspended and another ready process run). An `always_comb` activation is a sequence of atomic units: a
  blocking assignment (evaluate and write), or the evaluation of an `if` condition or a `case` subject and patterns
  (which selects the branch run later). After every unit, the processes whose sensitivity saw a change in THAT unit and
  that are waiting become ready; a process that is running (started and suspended) is not waiting, so it is not woken
  (LRM 9.2.2.2: `always_comb` waits on its sensitivity only between activations). Starting a process and running its
  first unit are one move (a started process that has run nothing is indistinguishable from a ready one).
  Continuous assigns stay one unit (E-core-0's fused evaluation and update; the policies here are about procedural
  statements).
* `eval` splits each blocking assignment of an `always_comb` further: evaluation, then (possibly after other processes)
  the write (LRM 4.7: "the simulator may suspend execution and place the partially completed event as a pending
  event").

A row's verdict per policy compares the set of closed stores (and of observed samples) with `atomic`'s, slot by slot,
each slot started from the canonical atomic run's store (a FIFO choice). If every slot's closed-store set is the same as
`atomic`'s, every behaviour of the row is (induction over slots). Otherwise the shortest witness schedule (breadth
first) is printed: `a<q>` an assign activation, `c<q>` a whole `always_comb` activation (atomic), `s<q>` start process
`q` and run its first unit, `r<q>` resume `q` for one unit.

This is an instrument: `partial def` is used for the syntax walks; nothing here is trusted or imported.
-/

import Lean
import Std.Data.HashSet
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2

open Lean (Json toJson)
open LeanModels.Sv

namespace X2

/-! ## The copy of E-core-0 -/

structure VType where
  width : Nat
  signed : Bool := false
  fourState : Bool := true

def VType.ofDecl (dc : Decl) : VType :=
  { width := dc.width, signed := dc.isSigned, fourState := !dc.twoState }

def VType.conv (ty : VType) (v : LVec) : LVec :=
  if ty.fourState then v else v.toTwoState

structure Val where
  ty : VType
  bits : LVec

instance : Inhabited Val := ⟨⟨{ width := 0 }, ⟨#[]⟩⟩⟩

def Val.ofLVec (ty : VType) (v : LVec) : Val := ⟨ty, ty.conv (v.resizeU ty.width)⟩

def Val.write (x : Val) (lo : Nat) (part : LVec) : Val := ⟨x.ty, x.ty.conv (x.bits.insertAt lo part)⟩

/-- The store: declaration `i` is variable `⟨[], i⟩`. -/
abbrev Store := Array Val

inductive Proc0 where
  | assign (target : Lhs2) (rhs : Expr2)
  | comb (body : Stmt2)

def Proc0.ofProcess2 : Process2 → Proc0
  | .assign t e => .assign t e
  | .alwaysComb b => .comb b
  | .unsupported k x => .comb (.unsupported k x)
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ =>
      .comb (.unsupported "always_ff" "clocked processes are outside E-core-0")

structure Elab where
  decls : Array Decl
  procs : Array Proc0
  /-- The design the windows are resolved against (only its declarations are read). -/
  d2 : Design2

def Elab.ofDesign2 (d : Design2) : Elab :=
  { decls := d.decls, procs := (d.processes.toList.map Proc0.ofProcess2).toArray, d2 := d }

def Elab.resolve (E : Elab) (n : String) : Option Nat := E.decls.findIdx? (·.name == n)

def Elab.view (E : Elab) (s : Store) : SvState :=
  (E.decls.toList.zip s.toList).map fun (dc, v) => (dc.name, v.bits)

def Elab.initStore (E : Elab) : Store :=
  E.decls.map fun dc => Val.ofLVec (VType.ofDecl dc) (dc.init.getD (LVec.xVec dc.width))

def Elab.writeWin (E : Elab) (s : Store) (n : String) (lo : Nat) (part : LVec) : Store :=
  match E.resolve n with
  | some i => s.modify i (fun x => x.write lo part)
  | none => s

def Elab.writeWins (E : Elab) (s : Store) (val : LVec) : List (Win × Nat) → Store
  | [] => s
  | ((n, lo, w), off) :: rest => E.writeWins (E.writeWin s n lo (val.extract off w)) val rest

def staticWin (d : Design2) (t : Lhs2) : Option Win :=
  match t with
  | .concat _ => none
  | _ =>
      (t.window? d).bind fun W =>
        (d.declWidth W.1).bind fun dw => if W.2.1 + W.2.2 ≤ dw then some W else none

partial def rawReads : Stmt2 → List ReadWin
  | .blockingAssign _ e => e.reads
  | .nbaAssign _ e => e.reads
  | .ifStmt c t e => c.reads ++ rawReads t ++ (match e with | some s => rawReads s | none => [])
  | .block body => body.toList.flatMap rawReads
  | .caseStmt subj items dflt _ _ =>
      subj.reads ++ items.toList.flatMap (fun it => match it with
        | .mk pats b => Expr2.listReads pats.toList ++ rawReads b) ++
      (match dflt with | some s => rawReads s | none => [])
  | .unsupported _ _ => []

partial def targetWins (d : Design2) : Stmt2 → List Win
  | .blockingAssign t _ => (staticWin d t).toList
  | .nbaAssign _ _ => []
  | .ifStmt _ t e => targetWins d t ++ (match e with | some s => targetWins d s | none => [])
  | .block body => body.toList.flatMap (targetWins d)
  | .caseStmt _ items dflt _ _ =>
      items.toList.flatMap (fun it => match it with | .mk _ b => targetWins d b) ++
      (match dflt with | some s => targetWins d s | none => [])
  | .unsupported _ _ => []

instance (st st' : SvState) (r : ReadWin) : Decidable (r.agree st st') := by
  cases r <;> unfold ReadWin.agree <;> infer_instance

def Elab.sens (E : Elab) (q : Nat) : List ReadWin :=
  match E.procs[q]? with
  | some (.assign _ e) => e.reads
  | some (.comb body) =>
      let tw := targetWins E.d2 body
      (rawReads body).filter fun r => !(tw.any fun W => r.overlaps W)
  | none => []

/-- Everything a process may read (for the independence reduction). -/
def Elab.reads (E : Elab) (q : Nat) : List ReadWin :=
  match E.procs[q]? with
  | some (.assign _ e) => e.reads
  | some (.comb body) => rawReads body
  | none => []

/-- What a process may write (for the "fed by another process" census). -/
def Elab.writes (E : Elab) (q : Nat) : List Win :=
  match E.procs[q]? with
  | some (.assign t _) => (t.windows? E.d2).getD []
  | some (.comb body) => targetWins E.d2 body
  | none => []

def Elab.applyInputs (E : Elab) (s : Store) (entry : SvState) : Store :=
  (E.decls.zip s).map fun (dc, v) =>
    if dc.isInput then
      match SvState.lookup entry dc.name with
      | some w => Val.ofLVec v.ty w
      | none => v
    else v

/-! ## Bodies as statement tables (the units of the preemptive policies) -/

inductive Node where
  | asg (t : Lhs2) (e : Expr2)
  | ifN (c : Expr2) (th : Nat) (el : Option Nat)
  | blk (cs : List Nat)
  | caseN (subj : Expr2) (inside : Bool) (arms : List (List Expr2 × Nat)) (dflt : Option Nat)
  | bad (msg : String)

def pushNode (n : Node) : StateM (Array Node) Nat := do
  let a ← get
  set (a.push n)
  pure a.size

partial def build : Stmt2 → StateM (Array Node) Nat
  | .blockingAssign t e => pushNode (.asg t e)
  | .nbaAssign _ _ => pushNode (.bad "9.2.2.2: nonblocking assignment in always_comb is outside E-core-0")
  | .ifStmt c t e => do
      let ti ← build t
      let ei ← match e with
        | some s => some <$> build s
        | none => pure none
      pushNode (.ifN c ti ei)
  | .block body => do
      let cs ← body.toList.mapM build
      pushNode (.blk cs)
  | .caseStmt subj items dflt inside _ => do
      let arms ← items.toList.mapM fun it => match it with
        | .mk pats b => do
            let bi ← build b
            pure (pats.toList, bi)
      let di ← match dflt with
        | some s => some <$> build s
        | none => pure none
      pushNode (.caseN subj inside arms di)
  | .unsupported k _ => pushNode (.bad s!"12: unsupported statement '{k}'")

inductive Item where
  | node (i : Nat)
  | pend (i : Nat) (v : LVec)

def Item.fp : Item → String
  | .node i => s!"n{i}"
  | .pend i v => s!"p{i}={v.toBinString}"

/-- Expand blocks at the head of a continuation (a block is not a unit). -/
partial def norm (tbl : Array Node) : List Item → List Item
  | .node i :: rest =>
      match tbl[i]? with
      | some (.blk cs) => norm tbl (cs.map Item.node ++ rest)
      | _ => .node i :: rest
  | k => k

def resStr {α : Type} : Res α → Except String α
  | .ok a => .ok a
  | .timeout => .error "evaluation timeout"
  | .unsupported m => .error s!"11: {m}"

def pickArm (st : SvState) (sv : LVec) (inside : Bool) :
    List (List Expr2 × Nat) → Except String (Option Nat)
  | [] => .ok none
  | (pats, b) :: rest => do
      let pvs ← resStr (evalPures2 st pats)
      if pvs.any (fun pv => caseHit inside sv pv) then pure (some b) else pickArm st sv inside rest

/-- One unit of an `always_comb` activation. `split`: a blocking assignment is two units (evaluate, then write). -/
def unit (E : Elab) (tbl : Array Node) (split : Bool) (s : Store) :
    List Item → Except String (Store × List Item)
  | [] => .ok (s, [])
  | .pend i v :: rest =>
      match tbl[i]? with
      | some (.asg t _) =>
          match staticWin E.d2 t with
          | some (n, lo, w) => .ok (E.writeWin s n lo (v.resizeU w), rest)
          | none => .error "10.4.1: blocking assignment target is not a static in-range window"
      | _ => .error "x2: a pending write without its assignment"
  | .node i :: rest =>
      match tbl[i]? with
      | some (.asg t e) =>
          match staticWin E.d2 t with
          | some (n, lo, w) => do
              let v ← resStr (evalPure2 (E.view s) e)
              if split then pure (s, .pend i v :: rest)
              else pure (E.writeWin s n lo (v.resizeU w), rest)
          | none => .error "10.4.1: blocking assignment target is not a static in-range window"
      | some (.ifN c th el) => do
          let cv ← resStr (evalPure2 (E.view s) c)
          pure (s, if cv.condTrue then .node th :: rest else
            match el with
            | some j => .node j :: rest
            | none => rest)
      | some (.blk cs) => .ok (s, cs.map Item.node ++ rest)
      | some (.caseN subj inside arms dflt) => do
          let st := E.view s
          let sv ← resStr (evalPure2 st subj)
          match ← pickArm st sv inside arms with
          | some j => pure (s, .node j :: rest)
          | none => pure (s, match dflt with
              | some j => .node j :: rest
              | none => rest)
      | some (.bad m) => .error m
      | none => .error "x2: no such statement"

/-! ## The prepared design -/

structure Prep where
  E : Elab
  sens : Array (List ReadWin)
  tbls : Array (Array Node)
  roots : Array Nat
  /-- `indep[q]`: no other process reads or writes what `q` writes, and none writes what `q` reads. Such a process
  commutes with every other move and is never woken by one, so running it first loses no closed store (a singleton
  ample set; the state graph of a slot is acyclic in the moves of `q`). -/
  indep : Array Bool

def Prep.ofElab (E : Elab) : Prep :=
  let built := E.procs.toList.map fun p => match p with
    | .comb b => Id.run ((build b).run #[])
    | .assign _ _ => (0, #[])
  let n := E.procs.size
  let ws := (List.range n).toArray.map E.writes
  let rs := (List.range n).toArray.map E.reads
  let wwOverlap (a b : List Win) : Bool := a.any fun (x, lo, w) => b.any fun W =>
    ReadWin.overlaps (.win x lo w) W
  let indep := (List.range n).toArray.map fun q =>
    (List.range n).all fun p => p == q ||
      (!(rs[p]!.any fun r => ws[q]!.any fun W => r.overlaps W) &&
       !(rs[q]!.any fun r => ws[p]!.any fun W => r.overlaps W) &&
       !wwOverlap ws[q]! ws[p]!)
  { E := E, sens := (List.range n).toArray.map E.sens,
    tbls := (built.map (·.2)).toArray, roots := (built.map (·.1)).toArray, indep := indep }

def Prep.trig (P : Prep) (st st' : SvState) : List Nat :=
  (List.range P.sens.size).filter fun q => (P.sens[q]!).any fun r => !decide (r.agree st st')

def Prep.isComb (P : Prep) (q : Nat) : Bool :=
  match P.E.procs[q]? with
  | some (.comb _) => true
  | _ => false

/-- Run an `always_comb` body's units to the end (`execBody`; no loops, so every node runs at most once and
`tbl.size + 2` units suffice). -/
def runBody (E : Elab) (tbl : Array Node) : Nat → Store → List Item → Except String Store
  | 0, _, _ => .error "x2: activation budget"
  | f + 1, s, k =>
      match norm tbl k with
      | [] => .ok s
      | k' => do
          let (s', k'') ← unit E tbl false s k'
          runBody E tbl f s' k''

/-- A whole activation (E-core-0's `activate`): an assign, or an `always_comb` body run to its end. -/
def Prep.activate (P : Prep) (q : Nat) (s : Store) : Except String Store :=
  match P.E.procs[q]? with
  | some (.assign t e) =>
      match t.windows? P.E.d2 with
      | some ws => do
          let v ← resStr (evalPure2 (P.E.view s) e)
          pure (P.E.writeWins s (v.resizeU (Win.sumWidth ws)) (Win.placed ws))
      | none => .error "10.3.2: continuous assignment target has no static window"
  | some (.comb _) =>
      let tbl := P.tbls[q]!
      runBody P.E tbl (tbl.size + 2) s [Item.node P.roots[q]!]
  | none => .error "4.5: no such process"

/-! ## Configurations and moves -/

structure Cfg where
  store : Store
  ready : List Nat
  running : List (Nat × List Item)
deriving Inhabited

def storeFp (s : Store) : String := ",".intercalate (s.toList.map fun v => v.bits.toBinString)

def Cfg.fp (c : Cfg) : String :=
  storeFp c.store ++ "|" ++ toString c.ready ++ "|" ++
    ";".intercalate (c.running.map fun (q, k) => s!"{q}:" ++ ",".intercalate (k.map Item.fp))

def sortNat (l : List Nat) : List Nat := (l.eraseDups).mergeSort (fun a b => decide (a ≤ b))

inductive Policy where
  | atomic | stmt | eval
deriving BEq, Inhabited

def Policy.name : Policy → String
  | .atomic => "atomic"
  | .stmt => "stmt"
  | .eval => "eval"

/-- The ready set after a move: the old ready set without the mover, plus every WAITING process the move's change
triggered (a running process is not waiting). -/
def nextReady (P : Prep) (c : Cfg) (q : Nat) (s' : Store) (running' : List (Nat × List Item)) : List Nat :=
  let t := P.trig (P.E.view c.store) (P.E.view s')
  let busy := running'.map (·.1)
  sortNat ((c.ready.erase q) ++ t.filter fun r => !busy.contains r)

def insertRun (q : Nat) (k : List Item) (l : List (Nat × List Item)) : List (Nat × List Item) :=
  ((q, k) :: l.filter (·.1 != q)).mergeSort (fun a b => decide (a.1 ≤ b.1))

/-- Every move from `c` under a policy: its label and the next configuration (or a refusal). -/
def moves (P : Prep) (pol : Policy) (c : Cfg) : List (String × Except String Cfg) :=
  let split := pol == .eval
  let fromReady : List (String × Except String Cfg) := c.ready.map fun q =>
    if !P.isComb q || pol == .atomic then
      ((if P.isComb q then "c" else "a") ++ toString q,
        (P.activate q c.store).map fun s' =>
          ({ store := s', ready := nextReady P c q s' c.running, running := c.running } : Cfg))
    else
      let tbl := P.tbls[q]!
      (s!"s{q}", (unit P.E tbl split c.store (norm tbl [Item.node P.roots[q]!])).map fun (s', k) =>
        let k' := norm tbl k
        let run' := if k'.isEmpty then c.running else insertRun q k' c.running
        ({ store := s', ready := nextReady P c q s' run', running := run' } : Cfg))
  let fromRun : List (String × Except String Cfg) := c.running.map fun (q, k) =>
    let tbl := P.tbls[q]!
    (s!"r{q}", (unit P.E tbl split c.store k).map fun (s', k2) =>
      let k' := norm tbl k2
      let run' := if k'.isEmpty then c.running.filter (·.1 != q) else insertRun q k' c.running
      ({ store := s', ready := nextReady P c q s' run', running := run' } : Cfg))
  let all := fromReady ++ fromRun
  -- the reduction: an independent process (ready or running) moves alone
  match (c.ready ++ c.running.map (·.1)).find? (fun q => P.indep[q]!) with
  | some q =>
      let lbls := [s!"a{q}", s!"c{q}", s!"s{q}", s!"r{q}"]
      all.filter fun (l, _) => lbls.contains l
  | none => all

structure Explored where
  /-- Each distinct closed store with the shortest schedule reaching it. -/
  closed : Array (Store × List String)
  states : Nat
  budget : Bool
  refusal : Option String

/-- Breadth-first exploration of every schedule of one slot, until `maxStates` configurations or the wall-clock
`deadline` (`IO.monoMsNow`); either stop marks the result `budget`. -/
def explore (P : Prep) (pol : Policy) (start : Cfg) (maxStates : Nat) (deadline : Nat) : IO Explored := do
  let mut seen : Std.HashSet String := {}
  let mut closedSeen : Std.HashSet String := {}
  let mut closed : Array (Store × List String) := #[]
  let mut queue : Array (Cfg × List String) := #[(start, [])]
  seen := seen.insert start.fp
  let mut i := 0
  let mut budget := false
  let mut refusal : Option String := none
  while i < queue.size do
    if i % 32 == 0 && (← IO.monoMsNow) > deadline then
      budget := true
      break
    let (c, path) := queue[i]!
    i := i + 1
    if c.ready.isEmpty && c.running.isEmpty then
      let f := storeFp c.store
      unless closedSeen.contains f do
        closedSeen := closedSeen.insert f
        closed := closed.push (c.store, path.reverse)
      continue
    for (lbl, r) in moves P pol c do
      match r with
      | .error m =>
          if refusal.isNone then refusal := some m
      | .ok c' =>
          let f := c'.fp
          unless seen.contains f do
            if seen.size ≥ maxStates then
              budget := true
            else
              seen := seen.insert f
              queue := queue.push (c', lbl :: path)
  return { closed := closed, states := seen.size, budget := budget, refusal := refusal }

/-- The canonical atomic run of one slot: always the lowest ready process (one legal Choice). -/
def runFifo (P : Prep) (c : Cfg) : Except String Store := Id.run do
  let mut c := c
  for _ in [0:100000] do
    match c.ready with
    | [] => return .ok c.store
    | q :: _ =>
        match P.activate q c.store with
        | .error m => return .error m
        | .ok s' => c := ({ store := s', ready := nextReady P c q s' [], running := [] } : Cfg)
  return .error "x2: the canonical run did not close within 100000 activations"

/-! ## Rows -/

def getF (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{name}'"

def getFOpt (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def parseEntry (d : Design2) (j : Json) : Except String SvState := do
  match j with
  | .obj kvs =>
      let mut st : SvState := []
      for (name, v) in kvs.toArray do
        let bits ← match v.getStr? with
          | .ok s => pure s
          | .error _ => .error s!"stimulus '{name}' is not a string"
        let some lv := LVec.ofString? bits
          | .error s!"stimulus '{name}': bad digits {bits}"
        let some dc := d.decls.find? (·.name == name)
          | .error s!"stimulus '{name}': not a declared signal"
        unless dc.isInput do .error s!"stimulus '{name}': not an input port"
        st := st ++ [(name, lv)]
      return st
  | _ => .error "stimulus entry is not an object"

/-- Load a row's design as `runner2.lean` does (parse, the defaults cross-check, the parameter point, `instantiateG2`
on an instance-free top). -/
def loadRow (envText : String) (paramsJ : Option Json) : Except String Design2 := do
  let (pd, lib) ← loadHierString envText
  unless lib.isEmpty do .error "hierarchical envelope (E-core-0 is one flat module)"
  match pd.crossCheck with
  | [] => pure ()
  | msgs => .error s!"crossCheck REFUSED: {String.intercalate " | " msgs}"
  let (pd, args) ← pd.atPoint <| pd.params.map fun p =>
    match paramsJ with
    | none => none
    | some pj =>
        match pj.getObjVal? p.name with
        | .ok v => v.getInt?.toOption
        | .error _ => none
  unless pd.int32Agrees args do .error "int32 disagreement at these parameters"
  match pd.instantiateG2 args (PDesign.surfaceFuel args) with
  | .ok d => pure d
  | .timeout => .error "instantiate2: generate fuel exhausted"
  | .unsupported m => .error s!"instantiate2: {m}"

def obs (P : Prep) (signals : List String) (s : Store) : String :=
  let v := P.E.view s
  " ".intercalate (signals.map fun n => s!"{n}={SvState.showSignal v n}")

def jstrs (l : List String) : Json := Json.arr (l.map Json.str).toArray

def procDesc (P : Prep) (q : Nat) : String :=
  let names := String.intercalate "," ((P.E.writes q).map (·.1)).eraseDups
  match P.E.procs[q]? with
  | some (.assign _ _) => "a" ++ toString q ++ ": assign " ++ names
  | some (.comb _) => "c" ++ toString q ++ ": always_comb writes " ++ names
  | none => toString q ++ ": ?"

/-- One row: the canonical run against Xcelium, then every slot under the three policies. -/
def runRow (row : Json) (maxStates : Nat) (rowMs : Nat := 30000) : IO Json := do
  let t0 ← IO.monoMsNow
  let name := (getF row "name" >>= fun j => j.getStr?).toOption.getD "?"
  let envPath := (getF row "envelope" >>= fun j => j.getStr?).toOption.getD ""
  let envText ← IO.FS.readFile ⟨envPath⟩
  let loaded : Except String (Prep × List SvState × List String × List String) := do
    let d ← loadRow envText (getFOpt row "params")
    let stim ← (← (← getF row "stimulus").getArr?).toList.mapM (parseEntry d)
    let signals ← (← (← getF row "signals").getArr?).toList.mapM (fun s => s.getStr?)
    let golden ← (← (← getF row "golden").getArr?).toList.mapM (fun s => s.getStr?)
    pure (Prep.ofElab (Elab.ofDesign2 d), stim, signals, golden)
  match loaded with
  | .error e => return Json.mkObj [("row", Json.str name), ("load", Json.str s!"REFUSED {e}")]
  | .ok (P, stim, signals, golden) =>
    let nProc := P.E.procs.size
    let combs := (List.range nProc).filter P.isComb
    let fed := combs.filter fun q =>
      (P.sens[q]!).any fun r => (List.range nProc).any fun p => p != q && (P.E.writes p).any fun W => r.overlaps W
    -- the slots: time zero (every process ready), then one slot per later stimulus entry
    let mut cur : Option Store := none
    let mut lines : List String := []
    let mut slots : Array Json := #[]
    -- an assign-only design has no procedural statement: every policy has exactly the atomic moves
    let noStmt := combs.isEmpty
    let mut verdict : Array (Policy × String) :=
      if noStmt then #[(.stmt, "no-statement"), (.eval, "no-statement")] else #[(.stmt, "invariant"), (.eval, "invariant")]
    let mut witness : Array Json := #[]
    let mut refused : Option String := none
    let mut k := 0
    for entry in stim do
      let start : Cfg := match cur with
        | none =>
            { store := P.E.applyInputs P.E.initStore entry, ready := List.range nProc, running := [] }
        | some s =>
            let s' := P.E.applyInputs s entry
            { store := s', ready := sortNat (P.trig (P.E.view s) (P.E.view s')), running := [] }
      match runFifo P start with
      | .error m =>
          refused := some m
          break
      | .ok sc =>
          let o := obs P signals sc
          lines := lines ++ [s!"CYCLE {k} {o}"]
          if noStmt then
            cur := some sc
            k := k + 1
            continue
          -- a time cap per row: past it, the remaining slots are not explored (an unsettled policy says "time")
          if (← IO.monoMsNow) - t0 > rowMs then
            for idx in [0, 1] do
              if verdict[idx]!.2 == "invariant" || verdict[idx]!.2 == "budget" then
                verdict := verdict.modify idx (fun (p, _) => (p, "time"))
            slots := slots.push (Json.mkObj [("cycle", toJson k), ("skipped_time", Json.bool true)])
            cur := some sc
            k := k + 1
            continue
          let A ← explore P .atomic start maxStates (t0 + rowMs)
          let aStores := A.closed.map (storeFp ·.1)
          let aObs := A.closed.map (obs P signals ·.1)
          let mut slotJ : List (String × Json) := [("cycle", toJson k), ("ready", toJson start.ready.length),
            ("atomic_closed", toJson A.closed.size), ("atomic_states", toJson A.states)]
          if A.budget then slotJ := slotJ ++ [("atomic_budget", Json.bool true)]
          for pol in [Policy.stmt, Policy.eval] do
            let idx := if pol == .stmt then 0 else 1
            -- once a policy has changed an observation its verdict is settled; and every `stmt` schedule is an
            -- `eval` schedule (evaluate and write back to back), so a `stmt` change in this slot is an `eval` change
            if verdict[idx]!.2 == "changes" then continue
            if pol == .eval && verdict[0]!.2 == "changes" then
              verdict := verdict.modify 1 (fun _ => (pol, "changes"))
              slotJ := slotJ ++ [("eval_implied_by_stmt", Json.bool true)]
              continue
            let X ← explore P pol start maxStates (t0 + rowMs)
            let xNew := X.closed.filter fun (s, _) => !aStores.contains (storeFp s)
            let xObsNew := X.closed.filter fun (s, _) => !aObs.contains (obs P signals s)
            slotJ := slotJ ++ [(s!"{pol.name}_closed", toJson X.closed.size), (s!"{pol.name}_states", toJson X.states),
              (s!"{pol.name}_new_stores", toJson xNew.size), (s!"{pol.name}_new_obs", toJson xObsNew.size)]
            if X.budget then slotJ := slotJ ++ [(s!"{pol.name}_budget", Json.bool true)]
            if let some m := X.refusal then slotJ := slotJ ++ [(s!"{pol.name}_refusal", Json.str m)]
            let prev := verdict[idx]!.2
            let nv :=
              if !xObsNew.isEmpty then "changes"
              else if !xNew.isEmpty then (if prev == "changes" then prev else "internal")
              else if X.budget then (if prev == "invariant" then "budget" else prev)
              else prev
            verdict := verdict.modify idx (fun _ => (pol, nv))
            -- the shortest witness of a changed observation, the first one per policy
            if !xObsNew.isEmpty && !(witness.any fun w => (w.getObjValD "policy").getStr?.toOption == some pol.name) then
              let best := xObsNew.foldl (fun (b : Option (Store × List String)) x =>
                match b with
                | none => some x
                | some y => if x.2.length < y.2.length then some x else some y) none
              if let some (s, path) := best then
                witness := witness.push (Json.mkObj [("policy", Json.str pol.name), ("cycle", toJson k),
                  ("schedule", jstrs path), ("obs", Json.str (obs P signals s)),
                  ("atomic_obs", jstrs aObs.toList)])
          slots := slots.push (Json.mkObj slotJ)
          cur := some sc
          k := k + 1
    let goldenAgree := refused.isNone && lines == golden
    let t1 ← IO.monoMsNow
    return Json.mkObj [("row", Json.str name), ("load", Json.str "ok"), ("ms", toJson (t1 - t0)),
      ("procs", toJson nProc), ("combs", toJson combs.length), ("fed_combs", toJson fed.length),
      ("proc_desc", jstrs ((List.range nProc).map (procDesc P))),
      ("refused", match refused with | some m => Json.str m | none => Json.null),
      ("golden_agree", Json.bool goldenAgree),
      ("model_cycles", jstrs lines),
      ("stmt", Json.str verdict[0]!.2), ("eval", Json.str verdict[1]!.2),
      ("witness", Json.arr witness), ("slots", Json.arr slots)]

end X2

open X2 in
def main (argv : List String) : IO UInt32 := do
  match argv with
  | path :: rest =>
      let txt ← IO.FS.readFile ⟨path⟩
      let rows ← match Json.parse txt >>= (·.getArr?) with
        | .ok a => pure a
        | .error e => throw (IO.userError e)
      let (lo, hi, budget) := match rest with
        | [a, b, c] => (a.toNat!, b.toNat!, c.toNat!)
        | [a, b] => (a.toNat!, b.toNat!, 4000)
        | _ => (0, rows.size, 4000)
      let out ← IO.getStdout
      for i in [lo:min hi rows.size] do
        let j ← runRow rows[i]! budget
        out.putStrLn s!"X2ROW {j.compress}"
        out.flush
      return 0
  | _ => do
      IO.eprintln "usage: X2Preempt.lean <batch.json> [<from> <to>]"
      return 1

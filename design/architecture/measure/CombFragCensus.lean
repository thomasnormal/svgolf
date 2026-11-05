/-
# The E-fragment coverage census (a measurement instrument)

    lake env lean --run svgolf/design/architecture/measure/CombFragCensus.lean <batch.json>   (integ1103's build;
                                                    `compile-measure.sh` typechecks it)

For every design of the batch (written by `combfrag_census.py batch`), at its DEFAULT parameter point: the envelope is
loaded as `runner2.lean` loads it (parse, the defaults cross-check, `PDesign.atPoint`, the `int32` agreement,
`instantiateG2`). The module's OWN processes are instantiated, with instances removed from its generate items, so that a
child module counts once, in its own row. For every `always_comb` process, three things are evaluated, and one
`CFE <json>` line is printed per design:
* L's `Stmt2.combOk d` (`CombFragE.lean`, ported to master's `CaseMode` at `6f1a68a6`): the body is in the E
  fragment, which admits a `case` only in E-core-0's modes (`caseModeInE0`: plain and `inside`);
* `qual`: the body holds a `unique`/`unique0`/`priority` case, so L's `Stmt2.claims` is a hypothesis of its meaning;
* `why`: the first construct that fails `combOk`, by a walk that mirrors `combOk` (checked against it: `agree`);
  after a `|`, the undeclared name, when that is the reason;
* `inside` and `zx`: the body holds a `case … inside`, or a `casez`/`casex` (outside the fragment).

The design-level columns: `single`, the elaborated design is exactly one `always_comb` process (L's
`activate_single` shape); `all_four`, every declaration is 4-state (`AllFour (Elab.ofDesign2 d)`, a hypothesis of
`Stmt2.sem_run` and `activate_single`; `Elab.ofDesign2` keeps `d.decls`); `design_has_unsupported`
(`Design2.hasUnsupported`, the test of svGolf's `design` stage). Imported by nothing; `partial def` only for the syntax
walks.
-/
import Lean
import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombFragE

open Lean (Json toJson)
open LeanModels.Sv LeanModels.Sv.Loop2

namespace CFE

partial def firstUnsup : Expr2 → Option String
  | .unsupported k _ => some k
  | .lit _ | .ident _ => none
  | .resizeSigned _ a | .squash2 a | .unary _ a | .slice a _ _ | .repl _ a | .reduce _ a | .resize _ a =>
      firstUnsup a
  | .binary _ l r | .scmp _ l r | .logical _ l r | .index l r _ => (firstUnsup l).orElse fun _ => firstUnsup r
  | .ternary c t f => ((firstUnsup c).orElse fun _ => firstUnsup t).orElse fun _ => firstUnsup f
  | .concat ps => ps.toList.findSome? firstUnsup

def whyExpr (d : Design2) (place : String) (e : Expr2) : Option String :=
  if e.wfB d then none
  else match firstUnsup e with
    | some k => some s!"{place}: unsupported expression {k}"
    | none => match e.idents.find? (fun x => !(d.symNames.contains x)) with
      | some x => some s!"{place}: undeclared name|{x}"
      | none => some s!"{place}: undeclared name"

def whyTarget (d : Design2) (t : Lhs2) : Option String :=
  if (Lhs2.staticWin d t).isSome then none
  else match t with
    | .concat _ => some "target: concatenation"
    | .index _ (.lit _) _ => some "target: constant element select out of range"
    | .index _ _ _ => some "target: dynamic element select"
    | .slice _ _ _ => some "target: part-select out of range"
    | .ident n => some s!"target: undeclared|{n}"

partial def whyStmt (d : Design2) : Stmt2 → Option String
  | .blockingAssign t e => (whyTarget d t).orElse fun _ => whyExpr d "assigned value" e
  | .nbaAssign _ _ => some "nonblocking assignment"
  | .ifStmt c a b => ((whyExpr d "if condition" c).orElse fun _ => whyStmt d a).orElse fun _ => b.bind (whyStmt d)
  | .block ss => ss.toList.findSome? (whyStmt d)
  | .caseStmt subj items dflt mode _ =>
      if !Kernel.caseModeInE0 mode then some "case mode: casez/casex" else
      (((whyExpr d "case subject" subj).orElse fun _ =>
        items.toList.findSome? fun it => match it with
          | .mk pats body => (pats.toList.findSome? (whyExpr d "case pattern")).orElse fun _ => whyStmt d body)
        ).orElse fun _ => dflt.bind (whyStmt d)
  | .unsupported k _ => some s!"statement: {k}"

partial def hasQual : Stmt2 → Bool
  | .ifStmt _ a b => hasQual a || (b.map hasQual).getD false
  | .block ss => ss.toList.any hasQual
  | .caseStmt _ items dflt _ chk =>
      chk != .none || items.toList.any (fun it => match it with | .mk _ b => hasQual b) || (dflt.map hasQual).getD false
  | _ => false

/-- Some `case` of the body has a mode `m` satisfies. -/
partial def hasMode (m : CaseMode → Bool) : Stmt2 → Bool
  | .ifStmt _ a b => hasMode m a || (b.map (hasMode m)).getD false
  | .block ss => ss.toList.any (hasMode m)
  | .caseStmt _ items dflt mode _ =>
      m mode || items.toList.any (fun it => match it with | .mk _ b => hasMode m b) ||
        (dflt.map (hasMode m)).getD false
  | _ => false

partial def stripInst : List GenItem → List GenItem
  | [] => []
  | .inst _ :: rest => stripInst rest
  | .genFor l g i b s c body :: rest => .genFor l g i b s c (stripInst body) :: stripInst rest
  | .genIf c t e :: rest => .genIf c (stripInst t) (stripInst e) :: stripInst rest
  | it :: rest => it :: stripInst rest

def kind : Process2 → String
  | .alwaysFF _ _ => "alwaysFF"
  | .alwaysPlain _ _ => "alwaysPlain"
  | .alwaysComb _ => "alwaysComb"
  | .assign _ _ => "assign"
  | .alwaysFFR _ _ _ => "alwaysFFR"
  | .unsupported k _ => "unsupported:" ++ k

def load (envText : String) : Except String (Design2 × Bool × Nat) := do
  let (pd, lib) ← loadHierString envText
  match pd.crossCheck with
  | [] => pure ()
  | m :: _ => .error s!"crossCheck: {m}"
  let (pd, args) ← pd.atPoint (pd.params.map fun _ => none)
  unless pd.int32Agrees args do .error "int32: a constant leaves the 32-bit range at the defaults"
  let hadInst := !GenItem.listInstFree pd.generates
  let pd' := { pd with generates := stripInst pd.generates }
  match pd'.instantiateG2 args (PDesign.surfaceFuel args) with
  | .ok d => pure (d, hadInst, lib.length)
  | .timeout => .error "instantiate: generate fuel exhausted"
  | .unsupported m => .error s!"instantiate: {m}"

def row (id grp envPath : String) : IO Json := do
  let txt ← IO.FS.readFile ⟨envPath⟩
  match load txt with
  | .error e => return Json.mkObj [("id", Json.str id), ("group", Json.str grp), ("load", Json.str s!"REFUSED {e}")]
  | .ok (d, hadInst, nlib) =>
      let ps := d.processes.toList
      let kinds := ps.map kind
      let mut combs : Array Json := #[]
      let mut k := 0
      for p in ps do
        match p with
        | .alwaysComb b =>
            let ok := b.combOk d
            let why := whyStmt d b
            combs := combs.push (Json.mkObj [("i", toJson k), ("ok", Json.bool ok), ("agree", Json.bool (ok == why.isNone)),
              ("why", match why with | some w => Json.str w | none => Json.null),
              ("qual", Json.bool (hasQual b)), ("inside", Json.bool (hasMode (· == .inside) b)),
              ("zx", Json.bool (hasMode (fun m => !Kernel.caseModeInE0 m) b))])
        | _ => pure ()
        k := k + 1
      let single := match ps with
        | [.alwaysComb _] => true
        | _ => false
      return Json.mkObj [("id", Json.str id), ("group", Json.str grp), ("load", Json.str "ok"),
        ("processes", toJson ps.length), ("kinds", Json.arr (kinds.map Json.str).toArray), ("combs", Json.arr combs),
        ("single", Json.bool single), ("had_instances", Json.bool hadInst), ("lib_modules", toJson nlib),
        ("design_has_unsupported", Json.bool d.hasUnsupported),
        ("all_four", Json.bool (d.decls.all fun dc => !dc.twoState))]

end CFE

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [path] =>
      let rows ← match Json.parse (← IO.FS.readFile ⟨path⟩) >>= (·.getArr?) with
        | .ok a => pure a
        | .error e => throw (IO.userError e)
      let out ← IO.getStdout
      for r in rows do
        let gs (k : String) : String := ((r.getObjVal? k) >>= (·.getStr?)).toOption.getD ""
        let j ← CFE.row (gs "id") (gs "group") (gs "envelope")
        out.putStrLn s!"CFE {j.compress}"
        out.flush
      return 0
  | _ => do
      IO.eprintln "usage: CombFragCensus.lean <batch.json>"
      return 1

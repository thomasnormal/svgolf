import Lean

/-!
# svGolf comparator (checker v0, Lean side)

    lake env lean --run check/Comparator.lean \
      --goal Submission.Goal --solution Submission.solution \
      --module Submission.Solution --prefix Submission \
      --allow propext,Classical.choice,Quot.sound [--bv-decide]

Run by `check.py` after the submission's modules compiled. It IMPORTS the
compiled modules with `loadExts := false`, so no code of the submission runs
in this process (environment-extension initializers of imported modules are
not executed), and then decides, from the kernel-level environment only:

1. **Exactly the task statement.** `--goal` is the generated, trusted
   `Submission.Goal : Prop` (`abbrev Goal := <Task>.Statement design.sem`, in
   the generated `Submission.Design`). The comparator asks the KERNEL to
   accept `theorem _svgolf_check : Goal := solution`: the kernel type-checks
   the reference to `--solution` against `Goal`, unfolding definitions as
   needed. The solution must be a `theorem`. It also reports whether the
   solution's declared type is syntactically `Goal` or `Goal`'s body. The
   kernel runs with the limits `leanchecker` uses (no heartbeat limit, no
   recursion-depth limit), so a proof that needed `set_option maxRecDepth`
   to elaborate is not refused here; `check.py` bounds the wall clock.
2. **Axioms.** It walks the solution's transitive dependencies through the
   constants' kernel values (it does NOT use the `#print axioms` cache, an
   environment extension a submission could populate) and collects every
   `axiom`. Each must be in `--allow`, or (with `--bv-decide`) a `bv_decide`
   axiom that point 6 RE-VERIFIES. `sorryAx`, `Lean.ofReduceBool`, a
   hand-written axiom of any other shape and `native_decide`'s axioms
   (`<decl>._native.native_decide.ax_*`) are rejected.
3. **No `extern` / `implemented_by`** on any constant of a module under
   `--prefix` (they only matter for compiled code, which a proof can reach
   through native evaluation; rejected outright).

4. **The toolchain is the toolchain** (WP-B review). Every loaded module whose root is
   `Init`, `Std`, `Lean` or `Lake` must resolve to the olean under the Lean installation's own
   `lib/lean`: Lean resolves a module root to the FIRST search-path entry that has a directory
   of that name, so a package build directory placed ahead of the toolchain could otherwise
   stand in for it, and point 5 takes the toolchain's constants as given.
5. **The dependency closure is replayed through the kernel** (WP-B review). The comparator
   trusts the oleans it imports, and since Mathlib and its packages are allowed in a submission
   those are files of a package checkout that a solution's own build (arbitrary code, v0 has no
   sandbox) could rewrite: an olean whose declaration was added with the kernel check switched
   off (`debug.skipKernelTC`, or `addDecl` in a `run_cmd`) carries `theorem evil : False` with
   no axiom anywhere in its value, which point 2 cannot see. So every constant the solution
   and the goal reach through types and values, minus what the toolchain provides and minus
   the submission's own modules (`leanchecker`'s job, below), is sent through the kernel
   (`Lean.Environment.replay`) on top of a fresh `Init`/`Std`/`Lean` environment. On the
   Mathlib fixture (`tests/imports/mathlib_band.lean`) that is 3,213 of the 7,938 constants
   of the closure and takes about 2.6 seconds; a closure with a planted `False` fails with
   the kernel's own error (`tests/checker/test_comparator.py`).

6. **`bv_decide` axioms can be re-verified** (WP-BV; DORMANT: `--bv-decide` is never passed by `check.py`
   while its `BV_DECIDE_SUPPORTED` is False, which is the case since the maintainers declined external solvers on
   2026-11-01, so without the flag every `bv_decide` axiom is rejected with a message that names the policy). A `bv_decide` proof ends in a tactic-generated axiom
   `<decl>._native.bv_decide.ax_<i>_<j> : verifyBVExpr E C = true` (`E`, `C` constants, `E` a closed
   `BVLogicalExpr`, `C` a string literal: the LRAT certificate), which the tactic added after
   evaluating `verifyBVExpr E C` by compiled code. Its name and shape prove nothing (a submission
   can declare an axiom of exactly that shape over a false certificate and derive `False`), so the
   comparator evaluates the statement ITSELF: it decodes `E` from its kernel value (a closed
   constructor term, read as `Expr` data: no submission code runs, nothing is evaluated through the
   submission's constants), checks that the toolchain's own `toExpr` of the decoded value is
   exactly that kernel value (so the decoder is not trusted, and anything that is not
   `toExpr` of a value is rejected), and runs the toolchain's compiled `verifyBVExpr` on it and on
   the string. The axiom is accepted iff that is `true`: then it is a TRUE theorem, so accepting
   it adds nothing to the logic. TRUSTED: the compiled LRAT checker, bitblaster and CNF
   conversion (`verifyBVExpr`, proved sound by `unsat_of_verifyBVExpr_eq_true`) as the tactic
   trusts them, and the toolchain's `ToExpr` instances of the reflection types; NOT trusted:
   CaDiCaL (a bad solver answer gives a certificate that fails here), the decoder, the axiom's
   name (a label: an axiom of another name is an ordinary axiom, rejected, and one of the
   generated name and shape is accepted exactly when its statement is true). A decoding
   budget (`--bv-max-nodes`) and a depth limit (`--bv-max-depth`) bound the work on a shared or
   deep term; the time and memory of the evaluation itself are bounded by the process's
   wall-clock and memory limits (`check.py`), and a limit hit is a rejection.

7. **A goal with the player's latency** (`--goal-arg NAME`; the `tx-family` kind, PLAN4 Gate 2,
   contract C3): the generated goal is then a function `Goal (lat : …) : Prop`
   (`Statement design.sem lat ∧ lat p₀ = n`, with the header's `n`) and the checked statement is
   `Goal NAME`, applied at the `Expr` level (nothing is parsed or elaborated in the solution's
   environment). `NAME` (`Submission.lat`) must be a definition (`def`/`abbrev`, not an axiom, an
   `opaque` or a theorem) without universe parameters; the kernel checks its type through the
   application, its closure is walked and replayed with the solution's.

Kernel replay of the submission's own declarations (catching a module that
added declarations without kernel checking) is `leanchecker`'s job; `check.py`
runs it on the same modules. Output: one line `SVGOLF_COMPARATOR <json>`; exit
status 0 iff accepted. The JSON also reports `imports` (the direct imports recorded in each
`--module`'s olean: what Lean itself read from the header, which `check.py` compares with its
own reading and with the allowlist), `toolchain_modules` and `replay`.
-/

open Lean

structure Args where
  goal : Name := .anonymous
  goalArg : Option Name := none
  solution : Name := .anonymous
  modules : Array Name := #[]
  prefixes : Array Name := #[]
  allow : Array Name := #[]
  bvDecide : Bool := false
  bvMaxNodes : Nat := 50000000
  bvMaxDepth : Nat := 500000

def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--goal" :: v :: rest, a => parseArgs rest { a with goal := v.toName }
  | "--goal-arg" :: v :: rest, a => parseArgs rest { a with goalArg := some v.toName }
  | "--solution" :: v :: rest, a => parseArgs rest { a with solution := v.toName }
  | "--module" :: v :: rest, a => parseArgs rest { a with modules := a.modules.push v.toName }
  | "--prefix" :: v :: rest, a => parseArgs rest { a with prefixes := a.prefixes.push v.toName }
  | "--allow" :: v :: rest, a =>
      parseArgs rest { a with allow := a.allow ++ ((v.splitOn ",").filter (· ≠ "")).toArray.map String.toName }
  | "--bv-decide" :: rest, a => parseArgs rest { a with bvDecide := true }
  | "--bv-max-nodes" :: v :: rest, a =>
      match v.toNat? with
      | some n => parseArgs rest { a with bvMaxNodes := n }
      | none => .error s!"--bv-max-nodes: not a number: {v}"
  | "--bv-max-depth" :: v :: rest, a =>
      match v.toNat? with
      | some n => parseArgs rest { a with bvMaxDepth := n }
      | none => .error s!"--bv-max-depth: not a number: {v}"
  | x :: _, _ => .error s!"unknown argument {x}"

/-- Every constant reachable from `roots` through types and values (theorem
values and opaque bodies included), and the subset that are axioms. Missing
constants are reported (they would make the walk incomplete). -/
partial def reach (env : Environment) (roots : Array Name) : NameSet × Array Name × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut todo : Array Name := roots
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => missing := missing.push n
    | some ci =>
        if ci matches .axiomInfo _ then axioms := axioms.push n
        for c in ci.getUsedConstantsAsSet do
          unless seen.contains c do todo := todo.push c
  return (seen, axioms, missing)

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?

/-- The module roots the toolchain itself provides (point 4). -/
def toolchainRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- The loaded toolchain modules whose olean is NOT under the installation's `lib/lean` (point 4),
and how many toolchain modules were checked. -/
def shadowedToolchain (env : Environment) (lib : System.FilePath) :
    IO (Array String × Nat) := do
  let libReal := (← IO.FS.realPath lib).toString ++ "/"
  let mut bad : Array String := #[]
  let mut n := 0
  for m in env.header.moduleNames do
    if toolchainRoots.contains m.getRoot then
      n := n + 1
      let p := (← IO.FS.realPath (← findOLean m)).toString
      unless libReal.isPrefixOf p do bad := bad.push s!"{m} -> {p}"
  return (bad, n)

/-- The direct imports recorded in the olean of module `m` (what Lean read from its header). -/
def importsOf (env : Environment) (m : Name) : Option (Array String) :=
  (env.header.moduleNames.findIdx? (· == m)).bind fun i =>
    env.header.moduleData[i]?.map fun d => d.imports.map (·.module.toString)

/-- Point 5. The constants of `closure` that the toolchain does not provide (`base` is a fresh
`Init`/`Std`/`Lean` environment) and that no submission module declares, sent through the
kernel on top of `base`. Returns the number replayed, and the error if the kernel (or the
replay's own consistency check of constructors and recursors) refuses one. -/
def replayClosure (env base : Environment) (closure : NameSet) (prefixes : Array Name) :
    IO (Nat × Option String) := do
  let mut m : Std.HashMap Name ConstantInfo := {}
  for n in closure.toList do
    unless base.contains n do
      let own := match moduleOf env n with
        | some mn => prefixes.any (·.isPrefixOf mn)
        | none => false
      unless own do
        if let some ci := env.find? n then m := m.insert n ci
  try
    let _ ← base.replay m
    return (m.size, none)
  catch e =>
    return (m.size, some (e.toString.take 600).toString)

/-! ### Point 6: re-verifying `bv_decide` axioms

The decoder reads a closed constructor term (`BVLogicalExpr`, as the toolchain's `ToExpr`
instances write it) off the kernel value of `E`. It is NOT trusted: whatever it returns is only
used if the toolchain's `toExpr` of it is, syntactically, the kernel value it was read from. -/

namespace BvRecheck

open Std.Tactic.BVDecide

/-- The decoder: `ReaderT` the maximum depth, `ExceptT` a reason, `StateM` the node budget left. -/
abbrev D := ReaderT Nat (ExceptT String (StateM Nat))

def tick (d : Nat) : D Unit := do
  if d > (← read) then throw "the expression is nested too deeply (--bv-max-depth)"
  let n ← get
  if n == 0 then throw "decoding budget exhausted: the expression is too large (--bv-max-nodes)"
  set (n - 1)

def fail {α} (what : String) (e : Expr) : D α :=
  throw s!"{what}: {(e.dbgToString).take 120}"

/-- A natural number as `toExpr` writes it: `OfNat.ofNat Nat n (instOfNatNat n)`. -/
def decNat (e : Expr) : D Nat :=
  match e with
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
      (.app (.const ``instOfNatNat []) (.lit (.natVal m))) =>
      if n == m then pure n else fail "malformed Nat literal" e
  | _ => fail "not a Nat literal" e

def decBitVec (w : Nat) (e : Expr) : D (BitVec w) := do
  match e.getAppFn, e.getAppArgs with
  | .const ``BitVec.ofNat [], #[wE, nE] =>
      if (← decNat wE) == w then pure (BitVec.ofNat w (← decNat nE)) else fail "BitVec width" e
  | _, _ => fail "not a BitVec literal" e

def decBinOp (e : Expr) : D BVBinOp :=
  match e with
  | .const ``BVBinOp.and [] => pure .and
  | .const ``BVBinOp.or [] => pure .or
  | .const ``BVBinOp.xor [] => pure .xor
  | .const ``BVBinOp.add [] => pure .add
  | .const ``BVBinOp.mul [] => pure .mul
  | .const ``BVBinOp.udiv [] => pure .udiv
  | .const ``BVBinOp.umod [] => pure .umod
  | _ => fail "not a BVBinOp" e

def decUnOp (e : Expr) : D BVUnOp := do
  match e with
  | .const ``BVUnOp.not [] => pure .not
  | .const ``BVUnOp.reverse [] => pure .reverse
  | .const ``BVUnOp.clz [] => pure .clz
  | .const ``BVUnOp.cpop [] => pure .cpop
  | .app (.const ``BVUnOp.rotateLeft []) n => return .rotateLeft (← decNat n)
  | .app (.const ``BVUnOp.rotateRight []) n => return .rotateRight (← decNat n)
  | .app (.const ``BVUnOp.arithShiftRightConst []) n => return .arithShiftRightConst (← decNat n)
  | _ => fail "not a BVUnOp" e

def decBinPred (e : Expr) : D BVBinPred :=
  match e with
  | .const ``BVBinPred.eq [] => pure .eq
  | .const ``BVBinPred.ult [] => pure .ult
  | _ => fail "not a BVBinPred" e

def decGate (e : Expr) : D Gate :=
  match e with
  | .const ``Gate.and [] => pure .and
  | .const ``Gate.xor [] => pure .xor
  | .const ``Gate.beq [] => pure .beq
  | .const ``Gate.or [] => pure .or
  | _ => fail "not a Gate" e

def decBool (e : Expr) : D Bool :=
  match e with
  | .const ``Bool.true [] => pure true
  | .const ``Bool.false [] => pure false
  | _ => fail "not a Bool" e

def castBV {a b : Nat} (h : a = b) (x : BVExpr a) : BVExpr b := h ▸ x

/-- A `BVExpr` together with its width (its index), read off its kernel term. -/
partial def decBV (d : Nat) (e : Expr) : D (Σ w, BVExpr w) := do
  tick d
  match e.getAppFn, e.getAppArgs with
  | .const ``BVExpr.var [], #[wE, iE] =>
      let w ← decNat wE
      let i ← decNat iE
      pure ⟨w, .var i⟩
  | .const ``BVExpr.const [], #[wE, vE] =>
      let w ← decNat wE
      let v ← decBitVec w vE
      pure ⟨w, .const v⟩
  | .const ``BVExpr.bin [], #[wE, lE, opE, rE] =>
      let w ← decNat wE
      let ⟨wl, l⟩ ← decBV (d + 1) lE
      let op ← decBinOp opE
      let ⟨wr, r⟩ ← decBV (d + 1) rE
      if hl : wl = w then
        if hr : wr = w then pure ⟨w, .bin (castBV hl l) op (castBV hr r)⟩ else fail "width mismatch" e
      else fail "width mismatch" e
  | .const ``BVExpr.un [], #[wE, opE, xE] =>
      let w ← decNat wE
      let op ← decUnOp opE
      let ⟨wx, x⟩ ← decBV (d + 1) xE
      if hx : wx = w then pure ⟨w, .un op (castBV hx x)⟩ else fail "width mismatch" e
  | .const ``BVExpr.append [], #[lE, rE, wE, lhsE, rhsE, _proof] =>
      let l ← decNat lE
      let r ← decNat rE
      let w ← decNat wE
      let ⟨wl, lhs⟩ ← decBV (d + 1) lhsE
      let ⟨wr, rhs⟩ ← decBV (d + 1) rhsE
      if hl : wl = l then
        if hr : wr = r then
          if h : w = l + r then pure ⟨w, .append (castBV hl lhs) (castBV hr rhs) h⟩
          else fail "append width" e
        else fail "width mismatch" e
      else fail "width mismatch" e
  | .const ``BVExpr.replicate [], #[owE, nwE, nE, xE, _proof] =>
      let ow ← decNat owE
      let nw ← decNat nwE
      let n ← decNat nE
      let ⟨wx, x⟩ ← decBV (d + 1) xE
      if hx : wx = ow then
        if h : nw = ow * n then pure ⟨nw, .replicate n (castBV hx x) h⟩ else fail "replicate width" e
      else fail "width mismatch" e
  | .const ``BVExpr.extract [], #[owE, startE, lenE, xE] =>
      let ow ← decNat owE
      let start ← decNat startE
      let len ← decNat lenE
      let ⟨wx, x⟩ ← decBV (d + 1) xE
      if hx : wx = ow then pure ⟨len, .extract start len (castBV hx x)⟩ else fail "width mismatch" e
  | .const ``BVExpr.shiftLeft [], #[mE, nE, lhsE, rhsE] =>
      let m ← decNat mE
      let n ← decNat nE
      let ⟨wl, l⟩ ← decBV (d + 1) lhsE
      let ⟨wr, r⟩ ← decBV (d + 1) rhsE
      if hl : wl = m then
        if hr : wr = n then pure ⟨m, .shiftLeft (castBV hl l) (castBV hr r)⟩ else fail "width mismatch" e
      else fail "width mismatch" e
  | .const ``BVExpr.shiftRight [], #[mE, nE, lhsE, rhsE] =>
      let m ← decNat mE
      let n ← decNat nE
      let ⟨wl, l⟩ ← decBV (d + 1) lhsE
      let ⟨wr, r⟩ ← decBV (d + 1) rhsE
      if hl : wl = m then
        if hr : wr = n then pure ⟨m, .shiftRight (castBV hl l) (castBV hr r)⟩ else fail "width mismatch" e
      else fail "width mismatch" e
  | .const ``BVExpr.arithShiftRight [], #[mE, nE, lhsE, rhsE] =>
      let m ← decNat mE
      let n ← decNat nE
      let ⟨wl, l⟩ ← decBV (d + 1) lhsE
      let ⟨wr, r⟩ ← decBV (d + 1) rhsE
      if hl : wl = m then
        if hr : wr = n then pure ⟨m, .arithShiftRight (castBV hl l) (castBV hr r)⟩ else fail "width mismatch" e
      else fail "width mismatch" e
  | _, _ => fail "not a BVExpr constructor application" e

def decPred (d : Nat) (e : Expr) : D BVPred := do
  tick d
  match e.getAppFn, e.getAppArgs with
  | .const ``BVPred.bin [], #[wE, lE, opE, rE] =>
      let w ← decNat wE
      let ⟨wl, l⟩ ← decBV (d + 1) lE
      let op ← decBinPred opE
      let ⟨wr, r⟩ ← decBV (d + 1) rE
      if hl : wl = w then
        if hr : wr = w then pure (.bin (castBV hl l) op (castBV hr r)) else fail "width mismatch" e
      else fail "width mismatch" e
  | .const ``BVPred.getLsbD [], #[wE, xE, iE] =>
      let w ← decNat wE
      let ⟨wx, x⟩ ← decBV (d + 1) xE
      let i ← decNat iE
      if hx : wx = w then pure (.getLsbD (castBV hx x) i) else fail "width mismatch" e
  | _, _ => fail "not a BVPred constructor application" e

partial def decLog (d : Nat) (e : Expr) : D BVLogicalExpr := do
  tick d
  match e.getAppFn, e.getAppArgs with
  | .const ``BoolExpr.literal [], #[.const ``BVPred [], p] => return .literal (← decPred (d + 1) p)
  | .const ``BoolExpr.const [], #[.const ``BVPred [], b] => return .const (← decBool b)
  | .const ``BoolExpr.not [], #[.const ``BVPred [], x] => return .not (← decLog (d + 1) x)
  | .const ``BoolExpr.gate [], #[.const ``BVPred [], g, x, y] =>
      let g ← decGate g
      let x ← decLog (d + 1) x
      let y ← decLog (d + 1) y
      return .gate g x y
  | .const ``BoolExpr.ite [], #[.const ``BVPred [], c, l, r] =>
      let c ← decLog (d + 1) c
      let l ← decLog (d + 1) l
      let r ← decLog (d + 1) r
      return .ite c l r
  | _, _ => fail "not a BoolExpr constructor application" e

/-- The generated name of a `bv_decide` axiom: `<decl>._native.bv_decide.ax_*`. -/
def isAxiomName : Name → Bool
  | .str (.str (.str _ "_native") "bv_decide") s => s.startsWith "ax_"
  | _ => false

/-- The operands `(E, C)` of an axiom of exactly the type `Eq.{1} Bool (verifyBVExpr E C) Bool.true`
(`E`, `C` constants), the shape `nativeEqTrue` gives it. Anything else is an error. -/
def axiomOperands (ci : ConstantInfo) : Except String (Name × Name) :=
  match ci with
  | .axiomInfo ai =>
    if ai.isUnsafe || !ai.levelParams.isEmpty then .error "an unsafe or universe-polymorphic axiom"
    else match ai.type with
      | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
          (.app (.app (.const ``Reflect.verifyBVExpr []) (.const eN [])) (.const cN [])))
          (.const ``Bool.true []) => .ok (eN, cN)
      | _ => .error "its type is not `verifyBVExpr E C = true` with `E` and `C` constants"
  | _ => .error "not an axiom"

/-- The value of the closed, safe definition `n`, whose type must be one of `tys`. -/
def defValue (env : Environment) (n : Name) (tys : List Expr) : Except String Expr :=
  match env.find? n with
  | some (.defnInfo di) =>
      if di.levelParams.isEmpty && di.safety == .safe && tys.any (· == di.type) then .ok di.value
      else .error s!"{n} is not a closed, safe definition of the expected type"
  | _ => .error s!"{n} is not a definition"

/-- `Reflect.verifyBVExpr`, behind a call that is not inlined, so that the evaluation happens where
it is asked for (and is timed there). -/
@[noinline] def runVerify (x : BVLogicalExpr) (c : String) : IO Bool :=
  pure (Reflect.verifyBVExpr x c)

structure Report where
  axiomName : Name
  nodes : Nat
  certBytes : Nat
  decodeMs : Nat
  verifyMs : Nat

def Report.json (r : Report) : Json :=
  Json.mkObj [("axiom", toJson r.axiomName.toString), ("nodes", toJson r.nodes),
    ("cert_bytes", toJson r.certBytes), ("decode_ms", toJson r.decodeMs),
    ("verify_ms", toJson r.verifyMs), ("verified", Json.bool true)]

/-- Re-verify the `bv_decide` axiom `ax`: `Except` the reason it is not accepted. -/
def recheck (env : Environment) (maxNodes maxDepth : Nat) (ax : Name) :
    IO (Except String Report) := do
  let some ci := env.find? ax | return .error "no such constant"
  match axiomOperands ci with
  | .error e => return .error e
  | .ok (eN, cN) =>
    match defValue env eN [mkConst ``BVLogicalExpr, mkApp (mkConst ``BoolExpr) (mkConst ``BVPred)],
          defValue env cN [mkConst ``String] with
    | .error e, _ => return .error e
    | _, .error e => return .error e
    | .ok eV, .ok cV =>
      let .lit (.strVal cert) := cV
        | return .error s!"the certificate {cN} is not a string literal"
      let t0 ← IO.monoMsNow
      let (r, left) := ((decLog 0 eV).run maxDepth).run.run maxNodes
      match r with
      | .error e => return .error s!"the formula {eN} is not a closed `BVLogicalExpr` constructor term: {e}"
      | .ok x =>
        -- the decoder is untrusted: its result stands only if the toolchain's own `toExpr` gives back
        -- exactly the kernel value
        if toExpr x != eV then
          return .error s!"the formula {eN} is not `toExpr` of the value read from it"
        let t1 ← IO.monoMsNow
        let ok ← runVerify x cert
        let t2 ← IO.monoMsNow
        unless ok do
          return .error s!"the LRAT certificate {cN} does not verify: `verifyBVExpr {eN} {cN}` evaluates to `false`"
        return .ok { axiomName := ax, nodes := maxNodes - left, certBytes := cert.utf8ByteSize,
                     decodeMs := t1 - t0, verifyMs := t2 - t1 }

end BvRecheck


def report (ok : Bool) (fields : List (String × Json)) : IO UInt32 := do
  IO.println s!"SVGOLF_COMPARATOR {(Json.mkObj (("accepted", Json.bool ok) :: fields)).compress}"
  return if ok then 0 else 1

unsafe def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => do IO.eprintln e; return 2
  let sysroot ← findSysroot
  initSearchPath sysroot
  let env ← importModules (args.modules.map fun m => { module := m }) {} (loadExts := false)
  let mut errors : Array String := #[]
  -- 4. the toolchain's modules come from the toolchain
  let (shadowed, toolchainChecked) ← shadowedToolchain env (← getLibDir sysroot)
  unless shadowed.isEmpty do
    errors := errors.push s!"modules of the Lean toolchain (Init/Std/Lean/Lake) resolve outside its installation: {shadowed.toList.take 5}"
  -- 1. the solution is a theorem, the goal a definition
  let sol? ← match env.find? args.solution with
    | some (.thmInfo ti) => pure (some ti)
    | some _ => do errors := errors.push s!"{args.solution} is not a theorem"; pure none
    | none => do errors := errors.push s!"no constant {args.solution}"; pure none
  let goalVal? ← match env.find? args.goal with
    | some (.defnInfo di) => pure (some di.value)
    | _ => do errors := errors.push s!"no definition {args.goal} (the generated goal)"; pure none
  -- 7. the goal applied to the player's latency definition (`--goal-arg`)
  let argOk ← match args.goalArg with
    | none => pure true
    | some n => match env.find? n with
      | some (.defnInfo di) =>
          if di.levelParams.isEmpty then pure true
          else do errors := errors.push s!"{n} must not have universe parameters"; pure false
      | some _ => do
          errors := errors.push s!"{n} must be a definition (`def` or `abbrev`: the latency the goal is applied to)"
          pure false
      | none => do
          errors := errors.push s!"no constant {n} (the solution must define the latency its header declares)"
          pure false
  let goalArgs : Array Expr := match args.goalArg with
    | some n => #[mkConst n]
    | none => #[]
  let goalType := mkAppN (mkConst args.goal) goalArgs
  let mut syntactic := false
  let mut kernelOk := false
  if let (some ti, some goalVal, true) := (sol?, goalVal?, argOk) then
    syntactic := ti.type == goalType || ti.type == goalVal.beta goalArgs
    -- (a) the constant, against the goal; (b) the solution's own proof term,
    -- against the goal (re-checks the top-level proof even if the constant
    -- was added without kernel checking; its dependencies are leanchecker's).
    for (tag, value) in [("constant", mkConst args.solution), ("proof term", ti.value)] do
      let decl := Declaration.thmDecl {
        name := `_svgolf_check, levelParams := ti.levelParams, type := goalType, value }
      -- maxHeartbeats 0, maxRecDepth 0: no limits, as `leanchecker`
      -- (`Lean.Environment.replay`) runs the kernel
      match env.addDeclCore 0 0 decl none with
      | .ok _ => pure ()
      | .error e =>
          errors := errors.push s!"the kernel rejects `theorem _ : {goalType} := <{tag} of {args.solution}>`: {(← (e.toMessageData {}).toString)}"
    kernelOk := errors.isEmpty
  -- 2. axioms
  let (closure, axioms, missing) := reach env (#[args.solution] ++ args.goalArg.toArray)
  for m in missing do errors := errors.push s!"dependency {m} is not in the environment"
  let mut badAxioms : Array Name := #[]
  let mut bvForbidden : Array Name := #[]
  let mut bvVerified : Array Json := #[]
  for ax in axioms do
    if args.allow.contains ax then continue
    -- 6. a `bv_decide` axiom is accepted only when re-verified here
    if BvRecheck.isAxiomName ax then
      if args.bvDecide then
        match ← BvRecheck.recheck env args.bvMaxNodes args.bvMaxDepth ax with
        | .ok r => bvVerified := bvVerified.push r.json
        | .error e => errors := errors.push s!"bv_decide axiom {ax} is not accepted: {e}"
      else
        bvForbidden := bvForbidden.push ax
      continue
    badAxioms := badAxioms.push ax
  unless badAxioms.isEmpty do
    errors := errors.push s!"axioms outside the allowed set {args.allow.toList}: {badAxioms.toList}"
  unless bvForbidden.isEmpty do
    errors := errors.push s!"`bv_decide` is not supported: it runs an external SAT solver (cadical), which the checker does not support (decided 2026-11-01); prove the goal with decide +kernel, omega, simp or a symbolic argument (svgolf/README.md, \"bv_decide\"): {bvForbidden.toList}"
  -- 3. extern / implemented_by under the submission prefixes (the constants of the modules
  -- under the prefixes, from their module data: not a walk over every imported constant, which
  -- is half a million with Mathlib)
  let mut native : Array Name := #[]
  let names := env.header.moduleNames
  for i in [0:names.size] do
    if args.prefixes.any (·.isPrefixOf names[i]!) then
      if let some d := env.header.moduleData[i]? then
        for n in d.constNames do
          if isExtern env n || (Compiler.getImplementedBy? env n).isSome then
            native := native.push n
  unless native.isEmpty do
    errors := errors.push s!"`extern`/`implemented_by` on submission constants: {native.toList}"
  -- 5. the dependency closure of the solution and the goal, through the kernel
  let (closureAll, _, _) := reach env (#[args.solution, args.goal] ++ args.goalArg.toArray)
  let base ← importModules (#[`Init, `Std, `Lean].map fun m => { module := m }) {} (loadExts := false)
  let t0 ← IO.monoMsNow
  let (replayed, replayErr) ← replayClosure env base closureAll args.prefixes
  let replayMs := (← IO.monoMsNow) - t0
  if let some e := replayErr then
    errors := errors.push s!"kernel replay of the dependency closure failed: {e}"
  let subConsts := closure.toList.filter fun n =>
    match moduleOf env n with
    | some m => args.prefixes.any (·.isPrefixOf m)
    | none => false
  report errors.isEmpty [
    ("solution", toJson args.solution.toString),
    ("goal", toJson args.goal.toString),
    ("goal_arg", toJson (args.goalArg.map (·.toString))),
    ("kernel_accepts", Json.bool kernelOk),
    ("syntactic_match", Json.bool syntactic),
    ("axioms", toJson (axioms.map (·.toString))),
    ("bv_decide", Json.mkObj [("allowed", Json.bool args.bvDecide), ("verified", Json.arr bvVerified)]),
    ("submission_constants_used", toJson subConsts.length),
    ("imports", Json.mkObj (args.modules.toList.map fun m =>
      (m.toString, toJson ((importsOf env m).getD #[])))),
    ("toolchain_modules", toJson toolchainChecked),
    ("replay", Json.mkObj [("closure", toJson closureAll.toList.length),
      ("replayed", toJson replayed), ("ms", toJson replayMs), ("ok", Json.bool replayErr.isNone)]),
    ("errors", toJson errors)]

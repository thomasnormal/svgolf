import Lean

open Lean
open Std.Tactic.BVDecide

/-! Prototype of the comparator's bv_decide re-check (WP-BV, G0). -/

namespace Bv

abbrev D := ExceptT String (StateM Nat)

def tick : D Unit := do
  let n ← get
  if n == 0 then throw "decoding budget exhausted (the expression is too large)"
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

/-- A `BVExpr` together with its width (the index), read off its kernel term. -/
partial def decBV (e : Expr) : D (Σ w, BVExpr w) := do
  tick
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
      let ⟨wl, l⟩ ← decBV lE
      let op ← decBinOp opE
      let ⟨wr, r⟩ ← decBV rE
      if hl : wl = w then
        if hr : wr = w then pure ⟨w, .bin (castBV hl l) op (castBV hr r)⟩ else fail "width mismatch" e
      else fail "width mismatch" e
  | .const ``BVExpr.un [], #[wE, opE, xE] =>
      let w ← decNat wE
      let op ← decUnOp opE
      let ⟨wx, x⟩ ← decBV xE
      if hx : wx = w then pure ⟨w, .un op (castBV hx x)⟩ else fail "width mismatch" e
  | .const ``BVExpr.append [], #[lE, rE, wE, lhsE, rhsE, _proof] =>
      let l ← decNat lE
      let r ← decNat rE
      let w ← decNat wE
      let ⟨wl, lhs⟩ ← decBV lhsE
      let ⟨wr, rhs⟩ ← decBV rhsE
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
      let ⟨wx, x⟩ ← decBV xE
      if hx : wx = ow then
        if h : nw = ow * n then pure ⟨nw, .replicate n (castBV hx x) h⟩ else fail "replicate width" e
      else fail "width mismatch" e
  | .const ``BVExpr.extract [], #[owE, startE, lenE, xE] =>
      let ow ← decNat owE
      let start ← decNat startE
      let len ← decNat lenE
      let ⟨wx, x⟩ ← decBV xE
      if hx : wx = ow then pure ⟨len, .extract start len (castBV hx x)⟩ else fail "width mismatch" e
  | .const ``BVExpr.shiftLeft [], #[mE, nE, lhsE, rhsE] =>
      let m ← decNat mE
      let n ← decNat nE
      let ⟨wl, l⟩ ← decBV lhsE
      let ⟨wr, r⟩ ← decBV rhsE
      if hl : wl = m then
        if hr : wr = n then pure ⟨m, .shiftLeft (castBV hl l) (castBV hr r)⟩ else fail "width mismatch" e
      else fail "width mismatch" e
  | .const ``BVExpr.shiftRight [], #[mE, nE, lhsE, rhsE] =>
      let m ← decNat mE
      let n ← decNat nE
      let ⟨wl, l⟩ ← decBV lhsE
      let ⟨wr, r⟩ ← decBV rhsE
      if hl : wl = m then
        if hr : wr = n then pure ⟨m, .shiftRight (castBV hl l) (castBV hr r)⟩ else fail "width mismatch" e
      else fail "width mismatch" e
  | .const ``BVExpr.arithShiftRight [], #[mE, nE, lhsE, rhsE] =>
      let m ← decNat mE
      let n ← decNat nE
      let ⟨wl, l⟩ ← decBV lhsE
      let ⟨wr, r⟩ ← decBV rhsE
      if hl : wl = m then
        if hr : wr = n then pure ⟨m, .arithShiftRight (castBV hl l) (castBV hr r)⟩ else fail "width mismatch" e
      else fail "width mismatch" e
  | _, _ => fail "not a BVExpr constructor application" e

def decPred (e : Expr) : D BVPred := do
  tick
  match e.getAppFn, e.getAppArgs with
  | .const ``BVPred.bin [], #[wE, lE, opE, rE] =>
      let w ← decNat wE
      let ⟨wl, l⟩ ← decBV lE
      let op ← decBinPred opE
      let ⟨wr, r⟩ ← decBV rE
      if hl : wl = w then
        if hr : wr = w then pure (.bin (castBV hl l) op (castBV hr r)) else fail "width mismatch" e
      else fail "width mismatch" e
  | .const ``BVPred.getLsbD [], #[wE, xE, iE] =>
      let w ← decNat wE
      let ⟨wx, x⟩ ← decBV xE
      let i ← decNat iE
      if hx : wx = w then pure (.getLsbD (castBV hx x) i) else fail "width mismatch" e
  | _, _ => fail "not a BVPred constructor application" e

partial def decLog (e : Expr) : D BVLogicalExpr := do
  tick
  match e.getAppFn, e.getAppArgs with
  | .const ``BoolExpr.literal [], #[.const ``BVPred [], p] => return .literal (← decPred p)
  | .const ``BoolExpr.const [], #[.const ``BVPred [], b] => return .const (← decBool b)
  | .const ``BoolExpr.not [], #[.const ``BVPred [], x] => return .not (← decLog x)
  | .const ``BoolExpr.gate [], #[.const ``BVPred [], g, x, y] =>
      let g ← decGate g
      let x ← decLog x
      let y ← decLog y
      return .gate g x y
  | .const ``BoolExpr.ite [], #[.const ``BVPred [], d, l, r] =>
      let d ← decLog d
      let l ← decLog l
      let r ← decLog r
      return .ite d l r
  | _, _ => fail "not a BoolExpr constructor application" e

end Bv

@[noinline] def runVerify (x : BVLogicalExpr) (c : String) : IO Bool := pure (Reflect.verifyBVExpr x c)

def axiomOperands (ci : ConstantInfo) : Except String (Name × Name) :=
  match ci with
  | .axiomInfo ai =>
    if ai.isUnsafe || !ai.levelParams.isEmpty then .error "unsafe or universe-polymorphic axiom"
    else match ai.type with
      | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
          (.app (.app (.const ``Reflect.verifyBVExpr []) (.const eN [])) (.const cN [])))
          (.const ``Bool.true []) => .ok (eN, cN)
      | _ => .error "type is not `Eq Bool (verifyBVExpr E C) true` with E, C constants"
  | _ => .error "not an axiom"

def defValue (env : Environment) (n : Name) (tys : List Expr) : Except String Expr :=
  match env.find? n with
  | some (.defnInfo d) =>
      if d.levelParams.isEmpty && (tys.any (· == d.type)) then .ok d.value
      else .error s!"{n}: not a closed definition of the expected type"
  | _ => .error s!"{n}: not a definition"

unsafe def main (argv : List String) : IO UInt32 := do
  if argv.head? == some "--depth" then
    let n := argv[1]!.toNat!
    let c := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (mkConst ``Bool.true)
    let mut y := c
    for _ in [0:n] do y := mkApp2 (mkConst ``BoolExpr.not) (mkConst ``BVPred) y
    let t0 ← IO.monoMsNow
    let (r, left) := (Bv.decLog y).run.run 100000000
    match r with
    | .error e => IO.println s!"depth {n}: {e}"
    | .ok x =>
      let t1 ← IO.monoMsNow
      let back := toExpr x
      IO.println s!"depth {n}: decoded in {t1-t0} ms, toExpr == original: {back == y}, nodes {100000000 - left}"
    return 0
  initSearchPath (← findSysroot)
  let mods := argv.map String.toName
  let env ← importModules (mods.toArray.map fun m => { module := m }) {} (loadExts := false)
  for m in mods do
    let some i := env.header.moduleNames.findIdx? (· == m) | continue
    let some d := env.header.moduleData[i]? | continue
    for n in d.constNames do
      let some ci := env.find? n | continue
      unless ci matches .axiomInfo _ do continue
      IO.println s!"== axiom {n}"
      match axiomOperands ci with
      | .error e => IO.println s!"   REJECT: {e}"
      | .ok (eN, cN) =>
        match defValue env eN [mkConst ``BVLogicalExpr, mkApp (mkConst ``BoolExpr) (mkConst ``BVPred)], defValue env cN [mkConst ``String] with
        | .error e, _ | _, .error e => IO.println s!"   REJECT: {e}"
        | .ok eV, .ok cV =>
          let .lit (.strVal cert) := cV | IO.println "   REJECT: cert is not a string literal"
          let t0 ← IO.monoMsNow
          let budget := 50000000
          let (r, left) := (Bv.decLog eV).run.run budget
          let t1 ← IO.monoMsNow
          match r with
          | .error e => IO.println s!"   REJECT (decode): {e}"
          | .ok x =>
            let back := toExpr x
            let t2 ← IO.monoMsNow
            if back != eV then IO.println "   REJECT: re-encoding differs"
            else
              let ok ← runVerify x cert
              let t3 ← IO.monoMsNow
              IO.println s!"   verified={ok} nodes={budget - left} cert_bytes={cert.utf8ByteSize} decode_ms={t1-t0} toExpr+cmp_ms={t2-t1} verify_ms={t3-t2}"
  return 0

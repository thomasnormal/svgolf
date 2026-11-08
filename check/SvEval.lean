import LeanModels.Sv.Ingest2
import SvGolf.TaskSeq

/-!
# `svgolf-eval`: ls-sv's own evaluation of a design on many input vectors

The ls-sv side of the checker's `postsynth` stage (`check/postsynth.py`).
Built by `lake build svgolf-eval` (the `[[lean_exe]]` in `lakefile.toml`, a
default target, and part of `check.py`'s `trusted` stage):

    .lake/build/bin/svgolf-eval ENVELOPE POINT VECTORS OUT [FUEL]

* `ENVELOPE` is the envelope the checker's `extract` stage wrote, the very
  file `Submission.Design`'s `load_design_sv2` loaded. It is parsed by the
  parser that command uses (`parseEnvelope2String`).
* `POINT` is the scoring point, `N=16` (or `""` for a parameterless top).
* The design evaluated is EXACTLY `design.sem` at that point, the design the
  proof is about: `load_design_sv2` defines `design.sem` as
  `PDesign.instantiateGD2 pd args` for an instance-free top and
  `PDesign.instantiateHD2 pd lib args` for a hierarchy, with `args` the
  parameter values as `Int.ofNat` in declaration order, and `semAt` below
  builds the same term.
* `VECTORS`: one vector per line, `name=HEX name=HEX ...`, every input port
  exactly once, each value fitting its port (checked against the
  instantiated design).
* `FUEL` (default 100000): `run2`'s fuel per run.

Per vector, ONE fresh one-cycle `run2` under `σ_src` and one under `σ_rev`
(no history between vectors). `OUT` gets header lines
`PORT <name> <in|out> <width>` and
`DESIGN <name> processes=<n> unsupported=<bool>`, then per vector either

    V <i> <out>=<bin> ... | <out>=<bin> ...

(the outputs after the cycle under `σ_src`, then under `σ_rev`; MSB-first
binary, `x`/`z` digits as such) or `E <i> <reason>` when a run does not
complete (`TIMEOUT`, `UNSUPPORTED ...`, `BADTRACE ...`), and a last line
`TIME ...`. The Python side treats every `E` line, every `x`/`z` digit and
every `σ_src`/`σ_rev` difference as a failure: it fails closed.

**Trace mode** (`svgolf-eval --trace [--start START] ENVELOPE POINT VECTORS OUT
[FUEL]`, the clocked post-synthesis check, PLAN4 Gate 2 step 4): the vectors are
the consecutive stimulus entries of ONE run over the whole list, one entry per
clock period (the clock port's value is not read). Line `V <c>` is then the
snapshot after cycle `c`, under `σ_src` and under `σ_rev`; a run that does not
complete is the single line `E 0 <reason>`. The run starts from:

* `--start zeros`: the power-up state with every declared signal 0 (txtask-v2's
  `run2At` from a `PowerUp` state; Verilator's `randReset(0)` start);
* `--start seed:<n>`: the power-up state whose bits are drawn, declaration by
  declaration and bit by bit from bit 0, from a 64-bit linear congruential
  generator seeded with `n` (`seedStart`);
* no `--start` (the default, txtask-v1): ls-sv's own start state `initState2`
  (declaration initializers, all else x), i.e. `run2`.

A `START <start>` line records which.

Exit status 0 = ran (the verdicts are in `OUT`); 1 = a usage, envelope,
instantiation or vector error.

Trust: this is compiled code running ls-sv's definitions (`run2`, the
instantiation) on the same envelope bytes; nothing in the `LeanModels.Sv`
closure it imports has `implemented_by`, `@[extern]` or `@[csimp]`. Its
gap to the kernel's `design.sem` is `toExpr` faithfulness (the elaborator
embeds the parsed envelope as a term) plus the compiler's correctness.
-/

open LeanModels.Sv

namespace SvGolf.Eval

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex? (s : String) : Option Nat :=
  if s.isEmpty then none else
  s.foldl (fun acc c => do let a ← acc; let d ← hexDigit? c; pure (a * 16 + d)) (some 0)

/-- `"N=16,M=2"` ↦ `[("N", 16), ("M", 2)]`. -/
def parsePoint (s : String) : Except String (List (String × Nat)) :=
  (s.splitOn ",").filter (· ≠ "") |>.mapM fun kv =>
    match kv.splitOn "=" with
    | [k, v] => match v.trimAscii.toString.toNat? with
      | some n => .ok (k.trimAscii.toString, n)
      | none => .error s!"bad point value in {kv}"
    | _ => .error s!"bad point entry {kv}"

/-- `design.sem` at the point: the design the proof is about (the term
`load_design_sv2` builds, `Ingest2.lean`). -/
def semAt (envl : Envelope2) (point : List (String × Nat)) : Except String Design2 := do
  let pd := envl.design
  let args ← pd.params.mapM fun p =>
    match point.lookup p.name with
    | some v => .ok (Int.ofNat v)
    | none => .error s!"the point gives no value for parameter '{p.name}'"
  for (k, _) in point do
    unless pd.params.any (·.name == k) do
      .error s!"the top has no parameter '{k}'"
  let flatTop := envl.lib.isEmpty || GenItem.listInstFree pd.generates
  return if flatTop then pd.instantiateGD2 args else pd.instantiateHD2 envl.lib args

def parseVec (d : Design2) (ln : String) : Except String SvState := do
  let toks := (ln.splitOn " ").filter (· ≠ "")
  let mut st : SvState := []
  for t in toks do
    match t.splitOn "=" with
    | [name, hx] =>
      let some n := parseHex? hx | .error s!"bad hex '{hx}'"
      let some dc := d.decls.find? (·.name == name) | .error s!"'{name}' is not declared"
      unless dc.isInput do .error s!"'{name}' is not an input port"
      unless n < 2 ^ dc.width do .error s!"'{name}': {hx} does not fit {dc.width} bits"
      if st.any (·.1 == name) then .error s!"'{name}' twice"
      st := st ++ [(name, LVec.ofNat dc.width n)]
    | _ => .error s!"bad token '{t}'"
  for dc in d.decls do
    if dc.isInput && !(st.any (·.1 == dc.name)) then
      .error s!"input '{dc.name}' not driven by the vector"
  return st

def showOuts (d : Design2) (st : SvState) : String :=
  " ".intercalate <| (d.decls.toList.filter (·.isOutput)).map fun dc =>
    s!"{dc.name}={SvState.showSignal st dc.name}"

/-- One fresh one-cycle run: the outputs after the cycle, or why there are none. -/
def runOne (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (v : SvState) :
    Except String String :=
  match run2 d σ fuel [v] with
  | .ok [st] => .ok (showOuts d st)
  | .ok tr => .error s!"BADTRACE {tr.length} snapshots for 1 cycle"
  | .timeout => .error "TIMEOUT run2 fuel exhausted"
  | .unsupported m => .error s!"UNSUPPORTED {m}"

/-- The power-up state with every declared signal 0. -/
def zeroStart (d : Design2) : SvState :=
  d.decls.toList.map fun dc => (dc.name, LVec.ofNat dc.width 0)

/-- One step of the 64-bit linear congruential generator (Knuth's MMIX constants). -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- The power-up state drawn from the seed `n`: each declaration in order, each bit from bit 0,
takes bit 33 of the next generator state. -/
def seedStart (d : Design2) (n : Nat) : SvState := Id.run do
  let mut s := lcg (n + 1)
  let mut st : SvState := []
  for dc in d.decls do
    let mut v := 0
    for i in List.range dc.width do
      s := lcg s
      if (s / 2 ^ 33) % 2 == 1 then v := v + 2 ^ i
    st := st ++ [(dc.name, LVec.ofNat dc.width v)]
  return st

/-- `--start`: `zeros`, `seed:<n>`; `none` is ls-sv's own start state. -/
def startState (d : Design2) : Option String → Except String SvState
  | none => .ok (initState2 d)
  | some "zeros" => .ok (zeroStart d)
  | some s => match s.splitOn ":" with
    | ["seed", n] => match n.toNat? with
      | some k => .ok (seedStart d k)
      | none => .error s!"bad seed in --start {s}"
    | _ => .error s!"bad --start {s} (zeros or seed:<n>)"

/-- `--trace`: ONE run of all the vectors as consecutive cycles from `st0` (`run2At`; `run2` is
`run2At` from `initState2`): the outputs after each cycle, or why there are none. -/
def runTrace (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (st0 : SvState)
    (vs : List SvState) : Except String (List String) :=
  match SvGolf.run2At d σ fuel st0 vs with
  | .ok tr => if tr.length == vs.length then .ok (tr.map (showOuts d))
              else .error s!"BADTRACE {tr.length} snapshots for {vs.length} cycles"
  | .timeout => .error "TIMEOUT run2 fuel exhausted"
  | .unsupported m => .error s!"UNSUPPORTED {m}"

end SvGolf.Eval

open SvGolf.Eval in
def main (argv : List String) : IO UInt32 := do
  let fail (m : String) : IO UInt32 := do IO.eprintln s!"svgolf-eval: {m}"; return 1
  let (trace, argv) := match argv with
    | "--trace" :: rest => (true, rest)
    | _ => (false, argv)
  let (start, argv) := match argv with
    | "--start" :: s :: rest => (some s, rest)
    | _ => (none, argv)
  let (envP, ptS, vecP, outP, fuel) ← match argv with
    | [e, p, v, o] => pure (e, p, v, o, 100000)
    | [e, p, v, o, f] => match f.toNat? with
      | some f => pure (e, p, v, o, f)
      | none => return (← fail s!"bad fuel {f}")
    | _ => return (← fail "usage: svgolf-eval [--trace [--start zeros|seed:N]] ENVELOPE POINT VECTORS OUT [FUEL]")
  let t0 ← IO.monoMsNow
  let envl ← match parseEnvelope2String (← IO.FS.readFile envP) with
    | .ok e => pure e
    | .error e => return (← fail s!"envelope {envP}: {e}")
  let point ← match parsePoint ptS with
    | .ok p => pure p
    | .error e => return (← fail e)
  let d ← match semAt envl point with
    | .ok d => pure d
    | .error e => return (← fail e)
  let t1 ← IO.monoMsNow
  let lines := ((← IO.FS.readFile vecP).splitOn "\n").filter (·.trimAscii.toString ≠ "")
  let mut stims : Array SvState := #[]
  for ln in lines do
    match parseVec d ln with
    | .ok st => stims := stims.push st
    | .error e => return (← fail s!"vector '{ln}': {e}")
  let mut out : Array String := #[]
  for dc in d.decls do
    if dc.isInput then out := out.push s!"PORT {dc.name} in {dc.width}"
    else if dc.isOutput then out := out.push s!"PORT {dc.name} out {dc.width}"
  out := out.push s!"DESIGN {d.name} processes={d.processes.size} unsupported={d.hasUnsupported}"
  let mut i := 0
  if trace then
    let st0 ← match startState d start with
      | .ok s => pure s
      | .error e => return (← fail e)
    out := out.push s!"START {start.getD "init"}"
    match runTrace d σ_src fuel st0 stims.toList, runTrace d σ_rev fuel st0 stims.toList with
    | .ok as, .ok bs =>
      for (a, b) in as.zip bs do
        out := out.push s!"V {i} {a} | {b}"
        i := i + 1
    | .error e, _ | _, .error e => out := out.push s!"E 0 {e}"
  else
    for v in stims do
      match runOne d σ_src fuel v, runOne d σ_rev fuel v with
      | .ok a, .ok b => out := out.push s!"V {i} {a} | {b}"
      | .error e, _ | _, .error e => out := out.push s!"E {i} {e}"
      i := i + 1
  let t2 ← IO.monoMsNow
  out := out.push s!"TIME instantiate_ms={t1 - t0} run_ms={t2 - t1} vectors={stims.size}"
  IO.FS.writeFile outP ("\n".intercalate out.toList ++ "\n")
  return 0

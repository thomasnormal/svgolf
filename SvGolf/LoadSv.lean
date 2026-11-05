import Lean
import LeanModels.Sv.Ingest2

/-!
# `load_sv`: load a SystemVerilog design straight from its `.sv` file

```lean
load_sv orGate from "tests/_example/negative/or_gate.sv"
load_sv orGate from "tests/_example/negative/or_gate.sv" (task := "tasks/_example")
load_sv orGate from "some/where/or_gate.sv" (top := "band") (probes := "N=1;N=16")
```

`load_sv name from "x.sv"` extracts the design AT ELABORATION TIME, through
svGolf's one extraction path (`check/envelope.py`: the source gate's canonical
text, then the pinned lean-surfaces extractor with the probe points), and then
elaborates exactly as `load_design_sv2 name from "<that envelope>"`: it defines
`name.pdesign`, `name`, `name.sem` (and `name.plib` for a hierarchy) and runs
every load-time gate of `load_design_sv2`, the multi-point cross-check on the
probe sidecar included. The extractor's output is never committed: it is a
cache under `.lake/envelopes/` (see `check/envelope.py`), keyed by the
canonical text, the arguments, the extractor's source and the pyslang version.

* The TOP module and the PROBE POINTS are, by default, the task's, read from
  `tasks/<name>/task.json` exactly as `check.py` reads them (its probe points
  plus the scoring and backstop points); the task is inferred from the path
  (`tasks/<name>/…` or `tests/<name>/…`), or named with `(task := "tasks/<name>")`.
* Outside a task, name the top with `(top := "…")`, and optionally the probe
  points with `(probes := "N=1;N=16")` (none by default).

Paths resolve against the current directory (the svGolf package root under
`lake build`); the svGolf root, where `check/envelope.py` lives, is the
current directory too unless `SVGOLF_ROOT` says otherwise. The interpreter is
`python3.12` unless `SVGOLF_PYTHON` says otherwise; it needs pyslang. A
missing interpreter, a missing pyslang or extractor, a refusal by the source
gate or the extractor, and every `load_design_sv2` refusal are elaboration
errors at the `load_sv` command, never silent.

Lake re-elaborates a module that uses `load_sv` when a design changes: the
`tests` library `needs` the `.sv` files of `tasks/` and `tests/`, the
extractor and `check/envelope.py` (`lakefile.toml`).
-/

namespace SvGolf.LoadSv

open Lean Elab Command

/-- One `(option := "value")` of `load_sv`: `task`, `top` or `probes`. -/
syntax loadSvOpt := " (" ident " := " str ")"

/--
`load_sv name from "design.sv"` extracts `design.sv` at elaboration time
(svGolf's extraction path: source gate, then the pinned extractor with the
task's probe points; cached under `.lake/envelopes/`) and elaborates exactly
as `load_design_sv2 name from "<the cached envelope>"`. Options:
`(task := "tasks/<name>")` (default: inferred from the path),
`(top := "…")` with optional `(probes := "N=1;N=16")` for a design outside a
task. See the module docstring of `SvGolf.LoadSv`.
-/
syntax (name := loadSv) "load_sv " ident " from " str (loadSvOpt)* : command

private def optValue (opt : Syntax) : Option (Syntax × String × Syntax) :=
  if opt[1].isIdent then some (opt[1], opt[1].getId.toString, opt[3]) else none

@[command_elab loadSv] def elabLoadSv : CommandElab := fun stx => do
  let nameStx := stx[1]
  let pathStx := stx[3]
  let some pathStr := pathStx.isStrLit?
    | throwErrorAt pathStx "load_sv: expected a string literal path"
  let mut extra : Array String := #[]
  let mut seen : List String := []
  for opt in stx[4].getArgs do
    let some (keyStx, key, valStx) := optValue opt
      | throwErrorAt opt "load_sv: malformed option (expected `(task := \"…\")`, `(top := \"…\")` or `(probes := \"…\")`)"
    let some val := valStx.isStrLit?
      | throwErrorAt valStx "load_sv: expected a string literal"
    if seen.contains key then
      throwErrorAt keyStx "load_sv: option `{key}` given twice"
    seen := key :: seen
    match key with
    | "task" => extra := extra ++ #["--task", val]
    | "top" => extra := extra ++ #["--top", val]
    | "probes" => extra := extra ++ #["--probe-points", val]
    | _ => throwErrorAt keyStx "load_sv: unknown option `{key}` (known: `task`, `top`, `probes`)"
  if seen.contains "task" && (seen.contains "top" || seen.contains "probes") then
    throwErrorAt stx "load_sv: `(task := …)` brings its own top and probe points; drop `top`/`probes`, or drop `task`"
  if seen.contains "probes" && !seen.contains "top" then
    throwErrorAt stx "load_sv: `(probes := …)` needs `(top := …)` (a task brings its own probe points)"
  let python := (← IO.getEnv "SVGOLF_PYTHON").getD "python3.12"
  let root : System.FilePath ← match ← IO.getEnv "SVGOLF_ROOT" with
    | some r => pure ⟨r⟩
    | none => IO.currentDir
  let script := root / "check" / "envelope.py"
  unless ← script.pathExists do
    throwErrorAt stx "load_sv: svGolf's extraction script '{script}' does not exist (the svGolf root is the current directory, '{← IO.currentDir}', unless SVGOLF_ROOT says otherwise; build from the svgolf/ package root)"
  let out ←
    match ← (IO.Process.output { cmd := python, args := #[script.toString, pathStr] ++ extra }).toBaseIO with
    | .ok o => pure o
    | .error e =>
        throwErrorAt stx "load_sv: could not run `{python}` ({toString e}); install Python 3.12 with pyslang, or point SVGOLF_PYTHON at an interpreter that has it"
  if out.exitCode != 0 then
    let what := if out.exitCode == 1 then "the design was REFUSED" else "extraction could not run"
    throwErrorAt pathStx "load_sv: '{pathStr}': {what} (`{python} {script} {pathStr}{String.join (extra.toList.map (" " ++ ·))}` exited {out.exitCode}):\n{out.stderr}"
  let envPath ←
    match Json.parse out.stdout >>= (·.getObjValAs? String "envelope") with
    | .ok p => pure p
    | .error e => throwErrorAt stx "load_sv: '{script}' printed no envelope path ({e}):\n{out.stdout}\n{out.stderr}"
  -- Elaborate exactly `load_design_sv2 name from "<envPath>"`; the literal
  -- carries the user's path position, so `load_design_sv2`'s errors point there.
  let lit := Syntax.mkStrLit envPath (SourceInfo.fromRef pathStx)
  let name : Ident := ⟨nameStx⟩
  let cmd ← `(command| load_design_sv2 $name from $(⟨lit⟩))
  withRef stx <| elabCommand cmd

end SvGolf.LoadSv

import LeanModels.Sv.Ingest2

/-!
# `run2` batch runner for the `add` task's validation (untrusted tooling)

    lake env lean --run tests/add/validate/Run.lean <envelope.sv.json> <jobs.txt>   (from svgolf/)

Driven by `validate.py`. Loads an sv-0.2 envelope at RUN time
(`parseEnvelope2String`) and, for each job line `N <vectors.txt> <out.txt>`,
instantiates the semantic tier at `N` exactly as `load_design_sv2`'s
`name.sem N` does for an instance-free top (`PDesign.instantiateGD2 [N]`).
For each line `a b cin` (decimal) of the vectors file it runs ONE cycle of
`run2` (a one-entry stimulus driving `a`, `b`, `cin` with known values at
their port widths) under the schedules `σ_src` and `σ_rev`, and writes one
line `s_src cout_src s_rev cout_rev` to the out file: each value a binary
string, MSB first, with `x`/`z` bits as such (`SvState.showSignal`), or
`TIMEOUT`/`UNSUPPORTED`/`BADTRACE` when the run does not complete with one
snapshot. Exit status 1 on a usage or envelope error.
-/

open LeanModels.Sv

namespace SvGolfAddValidate

/-- One cycle of `run2` on `d`, rendered as `s cout` (or a failure tag). -/
def runOne (d : Design2) (σ : ScheduleOracle) (stim : List SvState) : String :=
  match run2 d σ 100000 stim with
  | .ok [st] => s!"{SvState.showSignal st "s"} {SvState.showSignal st "cout"}"
  | .ok _ => "BADTRACE BADTRACE"
  | .timeout => "TIMEOUT TIMEOUT"
  | .unsupported _ => "UNSUPPORTED UNSUPPORTED"

def runJob (pd : PDesign) (n : Nat) (vecPath outPath : String) : IO Unit := do
  let d := pd.instantiateGD2 [(n : Int)]
  let lines := ((← IO.FS.readFile vecPath).splitOn "\n").filter (· ≠ "")
  let mut out : Array String := #[]
  for ln in lines do
    match (ln.splitOn " ").map String.toNat? with
    | [some a, some b, some ci] =>
        let stim : List SvState :=
          [[("a", LVec.ofNat n a), ("b", LVec.ofNat n b), ("cin", LVec.ofNat 1 ci)]]
        out := out.push s!"{runOne d σ_src stim} {runOne d σ_rev stim}"
    | _ => throw (IO.userError s!"bad vector line: {ln}")
  IO.FS.writeFile outPath (String.intercalate "\n" out.toList ++ "\n")

end SvGolfAddValidate

def main (args : List String) : IO UInt32 := do
  match args with
  | [envPath, jobsPath] =>
      let envl ← match parseEnvelope2String (← IO.FS.readFile envPath) with
        | .ok e => pure e
        | .error e => do IO.eprintln s!"ERROR: envelope {envPath}: {e}"; return 1
      unless envl.lib.isEmpty do
        IO.eprintln "ERROR: a hierarchical envelope (this runner instantiates flat tops only)"
        return 1
      let jobs := ((← IO.FS.readFile jobsPath).splitOn "\n").filter (· ≠ "")
      for j in jobs do
        match j.splitOn " " with
        | [ns, vec, out] =>
            let some n := ns.toNat? | do IO.eprintln s!"ERROR: bad N in job {j}"; return 1
            SvGolfAddValidate.runJob envl.design n vec out
        | _ => do IO.eprintln s!"ERROR: bad job line {j}"; return 1
      return 0
  | _ =>
      IO.eprintln "usage: lake env lean --run tests/add/validate/Run.lean <envelope.sv.json> <jobs.txt>"
      return 1

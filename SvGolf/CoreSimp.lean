import Lean

/-!
# `sv_core_simp`: the simp set the sv_comb tactics were written against (WP-B review)

Since 2026-11-01 (gate M) the tactics do not need this command: their own `simp` calls are `sv_simp`
(`LeanModels/Sv/CombCoreSimp.lean`), which erases the same package tags for the duration of the call. It remains
for a player whose OWN `simp` calls want core's simp set. What follows is the original finding.

Mathlib is allowed in a submission (README.md, "Mathlib in submissions"), and `import Mathlib.Tactic` adds
some 37,000 simp-set entries (58,112 lemmas in the set, against 20,570 without the packages). The `sv_comb`
tactics (`sv_structure`, `sv_equations`, `sv_norm`, ...) normalize their obligations with `simp only [...]`
followed by a plain `try simp`, the whole ambient simp set, so Mathlib changes what they leave. Measured on
the shipped references (2026-10-31): `Nat.cast_natAbs` turns the declared-range obligations into `|↑N + -1|`,
which `omega` cannot read (`add_n`, `add_proc`, `mul_n`, `mul_wallace` fail with `import
Mathlib.Tactic.Linarith` alone); `Order.add_one_le_iff` turns `x + 1 ≤ y` into `x < y`, a form
`sv_rowmajor` does not expect (`mul_n`, `mul_wallace` still fail after the first lemma is erased); with
both erased `sv_cover` meets `(1 + 1).toNat` and `mul_struct` runs out of heartbeats. Erasing lemmas one
at a time (`attribute [-simp] Nat.cast_natAbs`) is whack-a-mole: every Mathlib bump and every design can
need another. With `sv_core_simp` all seven references proved with the tactics are accepted unchanged
under `import Mathlib.Tactic` (`tests/run.py`, `attacks`: `mathlib_tactics_*`).

`sv_core_simp` removes, for the REST OF THE CURRENT SECTION (or file), every `@[simp]` tag that a module of
Mathlib or of one of the packages it imports (`corePackageRoots`, the same eight roots as `PACKAGE_ROOTS` in
`check.py`) added: lemmas those modules declare, core lemmas they re-tag, and their `@[simp]` definitions.
What is left is the simp set of Lean core, which is the one the tactics were tuned on. Mathlib's `ring`,
`linarith` and `positivity` do not read the simp set and work as before; a plain `simp` (yours or a
tactic's) and `norm_num` (whose simp call uses it, next to its own extensions) lose Mathlib's lemmas, which
`simp [Nat.cast_add]` can still name one by one.

    import Mathlib.Tactic
    import SvGolf.Comb

    sv_core_simp                    -- the sv tactics below see core's simp set

    section
    sv_core_simp                    -- or only for one theorem
    theorem mul_struct ... := by sv_structure ...
    end

The erasure is a modification of the extension's state in the current scope: a `section`/`namespace` that
ends restores the full set, and nothing is written into an olean (a solution is a leaf module). With no
package imported it removes nothing. It adds no axiom and no declaration: it cannot change what the
comparator and `leanchecker` accept, only which tactic scripts elaborate.
-/

namespace SvGolf

open Lean Meta Elab Command

/-- The module roots of Mathlib's package closure (`PACKAGE_ROOTS` in `check.py`;
`tests/imports/test_allowlist.py` keeps the two lists equal). -/
def corePackageRoots : List Name :=
  [`Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible, `ImportGraph, `LeanSearchClient]

/-- The simp origins that modules of `corePackageRoots` added: their lemmas, the lemmas of other modules
they re-tagged `@[simp]`, and the definitions they marked to be unfolded. -/
def packageSimpOrigins (env : Environment) : Array Origin := Id.run do
  let names := env.header.moduleNames
  let mut origins : Array Origin := #[]
  for i in [0:names.size] do
    if corePackageRoots.contains names[i]!.getRoot then
      for e in simpExtension.ext.getModuleEntries env i do
        let se : SimpEntry := match e with | .global a => a | .scoped _ a => a
        match se with
        | .thm t => origins := origins.push t.origin
        | .toUnfold n => origins := origins.push (.decl n)
        | .toUnfoldThms n _ => origins := origins.push (.decl n)
  return origins

/-- `sv_core_simp`: erase the package-added `@[simp]` tags from the current scope's simp set (see the
module docstring). Prints one line, `sv_core_simp: simp lemmas 58112 -> 20570` (the same count, unchanged,
when no package is imported). -/
elab "sv_core_simp" : command => do
  let env ← getEnv
  let count (e : Environment) : Nat := (simpExtension.getState e).lemmaNames.fold (fun n _ => n + 1) 0
  let origins := packageSimpOrigins env
  setEnv (simpExtension.modifyState env fun s => origins.foldl (fun s o => s.eraseCore o) s)
  logInfo m!"sv_core_simp: simp lemmas {count env} -> {count (← getEnv)}"

end SvGolf

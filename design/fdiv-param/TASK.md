# fdivP: the parametric floating-point division task (design note, WP-H1 gate 1)

Status: DRAFT, untrusted. Nothing here is applied to `SvGolf/**`, `spec/**`, `tasks/**` or the
checker. Everything below was compiled (see "Files" at the end).

## 1. The task

```systemverilog
module fdiv #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
```

`W` = width of the biased-exponent field, `P` = precision (significand digits including the
implicit bit), exactly the spec's `Format {w, p}`. The storage width is
`Format.k = 1 + w + (p - 1) = W + P`, so `K = W + P` and binary16 is `(5, 11)`, bfloat16 `(8, 8)`,
binary32 `(8, 24)`, binary64 `(11, 53)`. The function is the trusted
`divide ⟨W, P⟩ .roundTiesToEven` of `spec/IEEE754.lean` at that format (the very function
`fdiv16`/`fdiv32` instantiate), with the same canonical-NaN policy.

Statement (`Spec.lean` / `SpecLocal.lean`): for every `W ≥ 2`, `P ≥ 2`: the design has exactly
the input ports `a`, `b` and output port `q`, each `W + P` bits, no clocked process, every run
terminates, and every cycle that drives `a`, `b` with known values ends with
`q = divide ⟨W, P⟩ .roundTiesToEven a b`. That is `CombTask`'s three conjuncts, unchanged,
taken at every parameter pair.

## 2. What generalization of `CombTask` is needed

`CombTask` has ONE parameter `N : Nat`, and `CombTask.Statement` takes `sem : Nat → Design2`.
`load_design_sv2` already defines `name.sem : Nat → Nat → Design2` for a two-parameter module
(one explicit `Nat` binder per SV parameter, declaration order; checked on a toy two-parameter
module through `load_sv`, including the multi-point cross-check at
`W=2,P=2;W=5,P=11;W=3,P=4`, and the ports come out `W + P` wide at `(5,11)`, `(8,24)`,
`(11,53)`, `(2,2)`: `$SCRATCH/wph1/toy/Toy.lean`). So only the TASK STATEMENT needs a
second parameter.

Options considered:

| option | change to the trusted library | verdict |
|---|---|---|
| **C. a family of fixed-size tasks** (`SpecLocal.lean`) | **none** | **recommended now** |
| **A. `CombTask2`** (`Spec.lean`, `Task.lean.patch`) | +35 lines, purely additive, in `SvGolf/Task.lean` | recommended when a SECOND two-parameter task exists |
| B. pair `(W, P)` into one `Nat` (`Nat.unpair`) | none | rejected: the statement stops being about `design.sem` as loaded, and a bijection `Nat ≃ Nat × Nat` becomes trusted |
| D. a parameter LIST `List Nat` | rewrites `CombTask` and every task | rejected: widths become functions of a list, every existing proof changes |

### C: no change to `Task.lean` (smallest)

`CombTask.StatementFixed` is "the task at the one parameter value 0, whose interface and
function ignore `N`". A two-parameter task is a family of those, one per `(W, P)`:

```lean
def task (W P : Nat) : CombTask where
  inRange K := K = 0
  inputs _ := [("a", W + P), ("b", W + P)]
  outputs _ := [("q", W + P)]
  fn _ := fun (a, b, ()) => (fdivBits W P a b, ())

abbrev Statement (sem : Nat → Nat → LeanModels.Sv.Design2) : Prop :=
  ∀ W P, inRange W P → (task W P).StatementFixed (sem W P)
```

The statement is the trusted per-task `Spec.lean` (already trusted), and the checker's
`abbrev Goal : Prop := <constant> design.sem` works verbatim. EVERY helper of `SvGolf/Comb.lean`
applies unchanged to `task W P` at parameter `0` (`CombTask.satisfiedAt_of_comb`,
`SatisfiedAt.exists_run`, `not_computes_of_counterexample`).

### A: `CombTask2` (the proposed diff, NOT applied)

`design/fdiv-param/Task.lean.patch` (`diff -u SvGolf/Task.lean <patched copy>`, 35 added lines,
nothing deleted): a structure `CombTask2` with `inRange inputs outputs fn` each taking `(N M)`,
`CombTask2.atPoint t N M : CombTask` (the fixed-size task at the pair, defined by exactly the
three field projections above), `CombTask2.SatisfiedAt t N M d := (t.atPoint N M).StatementFixed d`
and `CombTask2.Statement t sem := ∀ N M, t.inRange N M → t.SatisfiedAt N M (sem N M)`.
`Spec.lean` is the task in this vocabulary. Same statement as C, with the concept named once;
`Comb2.lean` restates the three proof entry points in it (each is one line: the one-parameter
theorem at `t.atPoint N M`). I recommend waiting for a second user before taking it into the
trusted base: the trusted reading burden of C is zero lines beyond the task's own Spec.

Both forms compile (A in a scratch copy of the library, `SvGolfP`, C against the tree as is).
`SpecLocal.lean` also proves `statement_fdiv16 : Statement sem → Fdiv16.Statement (sem 5 11)`:
at binary16 the new task IS the old one (same ports, same function by `rfl`:
`fdivBits 5 11 a b = fdiv16 a b`, `fdivBits 8 24 a b = fdiv32 a b`), so a proof for all formats
subsumes the 16-bit goalpost.

### The function and the cast

`fn` must be total in `(W, P)` and the port widths are written `W + P`, while the spec's
`BitVec f.k` has width `1 + W + (P - 1)`. `fdivBits` transports along `k_eq : 1 + W + (P-1) = W + P`
with `BitVec.cast` (it leaves `toNat` unchanged, `fdivBits_toNat`) and is `0` out of range
(`2 ≤ W ∧ 2 ≤ P` is the spec's `Format.hw`/`Format.hp`; the statement never evaluates it there).
The alternative, writing the port widths as `(⟨W, P⟩ : Format).k` for a total `Format`
(`max W 2`, `max P 2`), puts the clamping into the interface, which is worse for the reader
and for the checker's width pins. If the spec ever defines `Format.k := w + p` the cast
disappears; that is a change to the trusted spec and is not proposed here.

## 3. `inRange`

`2 ≤ W ∧ 2 ≤ P`, nothing more: the spec's own well-formedness, no upper bound. The semantics
needs none (`divide` is defined, and its five properties are proved, for every format).
ls-sv evaluates `int` parameter arithmetic over the mathematical integers on its fast path
(`Param.lean`: the 32-bit wrap "is not modelled", `PDesign.int32Agrees` compares the exact
32-bit instantiation at the probe points), so a design with `2**W`-style constants is judged at
all `W`; the same situation as `add`'s unbounded `N`. A proof obligation needing the cap can
take a `W ≤ 30` fact from nowhere, so adding one WOULD be a real restriction: only add it if
the checker's Yosys scoring or the int32 cross-check made the unbounded statement
unprovable, which nothing in this phase suggests.

## 4. Non-vacuity discipline (kept)

* inputs distinct: `example (W P) : (((task W P).inputs 0).map Prod.fst).Nodup := by simp [task]`;
  with it `CombTask.SatisfiedAt.exists_run` applies at every pair (`Comb2.lean` restates it);
* an in-range witness: `inRange 5 11 ∧ inRange 8 8 ∧ inRange 8 24`;
* golden vectors through the task's own function, by kernel `decide`: binary16 `1/3 = 0x3555`,
  binary32 `1/3 = 0x3EAAAAAB`, bfloat16-like `(8,8)`: `1/3 = 0x3EAB`, `0/0` = `0x7E00`;
* `fdivBits_five_eleven`, `fdivBits_eight_twentyfour` (`rfl`): the instantiations are `fdiv16`
  and `fdiv32`; `statement_fdiv16` (task C).

## 5. What the checker needs for the task to be registered (nothing applied)

Measured by reading `check.py`, `check/envelope.py`, `check/postsynth.py`, `tests/run.py`:

* already multi-parameter: `task["parameters"]` is a list and the top module's parameters must
  be exactly that list in order (`check.py` line ~517); `scoring.params` and
  `backstop_points` are dicts; `parse_point("W=5,P=11")`, `-G` flags for Verilator, the
  `oracle(params, inputs)` interface, the generated `abbrev Goal := <constant> design.sem`;
* **one spot assumes a single parameter**: `tactics_probe_text` (`check.py`, the `--tactics`
  probe: `kind == "comb-family" and len(params) == 1`). It should emit
  `example (W P : Nat) : CombDesign (design.sem W P)` for n parameters; the probe is advisory;
* `README.md` line 288 documents `kind` as one parameter for `comb-family`: say "one or more";
* the oracle (`tasks/fdivp/oracle.py`) would wrap `spec/validate/oracle.py`'s format-general
  `Fmt(w, p)` / `div_exact` (exact rational arithmetic, any `w ≥ 2`, `p ≥ 2`) in place of
  `div_hw16`;
* `task.draft.json` (this directory) is a complete task.json in the checker's schema, with
  the banlist `/ % **`, probe points from `W=2,P=2` to `W=8,P=24`, the scoring point `(5, 11)`
  (the binary16 point, comparable with the fixed task) and backstops `(2,2)`, `(5,11)`, `(8,24)`.
  It is NOT registered (a `tasks/fdivp/` directory is picked up by `tests/run.py`).

## 6. Files

All under `svgolf/design/fdiv-param/` (compile commands in `$SCRATCH/wph1/LOG.md`):

| file | content | compiled |
|---|---|---|
| `Task.lean.patch` | proposed diff of `SvGolf/Task.lean` (option A), NOT applied | applied to a scratch copy, compiles |
| `Spec.lean` | `fdivp` task in the `CombTask2` vocabulary | against the scratch copy (`SvGolfP.Task`) |
| `SpecLocal.lean` | the same task, option C; needs no library change; `statement_fdiv16` | against the tree as it is |
| `Comb2.lean` | proof entry points for `CombTask2` (one-liners over `Comb.lean`) | against a scratch copy of `Comb.lean` |
| `task.draft.json` | the task.json for `tasks/fdivp/` | schema read, not run |

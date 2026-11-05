# The extractor writes a clean-looking envelope for a program slang rejects

> **Status (WP-RB1, 2026-11-01): implemented as proposed in section 3.** `extractors/sv/extract.py` carries `SlangError:<code>` (hunks: `_slang_error_nodes`, the
> `probed=False` keyword of `process_symbolic`, the use next to the `SlangAnalysis` block), register row `sa-slang-error`, `extractors/sv/test_slang_errors.py`;
> the two side observations of section 2 are resolved (the schema doc's `frontend_errors` sentence was wrong and is corrected; `check.py` says "slang reports the
> program illegal at the scoring point" for a pure slang error, pinned with the empty-banlist case by `svgolf/tests/checker/test_slang_errors.py`).
> The prototype's `SlangError:FrontendFailed` and the cap of 20 are as proposed; `proposal.diff` below is the prototype, the committed code differs in details only.

Follow-up of WP-RB0 (the `el2_ifu_compress_ctl` row of `CENSUS.md`): two slang errors, zero `Unsupported` nodes, and `load_design_sv2` loads it. Question: what exactly lands in
the envelope, which consumer notices, and what is the smallest fix against the ruling of 2026-11-01 ("if slang says the program is illegal, reject it").
Everything here is slot-free Python except two statements marked "by code" (the Lean side was read, not run). `envelope-errors/repro.py` regenerates the first table of section 2 and `envelope-errors/checkpy.sh` its two end-to-end rows;
`envelope-errors/proposal.diff` is the proposed extractor change, applied only to a scratch copy (nothing in `extractors/sv` or `check.py` was touched).

## 1. What lands in the envelope: nothing

Minimal repros (`envelope-errors/*.sv`; every case is a 3-line module `t` with `assign y = a;` plus the item named):

| case | the line that is illegal | slang error | what the extractor does |
|---|---|---|---|
| `c1_include` | `` `include "nonexistent.vh" `` | `CouldNotOpenIncludeFile` | exit 0, one stderr warning, **envelope identical to the clean control** (`c7_control`; spans and source hash ignored) |
| `c2_macro` | `` `NO_SUCH_MACRO `` at module level | `UnknownDirective` | same: identical to the control |
| `c4_import` | `import nopkg::*;` | `UnknownPackage` | same, except the envelope's `imports` list names `nopkg` (no `Unsupported`, no marker) |
| `c6_other_module` | a second module in the file reads an undeclared name | `UndeclaredIdentifier` | same: identical to the control |

The warning is the only trace: `warning: N compilation error diagnostic(s); extracting anyway (out-of-vocabulary nodes become Unsupported)`, on stderr, exit status 0
(`process_symbolic`, extract.py: the error count `nerr` feeds only that print and the four `*:invalid-compilation` markers for Division/Remainder/Power/Shift/implication).
The envelope has no `frontend_errors` field: that name exists only in the PROBE SIDECAR (`--probe-points`, one count per parameter point).

Not every slang error is silent. Where the error sits inside a construct the extractor converts, that construct itself becomes `Unsupported` (measured: `localparam int U = UNDEFINED + 1` ->
`InvalidExpression`; an unused `no_such_type_t v;` -> `VariableSymbol:type`; `assign y = a & undeclared;` -> `ContinuousAssignSymbol:InvalidExpression`; an elaboration `$error` ->
`ElabSystemTaskSymbol`). The silent class is exactly: errors that are not a converted construct (missing include, unknown macro, unknown package import, an error in another module
or file of the same sources, a package the top never uses). In the census this is `el2_ifu_compress_ctl` (error in an unused include of a generated config) and every VeeR row.

## 2. Consumers (`python3.12 envelope-errors/repro.py`, plus the end-to-end runs below)

| consumer | c1 include | c2 macro | c4 import | c6 other module | evidence |
|---|---|---|---|---|---|
| `extract.py --top` (default point) | proceeds, exit 0 | proceeds | proceeds | proceeds | measured |
| `extract.py --probe-points` (parametric twins `c4p`, `c6p`; c1/c2 not run this way) | - | - | sidecar `frontend_errors` 1 at both points | 1 at both points | measured |
| `load_design_sv2`, no sidecar | accepts | accepts | accepts | accepts | measured on the census row `el2_ifu_compress_ctl` (batch C: LOADED, `hasUnsupported = false`, 2 slang errors); `Ingest2.lean` has no field to read |
| `load_design_sv2`, with sidecar | refuses (`frontendRejects`) | refuses | refuses | refuses | by code: `Ingest2.lean:740` reads `frontend_errors`, `Probe2.lean:642` returns `.frontendRejects`, `ok = false`, the elab throws; NOT run (no slot) |
| `Design2.hasUnsupported` / `firstLoud` | false | false | false | false | nothing in the envelope to be loud; `PDesign.others` is the route, and it is empty |
| svGolf source gate | REJECT (directive) | REJECT (directive) | accepts | accepts | measured |
| `check/envelope.py` (the checker's extract stage and `load_sv`) | exit 0, path printed, stderr dropped | same | same | same | measured on c4 (`envelope.py ... --top t`: exit 0); `extract()` refuses only on non-zero exit or a missing envelope |
| `banlist.front_check` (non-empty banlist) | REJECT | REJECT | REJECT | REJECT | measured (slang errors are `diagnostics`) |
| banlist with an EMPTY banlist | accepts | accepts | accepts | accepts | measured: `banlist.check(ops=[])` returns `passed: True` before compiling; `check.py` has `if ops:` |
| `fourstate.slang_check` | REJECT | REJECT | REJECT | REJECT | measured |
| `check.py` end to end, task `add` + `import nopkg::*;` in `add_n` | - | - | rejected at stage **banlist**: `slang error UnknownPackage` (and Yosys: syntax error at the `::`) | - | measured by `envelope-errors/checkpy.sh`; the extract stage had exit 0 and the sidecar `frontend_errors = 1` at every probe point (N = 1, 2, 3, 16, 32, 64); the same text is also unreadable for Yosys (an independent reason) |
| the same with a copy of `add` whose banlist is empty | - | - | banlist stage passes; rejected at stage **fourstate** | - | measured by `envelope-errors/checkpy.sh` (slang error and Yosys error both reported) |

Reading of the table:
* **svGolf's checker is closed**, by three overlapping nets: the source gate (directives), fourstate (always runs, at the scoring point), banlist (when the task bans an operator), and for a
  parametric task the sidecar's per-point `frontend_errors`, which `load_design_sv2` enforces in the design stage. None of them is the extractor; each recomputes slang's verdict.
* **ls-sv alone is open.** `load_design_sv2` on an envelope with no sidecar has nothing to refuse. That is every `Examples/` fixture, every direct use of the loader, and WP-RB0-style
  verification of real cores (multi-file, `-I`, no gate, no task). Also `load_sv` in a player's proof file without `(task := ...)`/`(probes := ...)`: it elaborates a design from a program
  slang rejects, and the warning never reaches the player (stderr is discarded on exit 0).
* The weak point for the soundness story is the third case: a theorem about `X.sem` where `X` came from an illegal program is a theorem about slang's error RECOVERY of it (here: the program with
  the failed include silently dropped), not about the file.

Two side observations from the same runs:
1. `docs/sv-envelope-schema.md` (line ~2947) says the sidecar's `frontend_errors` does not count "errors of modules the top does not instantiate". `c6p_other_module` (an uninstantiated module
   with an undeclared name, top alone via `topModules`) measures `frontend_errors = 1` at both points, and `banlist.front_check` / `fourstate.slang_check` also report it. slang
   diagnoses unused definitions; the doc sentence is wrong for that shape (or the intent differs from the implementation: pick one).
2. `fourstate` reports a pure slang diagnostic under the header "an x or z value can arise in the design at the scoring point" (`checkpy.sh`, second run): the verdict is right, the wording is not.

## 3. Proposal

**Where: the extractor, as a marker, the exact twin of `SlangAnalysis:*`.** The extractor is the only party that sees the slang diagnostics when it writes the envelope, and every consumer of an envelope
(Lean loader, `hasUnsupported`, the checker's design stage, `load_sv`, direct use) already honours `Unsupported` nodes in `module.others`: `Ingest2.parseModule2` routes them to `PDesign.others`,
instantiation turns them into loud unsupported processes (`Param.lean:2250`), so a run never completes and `hasUnsupported` is true. Nothing in Lean or in svGolf changes.

The change (`envelope-errors/proposal.diff`, 3 hunks, about 45 lines in `extract.py`):
* `_slang_error_list(comp, sm)`: the error diagnostics of the default-point compilation (`getAllDiagnostics`, what `nerr` already counts), with slang's own code name, message and `file:line`;
  fails closed (`FrontendFailed`) if the list cannot be built.
* `_slang_error_nodes`: one `Unsupported` per distinct error (at most 20), kind `SlangError:<slang code>`, text `file:line: message`.
* In `process_symbolic`, next to the analysis block, and under the same rule: `if nerr and (not _top_is_parametric(module) or not _SYM_PROBED)`, append them to `module["others"]`.
  `_SYM_PROBED` is set by `main()` when `--probe-points` was given. So: a top without parameters carries its errors as nodes (one point, one verdict); a top with parameters and a sidecar keeps the
  per-point verdict it has today (the default-point envelope must stay instantiable where the default point is the illegal one, the reason the analysis path gave); a top with parameters and NO
  sidecar, which nothing else can vouch for, carries the nodes. The probe run itself (`_SYM_PARAM_OVERRIDES` set) is untouched.

Measured on the prototype (scratch copy of `extractors/sv`, nothing committed to it):
* the four repros each gain exactly one node (`SlangError:CouldNotOpenIncludeFile`, `UnknownDirective`, `UnknownPackage`, `UndeclaredIdentifier`), the control and the sidecar runs gain nothing
  (`repro.py` last column / last four lines);
* `python3.12 -m unittest discover -s extractors/sv`: **2253 tests, OK (8 skipped), same as the unpatched copy** (CI step `sv-extractor-tests`);
* `tools/gen_sv_refusals.py --check` FAILS on the prototype: `extractor kind 'SlangError:*' (symbolic mode, 1 site(s)) is not in the register`. So the register row below is part of the change, not an afterthought;
* blast radius on shipped inputs: of 1501 `.sv` files under `Examples/system-verilog`, `harness/sv`, `svgolf/{tasks,tests,design}`, only 16 are slang-illegal as single files: 13 `Examples/*_refuse`
  fixtures (they exist to be refused) and 3 testbenches under `svgolf/tests` and `svgolf/design/always-comb` (never extracted with `--top`).

Not measured (no slot): the Lean side of the marker (`hasUnsupported`/`firstLoud` on a marked envelope, and whether any `Examples/*_refuse/*.lean` pins the exact first loud message of those 13 fixtures).
The route is the one `SlangAnalysis:*` and the census rows with assertion nodes already use (`ot_prim_onehot_mux@wa3` loads with `hasUnsupported = true`, first loud node an `assert property`).

**Register row.** New row `sa-slang-error` (proposed, `proposed: true` until the maintainers confirm), layer extractor, category `never`, tag `SlangError:*`, trigger `` `include "missing.vh" `` / an unknown macro / `import nopkg::*;` /
an undeclared name in a second module of the same sources, principle `P-SAME-PROGRAM`, policy "If slang reports a program illegal, that is a good reason to reject it" (decided 2026-10-31) and the
2026-11-01 amendment ("parse, elaboration AND ANALYSIS errors"), sibling of `sa-slang-analysis` (the analysis half of the same ruling) and of `ex-op-invalid-compilation` (the four operators
that already refuse "in a compilation with errors"). `where`: `process_symbolic`, `_slang_error_nodes`. The schema doc's tag table (`docs/sv-envelope-schema.md` near line 100) gets the
`SlangError:<slang code>` line next to `SlangAnalysis:<slang code>`. Test: a twin of `extractors/sv/test_slang_analysis.py` over the four shapes above plus the parametric-with-sidecar and
parametric-without-sidecar cases (the repro's last four lines are its oracle).

**Alternatives considered, and why not.**
* *Loader gate* (an envelope field with the default-point error count, refused in `load_design_sv2`): a schema change, a Lean change and a re-pin of every envelope for the same effect; the marker needs none.
* *Checker only* (make `check/envelope.py` refuse on the warning line, or run slang itself): closes `load_sv` and the extract stage, but svGolf is already closed (section 2), and ls-sv alone, where the hole is,
  stays open. It also parses a human-readable warning.
* *Non-zero exit from `extract.py` on any slang error*: the cheapest, and wrong: the census drivers (`extractors/sv/census.py`, `cv32e40p_census.py`) and the "extracting anyway" contract deliberately extract
  partial compiles, and a consumer that wants the partial envelope could no longer get it.

**Residual gaps, stated.** (a) A parametric top extracted WITH a sidecar has no default-point verdict beyond the per-point counts (by design, as for analysis errors). (b) An error slang only raises at a
non-default point of a parametric top extracted without probe points cannot be seen by anyone. (c) The marker is deliberately strict: errors in any module or file of the same compilation refuse the
top (c6), which is also what banlist and fourstate do; narrowing it to errors in the top's own files would need a reachability notion the extractor does not have, and is not proposed.
(d) What slang's error RECOVERY means for the rest of the program is exactly what the marker declines to answer.

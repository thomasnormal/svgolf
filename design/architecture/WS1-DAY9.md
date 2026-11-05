# WS1 (authority: E-core, R-COMB, R-EDGE, R-DESIGN2): Day-9 write-up

Agent A, branch `arch-x1` at `bebc7f65`. Claim labels as in `TASKV2-REVIEW.md` (on `svgolf-prep`); "derived from E" only for chains with no
`run2` constant (NoRun2): **MEASURED** (proved
and compiled, or counted), **READ** (taken from a file), **JUDGED** (our estimate). Details:
`X1-NOTE.md` §7–§12.

Applies to every row below (MEASURED):
- No `sorry`, `admit`, `native_decide` or `bv_decide`.
- Every headline theorem is pinned by `#print axioms`, within `[propext, Classical.choice, Quot.sound]`.
- Line counts are `wc -l` of the whole file, including documentation.
- No pre-existing module imports a new one, and nothing trusted in `svgolf` imports any of it.
- The `LeanModels/Sv` files build with targeted `lake build`, the `svgolf/design/architecture` ones
  with `compile-obsE.sh`.

## 1. What is proved

| Item | Files (lines) | Commits | Label | Headline results |
|---|---|---|---|---|
| E-core-0: assigns, then `always_comb` (one activation per body); fidelity fixes | `Kernel/Core0.lean` (841) | `0e4aa7a0` `c279523c` `33dc39c8` `2d4cdd55` | trusted definitions (the authority) | `exec_sound`, `step_legal`; sensitivity keeps unwritten bits of a partly written read (LRM 9.2.2.2.1); violated `unique`/`priority` refuses loudly (12.5.3) |
| G-A: R-COMB-0, assign-only | `Core0Comb.lean` (984) | `1d28a0ee` `92c5e25d` | derived from E; `closed_eq_combSettle2` transport | `Settles.rcomb`, `schedule_independent`, `closed_eq_combSettle2`, `combEqs_unique` |
| G-B: `always_comb` through R-BODY and the process lowering | `Core0Proc.lean` (826) | `dcc95d55` | derived from E; `rcomb1`'s `combSettle2` half transport | `rcomb1`, `Settles.ofLower`; fixture `mux1` |
| R-DESIGN2, comb slice | `Core0Obs.lean` (1,055) | `ddbb66cc` `d00b2919` | transport theorem | `included_E0_run2_lower`; `included_run2_E0_of_typed` (typed stimuli); `not_included_run2_E0` (the untyped converse is false) |
| `CombTask` and 3 accepted records moved to E-core-0 | `ObsCombE.lean` (163), `ObsCombEExample.lean` (60), `ObsCombEAdd.lean` (39) | `4247e13d` `d00b2919` | transport theorem (the instances too) | `statement_E0`, `example_E0`, `add_E0` |
| R-COMB-1: the window rank | `Core0Win.lean` (1,500) | `439574fd` | derived from E; `closed_eq_combSettle2` transport | `WSettles.rcomb`, `closed_eq_combSettle2`, `Settles.toW`; `ibex` (cyclic per process, acyclic per window) |
| X4: E-core-1's edge fragment, R-EDGE; the clocking discipline | `Core1Edge.lean` (804), `Core1Disc.lean` (175), `audit_discipline.py` (115) | `e39d0871` `7315a647` | derived from E | `rEdge` (any legal schedule, one commit); `clockExpand_disciplined`; audit: 22 ok, 38 no clock edge, 3 deliberate, 0 undisciplined |
| D-X1f, fuel half: `always_comb` statement fuel in `combFuel` | `Comb2Base.lean` (+57, additive), `Comb2Fuel.lean` (95) | `b47a2cab` | `run2` library lemma (no E) | `runCombProcess2_alwaysComb_of_combFuelB` |
| D-X1f2: termination on window-acyclic designs | `Core0WinTerm.lean` (312) | `ca33c55a` | `run2` theorem under E's window-rank hypotheses | `combSettle2_terminates_win`, `ibex_terminates` |
| D-X1g: R-DESIGN2 over the window rank | `Core0ObsWin.lean` (238) | `bebc7f65` | transport theorem | `included_E0_run2_win`; `ibex_included` (the process-rank route has no instance: `ibex_no_settles`) |
| D-X1h: the counter's cycle step | `CounterE.lean` (186) | `728b6ee2` | derived from E | `cnt_low`, `cnt_rise`, `cnt_rise_step` (supersedes P's `CounterMachine` as the R-CYCLE exemplar) |
| D-X1h: E-core-1 backend; the counter's inclusion and task statement | `Kernel/Core1Obs.lean` (201), `CounterEObs.lean` (289) | `e4d1f7bb` `92bd7481` | backend derived from E; `cnt_included`, `cnt_follows_E1` and `Safe.of_includedOnPorts` transport theorems | `cnt_included` (clock port hidden), `cnt_follows_E1` (`Follows_obs` and progress over `Obs_E1`), `progress_E1` |

Totals (MEASURED): 7,031 lines in 11 new `LeanModels/Sv` modules plus 57 added to `Comb2Base.lean`; 737
lines in 5 `.lean` files under `svgolf/design/architecture`.

## 2. Stop-rule record

| Item | Rule | Outcome |
|---|---|---|
| G-A | report the same day if items 1–3 do not close in the first slice | did not fire (READ, X1-NOTE §7) |
| G-B, R-DESIGN2, R-COMB-1, X4 | no line cap recorded in X1-NOTE (READ) | the sizes are in §1 |
| fidelity batch | none | +239/−50 lines across `Core0`, `Core0Proc`, `Core0Win` (MEASURED) |
| D-X1f fuel half | about 300 lines | 152 added (MEASURED) |
| D-X1h cycle step | about 300 lines | 186 (MEASURED) |
| D-X1h inclusion | about 150 plus the backend; report the backend's shape above 100 | **overran both**: backend 103, inclusion about 270 (MEASURED). Accepted, with the rule to stop at the line and send the count, even mid-proof |
| D-X1h `Follows_obs` transport | hard cap 60 | 50 (MEASURED) |
| D-X1f2 | about 350 | 312 (MEASURED) |
| D-X1g | about 200 | 238, inside the "about" (coordinator's ruling) |

## 3. Open debts, and what retires each

1. **Window rank, not yet restated.** The typed converse (`run2` → E: `runs_E0_of_runObs2`,
   `included_run2_E0_of_typed`) and progress over `Obs_E0` exist over the process-rank `Settles`
   only. Retired by restating them over `WSettles`, as for D-X1g. JUDGED 150–200 lines.
2. **Symbolic parameters.** `lowerWin` goes through `symExec`, which has no normal form at a
   symbolic `N` (L's finding, READ). So D-X1f2 and D-X1g apply at concrete lowerings only. Two
   routes (both JUDGED):
   - a general equation design built without `symExec`, its soundness (`WriteRel` per
     activation) proved once: 400–700 lines;
   - L's per-family route (`SingleE`: a hand-built equation design and one equality lemma): 100–150
     lines per family.
3. **Comb plus edge in one design** (D-X1h general). Stated in X1-NOTE §12: comb settle, edge
   Active region, NBA commit, comb settle again. It needs an edge-read discipline and `WSettles`'
   invariant re-established after the commit. JUDGED about 300 lines.
4. **`Obs_E1`'s environments.** It covers environments whose data change only in clock-low slots.
   Not proved (JUDGED): its slot list satisfies `Core1Disc.Disciplined`, and it agrees with
   `clockExpand` up to re-driving equal data. Retired by an `Obs_E1` over every disciplined slot
   list, with edge slots computed from the environment.
5. **The counter over `Obs_E1`:** the interface, admission and receptiveness conjuncts. Retired by
   proving them per backend (receptiveness is an existence claim).
6. **The clock's observation** is an assumption of `cnt_included`: a guarantee never reads its clock
   port from a sample (X1-NOTE §12). Retired by the TASKV2 decision on the clock port (decided
   Day 5).
7. **Hand profile proofs** (D-X1a, D-X1e): `CombDesign` of each lowered or equation design is about
   80–100 lines per fixture (READ, X1-NOTE §8, §10). Retired by an E-native decidable profile
   checker with a soundness theorem.
8. **D-X1d:** sensitivity-completeness and the rank on E's sensitivity are decided per design.
   Retired by a lemma from `symExec` and `selfReadFree`. JUDGED 200–300 lines.
9. **D-X1b** (`view` and `evalPure2` in E's trusted cone): retired when `Sv.Ast` carries resolved
   references. **D-X1c** (refusal payload `String`): retired by `SvClause`, with E-core-1's
   `World`/`Step` chain.
10. **E-core-1 growth:** blocking writes to locals in `always_ff` (D-X1i), `case` in edge bodies
    (D-X1j). Retired by the next E-core-1 slice.
11. **Observe-level definitions living in my modules:** `IncludedOn` (`Core0Obs.lean`), and
    `hidePorts`/`IncludedOnPorts`/`Safe.of_includedOnPorts` (`Core1Obs.lean`). Retired when P lands
    them in `Observe.lean` (one-line import change on my side).
12. **Not WS1's:** the `dyn32` declaration (the ls-sv audit's item). The Xcelium row for a one-step
    against a per-update NBA commit is needed only once a design can write a clock.

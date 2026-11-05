# WS2 (observations, cycle machine, contracts): Day-9 write-up

Agent P, branch `arch-obs` at `d2fbab08`. Claim labels as in `TASKV2-REVIEW.md`: **MEASURED** (proved
and compiled, or counted), **READ** (taken from a file), **JUDGED** (our estimate).

Applies to every row below (MEASURED):
- No `sorry`, `admit`, `native_decide` or `bv_decide`.
- Every theorem is pinned by `#print axioms`, within `[propext, Classical.choice, Quot.sound]`.
- Line counts are `wc -l` of the whole file, including documentation.
- Nothing trusted imports any of it.
- The `svgolf/design/architecture/*.lean` files compile with `compile-obs.sh`, the `LeanModels/Sv` ones
  with `lake build`.

## 1. What is proved

| Item | Files (lines) | Label | Headline results |
|---|---|---|---|
| Observation interface: port samples, pre/post per cycle, `ObservationModel`, `Behaves`/`Progress`/`Safe`, `Included` and the general `IncludedOn`/`SafeOn` | `Observe.lean` §1 (723 in all) | DRAFT of trusted text | `Safe.of_included`, `SafeOn.of_includedOn`, `included_iff_includedOn` |
| `Obs_run2`, with pre = the state the edge reads | `Observe.lean` §2 | provisional over `run2` | `run2_eq_runObs2`, `pre_sample_spec`, `Obs_run2.progress_iff` |
| Task v2 skeleton (`Spec`, `SatAt`, `Sat`, `IntParam`); `CombTask` and `SeqTask` as instances | `TaskV2.lean` (387) | DRAFT of trusted text; the instance theorems are proved | `statement_obs_iff_sat` (both classes) |
| `PreTask`, a Mealy class with its claim on pre | `PreTask.lean` (155) | DRAFT of trusted text | `PreTask.satisfiedAt_obs_iff_satAt` |
| Receptiveness for free: no process writes an input (decidable), plus termination | `ObserveFrame.lean` (707), `ObsComb.lean` (327) | provisional over `run2` | `Obs_run2.pre_input`, `receptive_of_writesInput` |
| v1 and Task v2 are equivalent on assign-only designs | `ObserveRedrive.lean` (197), `ObsCombRedrive.lean` (106) | provisional over `run2` | `computes_iff_computes_obs`, `statement_obs_of_comb`, `CombDesign.writesInput_eq_false` |
| All 4 accepted records under Task v2, with no re-proof | `ObsRecExample/Add/Mul.lean` (32 each, 7 code lines) | provisional over `run2` | each record re-accepted by `check.py` and its instance compiled against the staged solution (wall: 3–23 s per instance) |
| v1's convention restated over `Obs_run2` (`_stim`) | `ObsComb.lean`, `ObsSeq.lean` (276) | provisional over `run2` | `statement_stim_iff`, `statement_stim_bounded` |
| D6 cycle machine, and R-CYCLE against `Obs_run2` | `CycleMachine.lean` (167) | the shape is a derived view; the theorems are provisional over `run2` | `rcycle_run2`, `Obs_run2.safe_of_rcycle` |
| Closed-form clock cycle (the target of R-EDGE); flat-memory bridge | `REdgeRun2.lean` (123), `FlatMemRun2.lean` (136) | provisional over `run2` | `REdgeRun2.rcycle`, `rfRead_eq`, `rfWrite_abs` |
| Counter under Task v2 | `CounterObs.lean` (314) | provisional over `run2` | `cnt_sat` |
| Counter through D6 | `CounterMachine.lean` (221) | provisional over `run2`; **superseded** by A's `cnt_rise_step` (arch-x1 `728b6ee2`) | kept as the D6 exemplar only |
| Register file at every depth and width; a read during a write returns the old word | `RegFile.lean` (344) | provisional over `run2` | `rf_sat` (through `PreTask` and R-CYCLE) |
| D11 contracts: rely, guarantee, ghost state, arcs, direction; `Realizable`, `Receptive`, `Sat`, `SatExact` | `Contract.lean` (359) | the shape is a derived view; every theorem is a transport theorem (backend-generic) | `safety_sound` and its `_of_included`/`_of_includedOn` forms; `equiv_sound` (exact contracts only); `compose_holds`, `compose_safe_inv`, `compose_safe` |
| The full adder's contract | `ContractFA.lean` (210) | provisional over `run2` (through `Obs_run2`, not `Obs_E0`) | `fa_sat` |
| Contracts refine the Task v2 statement | `ContractTask.lean` (230) | §1–2 transport theorem; §3 provisional over `run2` | `Contract.Refines` (design-free), `satAt_of_sat`, `CombTask.contract_refines`, `fa_statement_obs` |

Totals (MEASURED): 2,622 lines in `LeanModels/Sv` (8 files) and 2,456 in `svgolf/design/architecture`
(12 `.lean` files).

## 2. Costs worth keeping (MEASURED)

- **Record instances:** 7 code lines each, against 39–60 lines for A's E0 instances. Over `run2`,
  `CombDesign` alone gives receptiveness, and no 4-state or `InitTyped` side conditions arise.
- **v1 ⇒ inputs read from pre:** 111 code lines, through A's re-driving argument (the estimate was
  higher).
- **`PreTask`:** 95 lines of draft trusted text.
- **`ContractTask`:** 104 lines of generic library, 22 lines of `run2` library, 52 lines for the
  full-adder instance.

## 3. Open debts, and what retires each

1. **Everything labelled "provisional over `run2`".**
   - Retired by R-DESIGN2 (WS1).
   - Safety moves with no re-proof through `SafeOn.of_includedOn`/`safety_sound_of_includedOn`. It
     needs typed stimuli: A measured that `run2` → E inclusion is false on ill-typed ones.
   - Progress and receptiveness are existence claims, re-proved per backend.
   - Comb slice: A's typed-stimulus inclusion. Clocked designs: R-EDGE (X4).
2. **`Obs_E0` instances of this work** (the records, the full adder, `ContractTask`'s instance).
   - Retired by the Day-9 merge with arch-x1. Every generic theorem here takes the backend as a
     parameter, so the instances re-instantiate.
   - A already transports 3 records to E-core-0 (READ, `X1-NOTE.md` §9).
3. **`ripple_fa` through the full adder's contract.** Closed by the lead's ruling (option (b)).
   - It needs four things, listed with JUDGED costs in `ContractFA.lean`:
     - `compose_safe_inv`'s `Inv`, from R-COMB-0's closed store;
     - `hproj`, from R-HIER on E-core-2;
     - the parent's `CombDesign` or E-fragment proof (about 60 lines);
     - the ripple arithmetic (about 120 lines, partly reusable from `ripple_add`).
   - Total about 250–300 lines beyond R-HIER and R-COMB-0.
   - Finding (READ): `compose_safe` alone cannot be used for a design with glue processes.
4. **Designs outside the comb profile** (`always_comb`, procedural) have no v1 ⇒ Task v2 transport.
   - Retired by WS1's R-COMB with `always_comb`, then the re-driving argument on that profile.
   - No record is blocked today: all accepted records are assign-only (READ, X3).
5. **Two-run properties have no instance yet:** `SatExact` (needs completeness) and `ArcsSoundOn`
   (needs an exact cycle machine per design).
   - Retired by the first equivalence task and the first composition with same-cycle paths through
     children, respectively.
6. **Promotion of the drafts** (`Observe.lean` §1, `TaskV2.lean`, `PreTask.lean`) after the maintainers'
   review:
   - unify the two receptiveness forms (`Valuation`/`Vals`, today bridged by `valOfVals`);
   - drop the duplicated `Sig`;
   - check the draft names for clashes in `SvGolf/Task.lean`;
   - write the `int32Agrees` guards on reference designs.
7. **Tied to future tasks:**
   - Receptiveness restricted to the input sequences a rely admits: needed by the first task with an
     input rely (none today).
   - The `Admissible` conjunct: once X10 fixes its clauses.

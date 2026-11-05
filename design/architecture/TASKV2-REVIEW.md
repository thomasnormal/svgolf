# Task v2: review packet (Day 5; updated 11-03, integ1103)

Agent P (WS2), branch `arch-obs`. Under review: `svgolf/design/architecture/TaskV2.lean` and
`PreTask.lean`, both DRAFTS of trusted text. Nothing trusted imports them, and no trusted file or
record has changed.

Labels: **MEASURED** (proved and compiled, or counted), **READ** (taken from a file), **JUDGED**
(our estimate).

## 1. The statement

- A statement sees a design only through its ports, sampled twice per clock cycle:
  - **pre**: what the clock edge reads. The inputs are applied, the combinational logic has settled
    and any asynchronous reset has taken effect, but no flop has updated. It is E's sample just
    before the edge.
  - **post**: the state after the cycle.
- The backend that produces the samples is a parameter: `run2` today, E next.
- `Sat` holds at every parameter value in the task's range intersected with its declared type's
  range, when:
  - the design's ports are exactly the task's;
  - the backend admits the design, every run completes (progress), and every sequence of known
    values on the inputs other than the clock appears in some run's pre samples (receptiveness);
  - under the clocking discipline (a rely on the environment), the guarantee holds on every prefix
    of every run where the task's rely holds.
- Inputs are read from **pre**.
- `CombTask` and `SeqTask` keep their own structures and their claims on **post**. `PreTask`
  (Mealy outputs, such as a register file's read port) puts its claim on **pre**.
- Each of the three classes is proved to be an instance of `Sat` (MEASURED: `statement_obs_iff_sat`,
  `PreTask.satisfiedAt_obs_iff_satAt`).

## 2. Proved since Day 5

| claim | status |
|---|---|
| v1's statement and the Task v2 statement are equivalent on comb-profile (assign-only) designs, over `run2` | MEASURED: `computes_iff_computes_obs` |
| Records move to Task v2 with no re-proof. The only side conditions are the record's own `CombDesign` lemma and distinct input names | MEASURED: `statement_obs_of_comb`, on all 4 accepted records, 7 lines each, each record re-accepted by `check.py` (`ObsRec*.lean`) |
| Receptiveness costs golfers nothing. "No process writes an input port" (decidable, and implied by `CombDesign`) plus termination gives it | MEASURED: `receptive_of_writesInput`, `CombDesign.writesInput_eq_false` |
| Changing the backend is a theorem. The general form is inclusion on the environments satisfying a predicate (`IncludedOn`) | MEASURED: `Safe.of_included`, `SafeOn.of_includedOn` |
| `run2` → E inclusion is FALSE on ill-typed stimuli. `run2` stores a stimulus value as given; E converts it to the port's width. It holds on typed stimuli | MEASURED by agent A: `not_included_run2_E0`, `included_run2_E0_of_typed` |
| E → `run2` inclusion needs no restriction, and three records transport to E-core-0 | MEASURED by agent A (READ, `X1-NOTE.md` §9) |
| The first sequential tasks under Task v2 | MEASURED, provisional over `run2`: the counter (`cnt_sat`), and the register file at every depth and width (`rf_sat`), where a read during a write returns the old word |

## 3. What changed from v1, and why

- **Samples instead of `run2` snapshots**: the backend is swapped by a theorem, not by re-proving.
- **Inputs read from pre**: this is E's convention, and the environment leaves trusted text.
- **Receptiveness**: without it, a design that drives its own input port could make the claim
  vacuous.
- **Pre exposed**: Mealy outputs become statable (`PreTask`).
- **The clocking discipline is a rely on the environment**: `Unclocked` and `ClockedBy` remain only as
  `run2`'s admission check.
- **Range intersected with the declared type's range**: a `parameter int` cannot hold 2^31.

## 4. Decisions for you, each with our lean and its cost

1. **Parameter range.** Lean: an explicit predicate per task, never derived from the submitted
   design, because a design-derived range could be made empty and the statement vacuous. The default
   is `N < 2^31`; tasks whose elaboration widths are larger get a tighter bound (`clmul`:
   `N ≤ 2^30`). Cost (JUDGED): one predicate per task, plus `int32Agrees` guards on the reference
   design. v1 implies the bounded statement (MEASURED), so no record moves.
2. **Receptiveness over all input sequences, or only those the rely admits.** Lean: all sequences
   now. Every current task has a trivial rely, so it costs 0 today. A task with a rely on its inputs
   will need the restricted form (JUDGED: one definition).
3. **The admission predicate stays a backend parameter until E exists.** Lean: yes. Cost 0.
4. **Pre = after the asynchronous-reset phase** (ruled by the lead); it agrees with A's E-core-0
   (READ). Cost 0.
5. **`PreTask` as a third trusted task class** (claims on pre). Lean: yes. Cost: 95 lines of draft
   text to review (MEASURED).
6. **Typed environments.** `run2` and E agree only on typed stimuli (MEASURED, by A). Lean: state
   R-DESIGN2 that way (`RDesign2On`) and change NO trusted text; E's environments are typed by
   construction (JUDGED). Cost 0.
7. **The `Admissible` conjunct.** Lean: add it once X10 fixes its clauses. Cost: later. For a design
   with a qualified `case`, the claim obligation (A1) is enforced by neither `Obs_run2` (it omits
   `run2`'s trace check, master `2218821b`) nor the draft statement: it comes from `Admissible`, or
   from E, which refuses a violated claim loudly (READ).
8. **The clock port is clocking, not an observed data port.** **Ruled 2026-11-03**:
   `docs/sv-kernel.md`, "Statement scope is narrower than E" (`16dbbcfb`), with its retirement path.
   The clock is hidden from the compared samples (`hidePorts`, `IncludedOnPorts`, transported by
   `Safe.of_includedOnPorts`; used in A's `cnt_included`); its behaviour is carried by the clocking
   discipline. Reason: within a cycle, E-core-1's samples show the clock going 0→1 while `run2`'s
   show the stimulus value (READ, agent A).

## 5. Open debts

- Everything over `run2` is provisional until R-DESIGN2. A has proved its comb slice; clocked
  designs need R-EDGE (X4).
- Designs outside the comb profile (`always_comb`, procedural) have no transport yet. All accepted
  records are assign-only (READ, X3).
- At promotion: unify the two forms of receptiveness, remove the duplicated `Sig`, and check the
  draft names for clashes.
- Hierarchical tasks wait for R-HIER (E-core-2).

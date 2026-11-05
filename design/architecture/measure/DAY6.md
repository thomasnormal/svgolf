# Day 6: the symbolic proof path over sv-tests, and RB82 after WP-PROC

**Status label:** measurement (pyslang, the repository's extractor, and the RB0 census's own Lean driver through the slot).
Agent M, WS4, 2026-11-02. Branch `arch-measure`, base `integ1102` at `d5fbdbc4`, which contains WP-PROC G1 (`19bc9f10`)
and its follow-ups. ARCH-NOTE §3.2 and §7 owe both measurements "before any tier is priced".

## A. The symbolic proof path over sv-tests ([`svtests_path.py`](svtests_path.py), data [`svtests_path.json`](svtests_path.json))

**Corpus.** The public chipsalliance/sv-tests, `~/repos/sv-tests` at `4f248075`: the `sv-tests` corpus of
`extractors/sv/census.py`. Every `.sv` file under `tests/chapter-*` is taken: 831 files. The 22k-file `sv-tests-2` corpus,
behind `docs/sv-construct-census.json`, is not on this host. The files are read under `python3.12 -I` and never executed.

**Path.** This is the one svGolf and the `sv_comb` tactics use, not the self-check path that
`docs/sv-construct-census.json` measures:
1. `extract.py --top T` (symbolic envelope);
2. `load_design_sv2`;
3. no Unsupported node at the default point;
4. for a flat design of continuous assigns and `always_comb`: `sv_structure?` (`CombDesign`, or the lowered
   `CombDesign d'`) and `sv_equations?`.

Steps 2 to 4 are the RB0 census's Lean driver (`census_lean.py`), reused unchanged: 183 loads and 37 tactic runs, one
slot acquisition, 8.5 min including the queue.

**Funnel (MEASURED, files):**

| stage | files | of 831 |
|---|---|---|
| negative test (`:should_fail_because:`) | 75 | |
| uses `` `include `` (multi-file) | 96 | |
| no module at the top (packages, classes, interfaces only) or several tops | 66 + 3 | |
| slang errors | 3 | |
| **reach the extractor** | **588** | 71 % |
| envelope has an Unsupported node | 405 | |
| **envelope clean** | **183** | 22 % |
| `load_design_sv2` refuses: the envelope holds an `Initial` process the Lean envelope parser does not know (126), `VACUOUS` cross-check (14), other (5) | 145 | |
| **loads, lowered design clean** | **38** | 4.6 % |
| not a flat comb design (no tactic) | 1 | |
| **`sv_structure?` recognizes it** | **28** | **3.4 %** (3.7 % of the 756 positive tests) |
| **`sv_equations?` accepts it** | **27** | 3.2 % |

The 28 come from chapters 6 (9 files), 11 (6), 5 (5), 10 (3), 9 (3), 7 (1) and 22 (1): nets, continuous assignments,
operators, selects, parameters, typedefs, a memory. The 9 refused at the structure tactic are chapter 7 arrays
(multidimensional, packed, unpacked), repetition and unpacking streams, and `localparam` of type `logic`, `string` or
`int unsigned`.

**Extractor blockers** (files in which they occur; top 10):

| blocker | files | blocker | files |
|---|---|---|---|
| `VariableSymbol:type` | 171 | `ClassType:ClassType` | 40 |
| `CallExpression` | 132 | `SysCall:format` | 20 |
| `AssignmentExpression:target` | 91 | `ProceduralBlockSymbol:NoEventControl` | 19 |
| `ExpressionStatement:CallExpression` | 80 | `SubroutineSymbol:Subroutine` | 18 |
| `NamedValueExpression:2state` | 46 | `TimedStatement:DelayControl` | 16 |

**Reading.** sv-tests is an LRM conformance corpus, dominated by testbench constructs: `initial`, `$display`, classes,
2-state and string variables. So 3.4 % is a statement about how far that corpus lies from the proof path, not about RTL.
- One finding is about the pipeline itself (READ, `Ingest2.lean` envelope parser). The extractor emits `Initial` as a
  structured process kind with no Unsupported node, and the Lean envelope parser rejects the whole envelope on it: 126
  sv-tests files and 18 RB0 envelopes (X6).
- The refusal is loud, but it lands at "the envelope does not parse" rather than at a named Unsupported node.
- If E is to give testbench processes a meaning (ARCH-NOTE §4.1, Day-6 owed item), this is the first boundary to move.

## B. RB82 re-run after WP-PROC ([`rb82_rerun/CENSUS.md`](rb82_rerun/CENSUS.md), [`rb82_rerun/census.json`](rb82_rerun/census.json))

**Method.** The RB0 census scripts (`svgolf/design/real-world-sv/rb0/census_{extract,lean,report}.py`), run unchanged on
`integ1102`. They read the same 137 pinned third-party files (`$SCRATCH/wprb0/src`, sha256-pinned in `files.tsv`),
through `run_py.py` (`python3.12 -I`).
- Lean: 217 loads and 44 tactic runs in two slot acquisitions (batch AB 3.8 min wall including the queue; batch C, 24 large envelopes, inside its 14-minute budget with no chunk skipped).
- The svGolf source-gate column is copied from the 11-01 run (`srcgate.json`); the gate itself is a trusted file and did
  not change.

**Funnel, before (11-01, base `9388ea91`) and after (11-02, `integ1102`), MEASURED:**

| stage | as is, before → after | best variant, before → after |
|---|---|---|
| blocks | 82 → 82 | 85 → 85 |
| slang accepts | 75 → 75 | 78 → 78 |
| extractor produces an envelope | 67 → **75** | 76 → **78** |
| envelope has no Unsupported node | 22 → **43** | 44 → **49** |
| `load_design_sv2` accepts it | 12 → **37** | 36 → **40** |
| lowered design clean (the checker's `design` stage) | 6 → **20** | 23 → **25** |
| `sv_structure?` recognizes it | 3 → **8** | 7 → **9** |
| `sv_equations?` accepts it | 0 → **6** | 2 → **7** |

**Status as-is, before → after:**
- LOADS-CLEAN 6 → 20
- LOAD-REFUSED 10 → 6
- EXTRACT-FAIL 8 → 0 (`--top` of an instantiated module, WP-PROC)
- EXTRACTS-LOUD 48 → 46

**Top blockers, before → after (blocks they are present in, as-is):**
- gone from the top: `ld-init-expr` (25, "unrecoverable packed dimensions" on typeless ports) and `st-for` (13);
- `dc-net-z` 25 → 15;
- `pr-implicit-event` 20 → 9;
- now first: `le-param-package` 16 → 18, package-scoped parameters, enum types and config structs.

The rest of the top 12 is unchanged in kind:
- `dc-unpacked` 12, `dc-member-kinds` 11, `ex-user-call` 11;
- `hi-uninstantiated` 10, `st-assign-target` 10;
- `le-const-context` 9, `cv-explicit` 9, `ld-initial-syscall` 9, `pr-concurrent-assert` 9.

**Reading.** WP-PROC roughly tripled the as-is real-block funnel at the design stage (6 → 20) and took the tactic stage
from 0 to 6 blocks. Packages now head the list, which matches X6: package-scoped parameters are also an elaboration
coverage gap.

## What this changes in ARCH-NOTE

- §3.2 caveat "No census of the symbolic proof path over sv-tests exists": it exists now. 28 of 831 files (3.4 %) reach a
  design the `sv_comb` tactics read, and 27 pass `sv_equations?`. The dominant boundary is testbench constructs (`initial`,
  calls, classes, 2-state and string variables), led by an `Initial` envelope kind that the loader cannot parse.
- §2 and §3 (RB82 numbers): base the next tier pricing on the post-WP-PROC funnel:
  - as is: 20 blocks clean at the design stage, 8 recognized by `sv_structure?`, 6 accepted by `sv_equations?`;
  - blockers led by packages, then nets, unpacked aggregates, functions and calls.

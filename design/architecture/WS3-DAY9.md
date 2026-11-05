# WS3 (product track: loops, then ordinary `always_comb`): Day-9 write-up

Agent L. Built on branch `arch-loop` (last `688c8f81`), now retired into `integ1103` (drift fixes `96ffce9f`,
`6f1a68a6`). Claim labels as in `TASKV2-REVIEW.md`: **MEASURED** (proved and compiled, or counted), **READ** (taken
from a file), **JUDGED** (our estimate). Details: `svgolf/design/loop/LOOP-NOTE.md` §9–§9.11.

Applies to every row below (MEASURED):
- No `sorry`, `admit`, `native_decide` or `bv_decide`.
- Every theorem is pinned by `#pin_axioms`, within `[propext, Classical.choice, Quot.sound]`.
- File sizes are `wc -l` of the whole file on `integ1103`. "Code lines" are non-comment, non-blank lines.
- No pre-existing module imports a new one, and nothing trusted imports any of it.
- Green on `integ1103` at `6f1a68a6`: targeted `lake build`, `compile-loop.sh` (10 modules, including `NoRun2`) and
  `compile-x7.sh` end to end. `compile-x7.sh` needs ibex at RB0's pin and M's slicer, in scratch.
- Heartbeats: `k` means thousands of `maxHeartbeats` units, which is 10⁶ `IO.getNumHeartbeats`.

## 1. What is proved

| Item | Files (lines) | Commits | Label | Headline results |
|---|---|---|---|---|
| G-L0–G-L3: fuel-free trip schemas, rows, the self-read guard, Bridge S | `Loop2.lean` (1,083), `Loop2Clmul.lean` (57), `g1/ClmulNested.lean` (146), two `Examples/…/schema.lean` (402) | `a6672a4e` `fb98950c` `0baa6bab` `f9c39f07` `2cbcbb95` | provisional over `run2` | the nested `clmul` `Statement` for every `N`; `headerSchema_agrees`, which refuses a wrapping 32-bit iterator; `SingleComb.terminates`/`runs` |
| Automation B, A, C, E | `Loop2Rows.lean` (105), `Loop2Sem.lean` (77), `LoopTask.lean` (133), `XorSum.lean` (62) | `ee2d1b26` `eee5dd0a` `903f5ef0` | tactics and lemmas, provisional over `run2` | `sv_loop_rows`, `sv_loop_sem`, `satisfiedAt_of_loop`; `clmul` design lines 394 → 96 |
| The recursive recognizer; nesting through it | `Loop2Frag.lean` (623), `g2/PriEnc.lean` (133), `g2/PopCount.lean` (98) | `e748d043` `a03c6bb5` | provisional over `run2` | `Stmt2.fragOk`/`frag_rec`, `loop1_single`; a priority encoder and a popcount for every `N`; `initNest` deleted |
| The seam over E-core-0 | `Loop2E.lean` (222) | `562a89db` | body: derived from E; task: transport theorem | `DenotesE` and five primitives, `Stmt2.frag_denE` |
| The single-process slot over E at a symbolic bound | `Loop2Slot.lean` (340), `LoopTaskE.lean` (180), `NoRun2.lean` (54) | `c7b56d30` | derived from E | `SingleE.slot`/`behaves`/`exists_behaves`; `statement_E0` for `clmul`, PriEnc and PopCount; `NoRun2` finds no `run2` constant in about 7,250 |
| Ordinary `always_comb` over E: defaults, `if`, `case`, several writes | `CombFragE.lean` (378), `x7/X7Blocks.lean` (part) | `d7af3dac` `688c8f81` | derived from E | `Stmt2.sem_run`, `activate_single` (a qualified `case` under its claim); `bwlogic_E`, `adder_flags_E` on M's ibex_alu slices |
| Written before read; whole slots | `CombSlotE.lean` (511), `X7Blocks.lean` (328 in all), `x7/latch.sv` | `5e2e16e9` `85b456f7` | derived from E | `combWbr`, `Stmt2.sem_rel`, `singleE_comb`, `slot_claimed`; `adder_flags_slot`, `bwlogic_slot` (claim only at the opening); `latch_refused` |
| Merges and master drift | as above | `dd88665e` `98ebce7b` `688c8f81`; `96ffce9f` `6f1a68a6` | drift fixes; the loop designs' statements are unchanged | A's loud qualifier and partial-overlap sensitivity; master's `run2` trace check; `CaseMode`. Lemma statements that changed: `satisfiedAt_of_loop` gains `hq`, `SingleComb` gains `noq`, `sem_runs` gains the claims premise, `combOk` excludes casez/casex |

Totals (MEASURED): 3,459 lines in 10 `LeanModels/Sv` modules, 1,072 in 7 `.lean` files under `svgolf/design/loop`, and
446 in 3 example files.

Heartbeats (MEASURED):
- `clmul`: on the first route `clmul_correct` used at most 85k and `statement` 100–200k. On the recognizer route every
  declaration passes at 20k.
- PopCount: `sem_eq` 3.6k, `statement` 1.6k. PriEnc: 4.6k and 2.2k.
- `bwlogic` costs 10.2k in all and `adder_flags` 18.2k. The E part is about 1k per block.
- The whole slots: `bwlogic_slot` 2.1k; `af_singleE` plus `adder_flags_slot` 3.3k.
- `CombSlotE` is 9.8k, plus 0.9k for `slot_claimed`.

## 2. Stop-rule record

| Item | Rule | Outcome |
|---|---|---|
| Plan build B | stop and re-price if B leaves `clmul` above about 280 design lines | did not fire: 245 after B (MEASURED) |
| Generalizing the shape (PriEnc, PopCount) | about 150 generic lines per shape | **fired**: PriEnc's shape is about 185 per shape (MEASURED). The recognizer was built instead, at 424 code lines, and accepted |
| Seam over E | about 250 lines | 200 (MEASURED) |
| Single-process slot over E | about 250 | **283, 13% over** (MEASURED). Accepted |
| Ordinary `always_comb` | about 300 generic lines | 245 (MEASURED) |
| Written before read | about 250 generic lines | **386** (MEASURED). Stopped at the line, not compressed in place. Accepted, with compression as a later pass |
| `slot_claimed` | hard cap 40 | 40 (MEASURED): 386 → 426 |
| `CombFragE` claims threading, at the arch-x1 merge | cap 50 | 44 (MEASURED) |
| Master drift, `SingleComb.noq` | cap 30; a new argument needs a go | asked first, then 26 (MEASURED) |

## 3. Open debts, and what retires each

1. **Closed: the arch-x1 merge broke three proof sites** (READ, flagged before the merge).
   - Sites: `Loop2Slot.sens_of_read`, `CombSlotE.sens_of_readW` and `CombFragE`'s case arm.
   - Retired by `98ebce7b` and `688c8f81`, and on master by `96ffce9f` and `6f1a68a6`.
2. **Every-behaviour statements for a body with a qualified `case`.**
   - `SingleE.typedI` asks its invariant of every typed view. A `unique` claim is about inputs, so `slot_claimed`
     covers one slot only.
   - Retired by an environment assumption in `SingleE`: the claim holds at every slot opening and `F` keeps it.
     JUDGED about 35 lines. A week-2 candidate under "multi-process slot over E" (the lead's call).
3. **Compression of `CombSlotE`** (426 lines against a line of about 250). JUDGED savings:
   - one relation bundling `sem_rel`'s six repeated hypotheses, about 30;
   - one walk instead of the separate `sem_inv` and `sem_rel`, about 40;
   - the arm/list split, about 15.
4. **Symbolic `N` beyond one process.** `SingleE` gives slot theorems at a symbolic bound with no lowering, but only
   for single-process designs. A's window route needs `lowerWin`, whose `symExec` has no normal form at a symbolic `N`
   (READ, WS1 debt 2). Retired by either:
   - a multi-process slot over E with the `SingleE` argument per process (week 2, JUDGED);
   - A's equation design without `symExec` (400–700 lines, READ there).
5. **The other four ibex_alu blocks** are in the fragment (MEASURED by an evaluated `#guard`). Their plain specs are
   not written. JUDGED:
   - `adder_in_a`/`adder_in_b`: about `bwlogic`'s size;
   - `result_mux`: wants a membership lemma, since a per-value split over 46 patterns is about 3.5× `af_mean`'s 9.7k;
   - `shifter`: needs the bit reversal over 32 trips, and window-level `combWbr` (next debt).
6. **`combWbr` tracks full writes only.**
   - So a signal assembled bit by bit, then read, is refused (`shifter`'s `shift_result_rev`).
   - Latches are refused by design: the extensionality step needs every signal of `W` written on every path.
   - Retired by tracking written windows in `D`. JUDGED about 40 lines.
7. **The `run2` `statement`s** beside each `statement_E0` stay provisional over `run2`. They are kept as `NoRun2`'s
   control. Retired by WS1's R-DESIGN2, or by deleting them once E is the only backend.
8. **Wiring.** `compile-loop.sh` is to be wired into the integration build by the lead. `compile-x7.sh` cannot enter CI
   as it stands: it needs the ibex sources and M's slicer, which stay out of the repository.

# fdiv circuit hunt: what exists in the wild and what we can prove

## Short answer

Yes, we found real circuits. No third-party circuit is provable through our interface as it stands, and none covers the full W>=2, P>=2 plane. The picture:

- **Two parametric families** have a measured, sharply bounded (W,P) region: drewbabel's `fp_div_sqrt` (W>=2, 2<=P<=2^(W-1)) and Berkeley HardFloat (W>=3, 2<=P<=2^(W-2)+3). Both are sequential FSMs. Both become exact combinational circuits only after a rewrite the evaluators wrote, not the authors.
- **Six fixed-format circuits** are exact at one format: binary32 (Kemet, Sherpa, fontamsoc), binary16 (DGrid, plus TEA at search stage) and (4,4) (tt_um_fp8_fpu). Two of the binary32 ones, and Kemet's `/` and `%`, need wrappers or rewrites.
- **One circuit is wrong:** Phy-Engine returns +-0 instead of 0x0400 on 60 of 2^32 binary16 pairs. Random testing does not find it. A one-line patch fixes it.
- **One cannot be assessed as shipped:** fudian (Chisel) was only measured on a hand transliteration.

On the interface: the statement is `forall W P, inRange W P -> (task W P).StatementFixed (sem W P)`. I read this in `svgolf/design/fdiv-param/TASK.md` and `H3-NOTE.md`. Option C needs zero library lines, and `inRange` is currently `2<=W /\ 2<=P`.

- **The machinery is general.** A region-limited circuit is a task with a narrower `inRange` (a new trusted `Spec.lean`, about 110 lines per H3), or a fixed-format task.
- **The trusted statement is not general.** A region-limited proof is a weaker theorem than the full-range one. It cannot sit on the same leaderboard row as a full-range solution without a rule. That is the maintainers' decision.

## 1. Method, and measured versus read

**Pipeline.** Five search agents (combinational, iterative, generators, reciprocal/Newton, small formats) screened about 80 candidates. About 60 were dismissed from headers or partial reads. Ten shortlisted candidates (nine circuits, HardFloat twice) were evaluated independently.

**Reference.** The reference is the exact-rational oracle `<scratchpad>/fdivsurvey/fdiv_oracle.py`. It was checked against the repo's binary16 oracle (200,000 pairs) and CPython float32 division. Evaluators also used their own C++ integer oracles, each cross-checked against it.

**Tools.** Verilator 5.042, Yosys 0.53, Icarus, and the repo's `score.py`, `banlist.py`, `srcgate.py`, `fourstate.py` and extractor.

**MEASURED by evaluators** (real RTL unless stated):
- Kemet (binary32), DGrid (binary16), Phy-Engine, drewbabel, both HardFloat evaluations, Sherpa, fontamsoc and tt_um_fp8_fpu were simulated as shipped, through thin wrappers where needed.
- Exhaustive runs: DGrid and Phy-Engine at all 2^32 pairs; tt_fp8 at all 65,536; drewbabel and HardFloat at all pairs of the formats with W+P<=12, plus partial or full W+P=13 and 14.
- Larger formats were sampled up to (11,53) and (15,113) for drewbabel.
- Mutation checks (dropped sticky, ties rounded up) showed the harnesses can see rounding errors.

**READ only, or transliterated:**
- fudian was measured only on an evaluator-written SystemVerilog transliteration of the Scala. Chisel could not be run: the Maven download was denied by the permission classifier. Every fudian region boundary depends on that transliteration being faithful.
- TEA's `fp16_div` was measured at search stage only: exhaustive on an extracted wrapper, plus a Python transliteration.
- About 60 dismissed candidates were classified from headers and partial reads.

**No Lean or lake was run by anyone**, so every "provable" statement and every proof-size estimate is judgement. I ran no simulations. I only read the repo notes (`TASK.md`, `H3-NOTE.md`, `PROVING.md`) to ground what the interface and tactics allow.

**Conversions the evaluators invented.** None of these are third-party code, and every area figure below is for such a rewrite:
- Port renames and handshake wrappers.
- NaN-sign masks, and rm/opcode/sqrt pins.
- FSM-to-combinational unrolls: drewbabel `fdiv_comb.sv` and `fdiv_flat.sv`; HardFloat `hf_div_comb.v`, `hf_flat.sv` and `hf_fdiv2.sv`; Sherpa `fdiv32_comb.sv` and `fdiv32_flat.sv`; fontamsoc `fdiv32_faithful/flat_mul/flat_arr.sv`; tt_fp8 `fdiv_comb.v`.
- Flattening, directive stripping, `signed` and function removal, and `*` to shift-add.
- A one-line Phy-Engine patch.
- DGrid's hand re-parameterisation, which is exact at all 66 formats with W+P<=14 but is not the author's code.

**Other caveats:**
- Equivalence of each unroll to its original FSM is empirical (identical outputs on test sets), not proved.
- The (8,24) pinned scores mostly timed out (1800 s limit, machine load 100-230), so binary32 areas are missing or unofficial proxies.
- Licences were read from repo metadata only. No legal review.
- Evaluator proof-size estimates are guesses extrapolated from the fdiv16 proof (3,781 lines).

Artifacts are under `<scratchpad>/fdivsurvey/`. Examples:
- `.../eval_drewbabel_riscv_vector_rtl_fp_div_sqrt_s/`
- `.../eval_Phy_Engine_Dev_Phy_Engine_test_0020_fp16/`
- `.../eval_Berkeley_HardFloat_divSqrtRecFN_small_Ve/`
- `.../eval_KemetCore_hapi_fp32_div_HapiCore_fp32_di/`

## 2. Table of evaluated circuits

Reference areas, from `H3-NOTE.md` and the evaluators: the fdiv16 reference scores 1929.778 GE / depth 299, our parametric D1 scores 1911.446 / 300 at (5,11) and 1251.195 / 181 at (8,8), and D2 scores 2314.058 / 295 at (5,11).

| Circuit | Licence | Format | Kind | Conformance (measured) | Area, pinned `score.py` (GE / depth) | Tooling | Proof route |
|---|---|---|---|---|---|---|---|
| KemetCore `hapi_fp32_div` | Apache-2.0 (repo) | (8,24) | comb, `/` `%` | **EXACT**; 0 mismatches in 7.26M pairs vs oracle and about 26.3G vs host float32 | pinned run did not finish; unofficial proxy about 21.6k GE; 15,106 gates pre-ABC | banlist FAIL; fourstate 2 findings; extractor 8 Unsupported | fixed fdiv32 task only, after rewrite plus `/ %` support |
| DGrid `dgrid_fp16_div_rtl` | none (reserved) | (5,11) | comb, `/` `%` | **EXACT**; 0 in 2^32 vs `_Float16`; 0 in 2.1M vs oracle; scored netlist 0 | 2142.4 / 316 (flat 2142.4 / 320) | source gate refuses 5 directive lines; banlist FAIL; 6 signed | fixed fdiv16, after rewrite; licence blocks copying |
| drewbabel `fp_div_sqrt` | Apache-2.0 WITH SHL-2.1 | W>=2, 2<=P<=2^(W-1) (SigW<=128) | FSM, P+5 cycles | **WRAPPER**; 0 mismatches over all pairs of 32 formats with W+P<=12; DIFFERS (refuses to elaborate) outside | own unroll: (2,2) 142.3 / 26; (3,3) 288.0 / 40; (4,5) 630.3 / 81; (8,8) 1388.5 / 168; (5,11) 2031.8 / 280; (8,24) timed out | Yosys cannot read the original; extractor 27 Unsupported; flat rewrite 0 Unsupported | after rewrite, restricted `inRange`; best third-party target |
| Berkeley HardFloat `divSqrtRecFN_small` (two evaluations) | BSD-3-Clause | W>=3, 2<=P<=2^(W-2)+3 | FSM, recoded format | **WRAPPER** in region (0 in about 2.6e9 pairs); **DIFFERS** outside | unrolls: (5,11) 2247-2309 / 283-318; (8,8) 1457-1529 / 181-191; (3,3) 305-320 / 43-44 | source gate refuses directives; Verilator rejects line 305; flat L2 0 Unsupported | after rewrite, region `inRange`; heavier |
| XiangShan fudian FDIV | Mulan PSL v2 (no repo LICENSE) | about 9<=P<=2^(W-1)+1 and W<P, measured on a transliteration | FSM, SRT16, sqrt shared | **UNUSABLE as is**; REGION-LIMITED; differs in 4 ways outside | unscoreable (flops); unroll timed out | not run as Chisel | do not pursue |
| RTLDesignSherpa `math_ieee754_2008_fp32_divider` | MIT | (8,24) | FSM 9-10 cycles, 128-entry LUT + Newton | **WRAPPER**; raw 43,368 NaN-sign mismatches in 3.33M pairs; **default `SUBNORMAL_SUPPORT=0` fails 28.7%** | none (timeouts); pre-ABC 25,480 gates | instances, `signed`, used-before-declared | fixed fdiv32, after rewrite; needs a Newton error bound |
| fontamsoc `fpu.sv` (`PUFDIVDSP2`) | **GPL-2.0-only** | (8,24) | FSM 18 cycles, Newton + fix-up | **WRAPPER**; 0 in 3.92M oracle pairs plus 16.8M float32 pairs | unofficial about 44.8k GE; pinned timed out | `*`, `signed`, functions | fixed fdiv32; large; GPL |
| Phy-Engine `fp16_div_unit` | Apache-2.0 | (5,11) | comb | **DIFFERS**: 60 of 2^32 pairs, one tie class | 2294.7 / 292 (patched+defaults 2307.1 / 291) | banlist pass; fourstate FAIL (21 latches); extractor 1 Unsupported; 24 instances | patched flat copy only; original is a negative test |
| tt_um_fp8_fpu | Apache-2.0 | (4,4) | elastic FPU, 4 or 14 cycles | **WRAPPER**; raw 6,482 of 65,536 NaN mismatches, 0 after `is_nan ? 7C : y` | own unroll: 542.3 / 63 | source gate refuses directives; fourstate 1 finding; 50 Unsupported | fixed (4,4) task, exhaustively decidable |
| TEA `fp16_div` (search stage only) | none | (5,11) | function in a sequential module | **EXACT** on an extracted wrapper (2^32, 0 mismatches) | 18.5k cells | needs extraction | cross-check only |

Mismatch classes and rates, by circuit:

- **Kemet:** none found. 0 NaN, subnormal, rounding or special-case mismatches. The only gap is port name `y` vs `q`. Run-time division by zero makes internal values x, but the output is never x in 400k tested pairs.
- **DGrid:** none found. A mutant without `sbit` was caught (5.66M mismatches in one exhaustive slice).
- **Phy-Engine:** one class only, 60 pairs (15 magnitude pairs x 4 signs). When the quotient is exactly 0x3FF.8 ulp (e.g. `a=0x07ff, b=0x4000`) the correct RNE result is 0x0400. The design emits +-0 because the exponent field stays 0 after the carry into bit 10. 1M uniform random pairs have an expected 0.014 hits, so only structured sweeps find it. The one-line patch gives 0 mismatches over all 2^32. Reported upstream on 2026-11-02 as https://github.com/Phy-Engine-Dev/Phy-Engine/issues/1 (file unchanged at that date: master `01367a3b`, sha256 `ca0614996cd0886cb2e1a21b547b9a65b5a1c690fa1d8b9592cddd9d0b676916`; re-checked on that head with Icarus against the exact-rational oracle, 30,124 pairs: exactly the 60 mismatches, 0 with the patch).
- **drewbabel, outside the guard (guard removed in an experiment):**
  - Still exact at (2,5), (2,6), (3,5..8), (4,9..10) and (5,17).
  - Wrong at (2,7..12), (3,9..10), (4,14) and (5,24): the W+2-bit exponent wraps and a huge quotient returns a signed zero instead of infinity.
  - The shipped guard is conservative but safe on everything tested.
- **HardFloat, outside the region:**
  - Fails for W=2 at every P and for P>2^(W-2)+3.
  - Classes are underflow/subnormal, spurious NaN, special-operand, and overflow edge. Never NaN payload or NaN sign.
  - The boundary was located exactly at W=3..7 (P 5/6, 7/8, 11/12, 19/20, 35/36).
  - P=2 works despite the documented p>=3.
- **fudian:** the failure classes are W>=P (output garbled), P>2^(W-1)+1 (zero returned as infinity), P>=2^(W-1)+4 (exponent wrap) and W in {2,3} with P>=9. Reportedly P<9 does not elaborate; this was read, not measured.
- **Sherpa and tt_fp8:** the NaN sign and payload are the only difference after the one wrapper step.
- **Sherpa with `SUBNORMAL_SUPPORT=0`:** it flushes subnormals to zero.

## 3. What could be proved through the general (W,P) interface

**As is: none of the nine.** Each fails at least one gate:
- Sequential: drewbabel, HardFloat, fudian, Sherpa, fontamsoc, tt_fp8.
- Spec mismatch: Phy-Engine.
- Banlist, signed declarations and fourstate: Kemet, DGrid.

**Full W>=2, P>=2 plane: none.** Only our own D1 and D2 (`H3-NOTE.md`) cover it, validated exhaustively at all 66 formats with W+P<=14 plus both 2^32 formats.

**Region-limited parametric families** (a proof would carry the region as a hypothesis, which means a narrower `inRange`):

| W | drewbabel (P range) | HardFloat (P range) | fudian (transliteration) |
|---|---|---|---|
| 2 | 2 only | none | none |
| 3 | 2..4 | 2..5 | none |
| 4 | 2..8 | 2..7 | none |
| 5 | 2..16 | 2..11 | 9..17 |
| 8 | 2..128 | 2..67 | 9..129 |

- (5,11), (8,24) and (11,53) lie inside all three; (8,8) is inside the first two.
- drewbabel is not a strict superset of HardFloat: (3,5) is HardFloat-only and (2,2) is drewbabel-only.
- The bounds are measured fits plus source reasoning, not proofs.

**Fixed-format circuits** (a fixed-size task, which Option C already supports):
- (5,11): DGrid; patched Phy-Engine.
- (8,24): Kemet, Sherpa, fontamsoc. `fdivBits 8 24 = fdiv32` is `rfl`, so the spec side is cheap.
- (4,4): tt_fp8. This is a new point with no existing task.

**Cannot be proved because they differ from the spec:**
- Phy-Engine's original. A proof attempt must end at `a=0x07ff, b=0x4000`.
- Each region circuit outside its region.
- Sherpa at default parameters.
- tt_fp8 and Sherpa raw, without the NaN mask.

**Relaxed variants.** These suggest a variant but not one clean one. The search stage saw many designs that differ from the spec on two or three axes at once:
- Flush-to-zero or DAZ (membrane, Sherpa bf16, SDF-RT).
- Truncating (Acc4Act bf16, the Cubic_Solver fp32 divider).
- Payload-propagating or x86 NaNs (membrane, dawsonjon).
- A no-infinity E4M3FN format (Radonoxius, Phy-Engine 0023, TEA FP8). This is a different spec function, not a relaxation.

The one clean candidate for a flush-to-zero family is `rafi-1st FpDivUnit`, from the generators search. It is parametric in exponent and fraction width, combinational, uses `/` and `%`, and emits the canonical qNaN with sign 0. It was read only; rounding and exactness are unmeasured. A relaxed task needs a new trusted spec function, so I would not start one until the maintainers want it.

**Proof effort.** The per-circuit estimates are guesses (Kemet 2.5-4.5k lines, DGrid 1.5-2.5k, drewbabel 1.5-2.5k, HardFloat 3.5-5.5k, Phy-Engine 1.5-2.5k, tt_fp8 0.3-0.7k, fudian 3-6k, Sherpa 2.5-6k, fontamsoc 4-7k). They are not additive. H3 estimates about 3,260 new lines (planning figure 4,300) for the shared parametric math layer. The first parametric proof pays that cost whichever circuit it is. Later parametric circuits are then marginal.

**The real obstacle is tactic cost, not circuit choice.** `H3-NOTE.md` measured `sv_structure` and `sv_equations` growing about 0.1*n^2 seconds in the number of sites on parametric netlists (about 13 minutes each for D2's roughly 90 sites, under load). Third-party flats are of comparable size: drewbabel's flat is about 44 assigns plus 2 loops; HardFloat's L2 has 104 assigns plus 6 loops. None of them was run through the tactics.

## 4. Baselines and proof targets

**Baselines.** No third-party-derived circuit beats our references at binary16. The extra columns below are for the evaluator rewrites:

| Circuit (rewrite) | Area at (5,11), GE / depth | vs reference 1929.778 |
|---|---|---|
| drewbabel unroll | 2031.8 / 280 | +5% area, depth 280 vs 299 |
| DGrid | 2142.4 / 316 | +11% |
| HardFloat unroll | 2247-2309 / 283-318 | +16-20% |
| Phy-Engine | 2294.7 / 292 | +19% |

- At (8,8): drewbabel 1388.5 / 168, HardFloat 1457-1529 / 181-191, against D1 1251.2 / 181.
- At (4,4): tt_fp8 542.3 / 63 (D1 not measured there).
- Binary32: no comparable pinned numbers. Kemet's unofficial proxy (about 21.6k GE) and Sherpa's pre-ABC count (about 38k GE) are not comparable to D1's pinned 7450.5 / 1256.
- DGrid pays for Yosys-lowering `/` and `%` (2142 GE against the hand restoring chain's 1930).
- Entries must pass the banlist, so DGrid and Kemet are not entries. Phy-Engine passes the banlist but is wrong and 19% larger.

Honest use as baselines:
- The drewbabel unroll (2031.8 GE) would beat the current fdiv16 draft starter (2089.081 / 298, per the evaluators).
- Nothing else is useful as a leaderboard rung.

**Cross-checks of spec and oracle.** Independent authors agree with our oracle: DGrid and TEA exhaustively at binary16, Kemet at about 26G binary32 pairs, and drewbabel and HardFloat across formats up to (11,53). This is real evidence that our NaN, subnormal and tie reading matches what people implement.

**Proof targets, in priority order:**
1. drewbabel flat, with hypothesis P<=2^(W-1). It is parametric, covers W=2, uses the same restoring-plus-RNE architecture as our reference so the shared certificate reuses, and has the smallest flat.
2. Phy-Engine patched and flattened, as a second binary16 structure. Moderate value.
3. tt_fp8 flat DIV-only at (4,4), with the NaN canonicalizer folded in. It is the cheapest proof and exhaustively decidable.
4. HardFloat L2, with region hypothesis W>=3, P<=2^(W-2)+3. It adds a recoded-exponent math layer that nothing else in the repo needs, so it is heavy. Its main value is TestFloat pedigree and big-format cross-checking.
5. Kemet and DGrid, only if word-level `/` and `%` is added to the tactics and a fourstate rule for division by zero.
6. Sherpa and fontamsoc: only as a Newton-error-bound exercise. They need `*` (shift-add arrays) and a bound over all 2^23 divisors, and fontamsoc is GPL.

**Negative test.** Phy-Engine's original is a ready-made real-world refutation fixture for `tests/fdiv16/negative`. The random post-synthesis vectors would miss it, so only the proof catches it.

## 5. What the circuits teach about constructs versus the tactic fragment

Fragment limits come from `svgolf/PROVING.md` and the H3 probes. Every idiom below is outside the fragment today:

- **Run-time `/` and `%`** (Kemet, DGrid, TEA, rafi, Centauria). The most common single-module idiom. It is banned in the task and has no tactic support. fourstate has no x rule for division by zero, even though the output is masked.
- **`signed` declarations and `$signed`** (Kemet 5, DGrid 6, HardFloat 11+, Sherpa 7, fontamsoc 7, tt_fp8 about 31). Always for the exponent. The repo's reference uses an unsigned offset exponent, which is the standard fix.
- **User functions with loops** (Kemet `clz24`, HardFloat `clog2`, drewbabel `fp_lzc` and `fp_round_up`, tt_fp8 `do_round`, fontamsoc `clz64` and `seedf`). The extractor marks them Unsupported. The fix is to inline them into assign chains.
- **`$clog2`, `2**` and sized localparams.** H3's D1 uses these and is refused at load. D2 uses affine counts instead.
- **Packages, header imports, enums, `$error` and size casts `N'(...)`** (drewbabel, Sherpa 46 casts). Yosys 0.53 cannot read drewbabel as written.
- **Preprocessor directives** (`include`, `define`, `ifdef`, `timescale`). The source gate refuses them (DGrid 5 lines, HardFloat 60+, fontamsoc about 50, tt_fp8). `verilator -E` removes them.
- **`always @*` with partial assignment** (Phy-Engine: 21 latch-inferring regs). It fails extractor rule R5 and fourstate.
- **Hierarchy** (Phy-Engine 24 instances, Sherpa 510, HardFloat). The tactics refuse instances, so everything must be flattened.
- **`*` between variables** (fontamsoc, Sherpa). It needs shift-add arrays (fontamsoc's flat is 598 assigns) or a hand multiplier proof.
- **Run-time part-select indices** (`x[i]`, `mag[i]` in priority-encoder loops). fourstate flags them.
- **Replication, `+:` selects and concatenation operands of `+`** (HardFloat L2, drewbabel flat). H3's probes found parameter-count replication refused and window fills accepted. These rewrites are likely to need more lowering.

**What is already accepted** (from `PROVING.md` and the H3 probes): generate-for with affine bounds, packed 2-D rows, affine integer localparams, window writes and fills, vector `?:`, comparisons into one-bit signals, and single-assignment `always_comb` case arms with a default.

Two other lessons:
- NaN policy is the most common mismatch, and the canonical sign-0 rule discriminates well (Sherpa, tt_fp8, dawsonjon and membrane all differ).
- Flush-to-zero is the most common subnormal divergence in the wild.

## 6. Recommended shortlist

**Do first**
1. **One Lean acquisition** to run `sv_structure?` on the evaluators' flat files: drewbabel `fdiv_flat.sv` at several (W,P), HardFloat `hf_fdiv2.sv`, fontamsoc `flat_mul`/`flat_arr`, Kemet `fdiv32r.sv`, the preprocessed tt_fp8. Nobody ran Lean. Record the first refusal and the scaling.
2. **Land H3 gate 1** (our own D2 proof). The shared math layer pays for every later parametric proof. Measure D2's `sv_structure` cost first. If it stays about n^2, drewbabel's smaller flat is the hedge.
3. **drewbabel flat, under P<=2^(W-1)**, as the first third-party proof. It needs a narrower-`inRange` task, which is the maintainers' decision.
4. **Phy-Engine original as a negative test**, plus its patched, flattened version as a second binary16 proof target.
5. **tt_fp8 at (4,4)** as a cheap demonstration, if a fixed-format task at a new (W,P) is wanted.

**Did not pan out**
- fudian: not runnable here; unreliable region; unscoreable.
- Sherpa and fontamsoc: need `*`, a Newton error bound over 2^23 divisors, and a GPL concern for fontamsoc.
- HardFloat as a first target: heavy, with a recoded-exponent layer.
- FloPoCo: flushes subnormals.
- PakFPU, the bf16 and fp32 toys (Centauria, Acc4Act, Cubic_Solver), moon_fpu_div (11-12% wrong) and TonnoBello fp16_unit (14.8% wrong): non-conforming.
- NR and Goldschmidt reciprocal designs: not correctly rounded.
- holoso and rafi-1st: not IEEE (no subnormals).

**Caveats to carry forward**
- Derived circuits are ours. A proof is about the rewrite, not about the third-party file.
- The unroll-to-FSM equivalence is empirical, not proved.
- Regions are measured fits.
- Licences: do not copy DGrid or TEA (none), watch fontamsoc (GPL-2.0-only), and treat drewbabel's SHL wraparound as unreviewed.
- (8,24) areas need an idle-machine rerun.
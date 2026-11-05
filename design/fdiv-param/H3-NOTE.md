# WP-H3, gate 0: the parametric `fdiv #(W, P)` (feasibility and design)

**Outcome (gate 0, 2026-11-02): the design exists and is validated; the math layer is GO; the design layer is
CONDITIONAL on the cost of two tactics, which is the one real obstacle (about `n^2` in the number of sites: a
fragment-clean parametric reference is about 13 minutes per tactic, extrapolated from measurements on a machine at load
average 140, against under a minute for the flat fdiv16).** Everything below is a note: no proof was attempted (that is gate 1), nothing outside `svgolf/design/fdiv-param/`
was touched.

Status: NOTE, 2026-11-02, branch `wph3` (off `svgolf-prep` `5d17a92e`, which has WP-B2 gates c, d, 3a, 3b, 4a; gate 4b is
on `wpb2g4b` and not merged). Labels: MEASURED (I ran it, the file is named), READ (from a source file), MODEL (the
Python model `h3/fdivp_model.py`), PLANNED (a proposal), ESTIMATE (a guess, with its basis). Everything is under
`svgolf/design/fdiv-param/h3/` (designs, model, testbenches, probes, generators, results).

## 0. Summary and go/no-go

1. **A parametric reference exists and is validated** (section 3). Two designs, module `fdiv #(parameter int W, parameter
   int P)`: **D1** `fdivp.sv` (165 lines, natural: `$clog2`, `2**`, replication, sized localparams, logarithmic
   normalizer and shifter) and **D2** `fdivp2.sv` (190 lines, fragment-friendly: only affine constructs, linear
   one-bit-step normalizer and denormalizer). Both equal the Python model, the exact integer oracle and the `Fraction` oracle
   of `spec/validate/oracle.py` (validated against the Lean spec) on **every operand pair of all 66 formats with `W + P <= 14`
   (3.8 x 10^9 pairs per design) and on every pair of the two 2^32-pair formats `(5, 11)` and `(8, 8)`: 0 mismatches**; and
   on 200,000 corner-rich vectors per format at 14 (D1) and 7 (D2) larger formats (section 3.3), up to `(11, 53)` and `(2, 62)`: 0 mismatches.
2. **Score.** D1 at `(5,11)`: **1911.446 GE, depth 300, 1.0 % SMALLER than the hand-flattened fdiv16 reference**
   (1929.778 / 299); at `(8,24)`: 7450.536 / 1256. D2: 2314.058 / 295 at `(5,11)` (+21 % over D1) and 9813.601 / 1279 at
   `(8,24)` (+32 %). Generality costs no area for D1; D2 pays for staying inside today's fragment.
3. **Fragment (section 4).** D1 is outside the `sv_comb` fragment in six independently probed ways (`$clog2`, `localparam`
   inside a generate, replication, parameter/genvar constants in comparisons, sized localparams, non-bare shift amounts) and is
   REFUSED AT LOAD (`KOV`, "ConversionExpression:width in a constant context"). D2 is entirely inside: `sv_structure?`
   reads all ~90 sites, and the loop-indexed rows that blocked H2 (gap G2) are accepted since gate 4a. **But the real
   tactics are expensive on a parametric netlist: 18 s, 49 s, more than 170 s for 11, 21, 41 plain sites** (about
   `0.1 * n^2`; the flat fdiv16 netlist costs under 1 s because it is DECIDED), so D2 (about 90 sites) is about 800 s for
   `sv_structure` and as much for `sv_equations` (both hit my 280 s ceiling on D2 itself). Implied solution stage:
   **T about 27 min, a 4T limit of about 110 min** for D2 as written (loaded-machine figures), against 130 s for fdiv16; about 9 min / 35 min if
   the design is reduced to about 50 sites (ESTIMATE). This is the number that decides the work package.
4. **Math layer (section 2).** The certificate is DONE for every format (`CertF.lean`, WP-H1). By declaration spans the
   fdiv16 proof splits **25 % AS IS, 63 % MECH (literals become expressions of `W`, `P`), 12 % NEW** (the three
   enumerating proofs: the 11-bit normalizer by kernel evaluation, the 4-stage barrel shifter on 16 shift codes, the
   13-way case split of the rounding core: each becomes an induction). ESTIMATE: about 3,260 new lines (planning figure
   4,300 with H2's overrun), 19 to 27 slot-hours (planning 25 to 36, the spread is the tactic cost); no solver, `bv_decide` or
   `native_decide`.
5. **Statement (section 5).** The minimal trusted change is **zero library lines**: Option C (`SpecLocal.lean` as the new
   trusted `tasks/fdivp/Spec.lean`, a family of fixed-size `CombTask`s, `statement_fdiv16` shows the 16-bit task is the
   instance `(5, 11)`). The `CombTask2` patch applies cleanly (35 lines) but would rebuild every task library; keep it for
   a second two-parameter task. The one non-N-ary spot of `check.py` is the advisory `--tactics` probe.
6. **Go / no-go.** Statement + task skeleton: GO. Math layer (H3-2 to H3-8): GO, independent of the tactic cost. Design
   layer (H3-9): **CONDITIONAL**: first measure D2 once (`sv_structure` with `maxHeartbeats 0`, one acquisition of
   15 to 25 minutes) after the all-clear, and reduce the site count; if the cost stays at `n^2` the time limit is the
   decision for the maintainers, or a tactic-side fix (REPORT G5', section 7).
7. **Decisions and requests** are in section 7.

## 1. How this was measured

* Tip `5d17a92e` (svgolf-prep: gates c, d, 3a, 3b, 4a of WP-B2 in; **gate 4b is NOT in the tip**: branch `wpb2g4b` =
  `wpb2g4c`, tip `87f0e2b4`, committed 2026-11-01 23:12, not merged; I did not build it, see section 4). Branch `wph3`
  off the tip, worktree in the scratchpad (`wph3/wt`). Lean probes ran READ-ONLY against the shared tree's built tactics
  (`lake env lean`, one acquisition at a time through the Lean-slot wrapper, `LEAN_NUM_THREADS=2`); nothing was built in the
  shared tree, and no file of `LeanModels/`, `check*`, `score/`, `lakefile.toml`, `lean-toolchain` or the trusted
  `tasks/*/Spec.lean` was touched.
* The lead's full suite was running on the shared tree for most of this gate, so every Lean number below is
  MEASURED UNDER HEAVY LOAD (`uptime` showed a load average of 135 to 155 during these runs: several `yosys-abc`, a
  `check.py` run and other agents): treat the seconds as upper bounds, the SHAPES (what is refused, what scales) as exact. The long measurements (`sv_structure` and `sv_equations` on
  the whole parametric design, section 4.3) are deliberately NOT done yet; they wait for the all-clear.
* Everything is under `svgolf/design/fdiv-param/h3/` (designs, model, testbenches, probes, generators). The Lean
  probe files there carry the scratchpad's absolute `load_sv` paths: they are the raw inputs of the probe runs, not
  files that build in the tree.
* Labels: MEASURED (I ran it, the file is named), READ (from a source file), MODEL (the Python model
  `h3/fdivp_model.py`), PLANNED (a proposal), ESTIMATE (a guess with its basis).

## 2. (a) What of the fdiv16 math layer generalizes

The proof of `fdiv16` is `tasks/fdiv16/{SpecFacts, Cert16, DpModel, DpRound, DpCert, DpFinal, DpBv, DpGlue}.lean` and
`reference/fdiv16.lean` (3,781 lines in all). The question for every lemma is the same: does its STATEMENT mention a
literal of binary16 (11, 10, 5, 16, 12, 13, 1024, 2048, 4096, 31, 33, 47, 63, `cert16`), and does its PROOF lean on a fixed-size
trick (kernel evaluation over the 2^11 significands, a 13-way case split on the shift, `decide` on a constant) that has
no parametric counterpart? Verdicts: **AS IS** (no literal, or only generic variables: reusable verbatim), **MECH**
(the literals become expressions of `W`, `P`; the proof keeps its shape, only the arithmetic goals change from
`omega`-on-numerals to a short symbolic argument), **NEW** (a new proof idea is needed). Line counts are those of the
fdiv16 files.

| file (lines) | declarations | verdict | what changes |
|---|---|---|---|
| `SpecFacts` (311) | `restore_spec` (`restQuo d x (n+1) = 2^n * x / d`, `restRem d x (n+1) = 2 * (2^n * x % d)`) | AS IS | already format-agnostic (the design note FORMAT.md says so); instantiated at `n = P + 1` |
| `Cert16` (543) | `cert16`, `Cert16Bridge` | SUPERSEDED | `design/fdiv-param/CertF.lean` (691 lines, `certF_bridge`, `fdivF_cert`, `divide_iff_certAllF`, standard axioms, no `sorry`) proves the rounding certificate for EVERY format and `cert16_bridge_of_certF` recovers the binary16 one: this is the piece that was done at WP-H1 |
| `DpModel` (239) | `expField`, `fracField`, `sig16`, `effExp` and their bounds (47-85) | AS IS + MECH | `expF`, `fracF`, `sigF`, `qexpF`, `sigF_pos`, `expF_lt`, `fracF_lt` are in `CertF`; `effExp_le` (`effExp x <= 2^W - 2` for finite x) needs one new lemma (30 lines) |
| | `norm1`..`norm4`, `normLz`, `norm_spec` (30-45) | NEW | the 8/4/2/1 greedy stages are specific to 11 bits; the parametric statement is by induction on a step count (`norm_spec`: `2^(P-1) <= m'`, `m' = m * 2^lz`, `lz <= P - 1`), about 60 lines |
| | `dpNa`, `dpLz`, `dpQq`, `dpRem`, `dpAdj`, `dpQm`, `dpSt0`, `dpEoff`, `dpSh`, `dpQs`, `dpInc`, `dpMag`, `dpWord`, `dpResult` (87-130) | MECH | definitions: `4096 -> 2^(P+1)`, `2048 -> 2^P`, `33 -> OFF + 1`, `12 -> P + 1`, `47 -> emax + OFF` |
| | `qm_st0`, `dpQq_bounds`, `dpM0_eq`, `dpQm_st0`, `dpEoff_spec` (140-239) | MECH, the costly kind | the bounds `4096 * na / nb in (2^11, 2^13)` are `omega` over numerals today; symbolic they need `Nat.div_lt_iff_lt_mul`, `Nat.le_div_iff_mul_le` and one NONLINEAR product `na * 2^(P+1)` kept as an atom (the core has no `nlinarith`; H2 had to do these by `calc`): about 2x the lines |
| `DpRound` (282) | `scale_le`, `scale_ge`, `scale_lt`, `scale_gt`, `mullt`, `two_zP_sub`, `two_zP_add`, `low_std`, `low_std_lt_a/b`, `low_floor`, `up_le`, `up_lt_a/b` | AS IS | stated over abstract `D S N T X`, `nb M P y z qm M0`: no binary16 number appears (about 150 lines: the whole certificate-interval half) |
| | `sh_cases`, `core_t`, `core_f` | NEW | the 13-way `rcases` on `sh <= 12` plus `omega` has no parametric analogue; the symbolic proof splits `u = qm / 2^sh`, `v = qm % 2^sh`, the parity of `u`, and closes by `Nat.mul_le_mul` calcs (about 100 lines each) |
| | `core_floor` | AS IS | already symbolic |
| | `scale_id`, `fields_grid` | MECH | literals `24, 33, 47, 11, 1024, 2048, 30` become `emax + P - 2 ...`, `2^T`, `2^P`, `2^W - 2` |
| `DpCert` (342) | `dpSh_normal/sub/zero`, `dpQm_bounds`, `dpQm_mul`, `dpZ_t/f`, `dpQs_*`, `dpInc_false_zero`, `dpMag_eq`, `dpZ_bounds`, `dpZ_2048`, `qexp16_eq`, `dp_scale`, `dpWord_fields` | MECH | thresholds `33, 21, 20, 12` and ranges `[2048, 4096)` parametrized; the three-regime case structure (normal, subnormal with shift, flush) is unchanged |
| | `c0_of`, `cert_fin_grid`, `cert_inf_grid` | MECH | stated against `cert16` and `BitVec 16`; the generic form is against `certNF` of `CertF` (`certNF_iff`, `thr_iff` are already format-generic) |
| `DpFinal` (232) | `dpSh_le`, `dpShU_eq`, `dpJ_le`, `dp_cert_ovf`, `dp_cert_noovf`, `dpResult_eq` | MECH | the overflow / normal / subnormal split on `eoff` against `63, 33, 21`, symbolic in `W`, `P` |
| `DpBv` (874) | `toNat_append_add`, `toNat_zero_append`, `getLsbD_div`, `getLsbD_zero_eq`, `ofNat_toNat'`, `beq_ofNat_iff`, `beq_eq_decide`, `ofNat_le_iff`, `decide_ofNat_le`, `orR`, `orR_iff` (25-100) | AS IS | generic in the width `n` (`getLsbD_top13` is the one literal: 3 lines) |
| | `ea`, `fa`, `sgn`, `nz`, `ma`, `xe` + `_toNat` lemmas (102-150) | MECH | widths `5, 10, 11, 16 -> W, T, P, K` |
| | `z8`..`n4`, `lz`, `norm_bv` (the kernel evaluation `forall n < 2048`), `n4_toNat`, `lz_toNat` (162-190) | NEW | `norm_bv` is the one proof in the whole layer that ENUMERATES (2^11 cases, kernel `decide`); D2's linear one-bit-stage normalizer is proved by induction instead |
| | `nb12`, `remR`, `remR_succ`, `dig`, `remR_toNat`, `dig_iff`, `qqN`, `tb0`, `tbS`, `testBit_qqN`, `qqN_eq`, `qq`, `qq_bit`, `qq_toNat` (196-310) | MECH | these are inductions on the step index already (`remR` is the row recurrence); only the widths 11/12/13 change |
| | `adj`, `qm`, `st0`, `Fin2`, `Q`, `R13`, `Adj`, `Qm`, `ST0` and the `_toNat`/`_iff` lemmas (313-395) | MECH | |
| | `Eoff`, `Ovf`, `Nrm`, `Dsh`, `Big`, `Sh` and `Eoff_toNat`, `Ovf_eq`, `Nrm_eq`, `Dsh_toNat`, `Big_eq`, `Sh_toNat` (399-480) | NEW (D2) / MECH (D1) | D2 has no `dsh`/`big`/`sh`; the denormalizer's activation chain replaces them (about 120 lines); `Eoff_toNat` becomes a modular-sum identity at width `EW` |
| | `sq1`..`sqs`, `sT1`..`sSt`, `sh_bits` (16 cases), `stage_step`, `stage_toNat`, `stage_sticky`, `stage_first`, `shift_arith`, `shifter_spec` (481-610) | NEW | the 4-stage barrel with `sh_bits` over the 16 values of 4 bits is specific; the counter-chain shifter of D2 is an induction on the stage with the same sticky arithmetic (`mod_ne_zero_mul`, `stage_step` carry over) |
| | `Q1..Q3`, `Qs`, `St1`, `Inc`, `Ef`, `Efq`, `Mag` and `_toNat`/`_iff` (608-695) | MECH | |
| | `aNan`, `aInf`, `aZero`, `cNan`, `cInf`, `cZero`, `wInf`, `wZero`, `wFin`, `Out`, `_iff`/`_eq` lemmas, `cat_word`, `wInf_eq`, `wFin_eq`, `Out_fin`, `F_eq` (696-874) | MECH | `0x7C00 -> 2^W - 1` shifted by `T`; the table is `divide_table` of `CertF` |
| `DpGlue` (416) | `bv1`, `val_ne_zero_iff`, `val_mod`, `g_any`, `g_bit`, `g_eqv`, `g_nan`, `g_infz`, `g_nz`, `g_ge`, `g_extract`, `g_extract0`, `g_copy`, `g_cat`, `g_cat0`, `bit_of`, `bv1_of`, `g_extract_of`, `g_extract0_of`, `g_zero_test`, `g_notbit`, `g_sticky`, `g_mux`, `g_mux3`, `g_mux5`, `g_sub`, `g_addz`, `g_shl1`, `g_shl2`, `g_shr1`, `constBit_toNat`, `shl_val`, `shr_val` | AS IS | one lemma per SHAPE of equation, all stated for general widths (`{w W lo}`) |
| | `lz_bits`, `g_lz`, `g_qm`, `g_eoff`, `g_qq` | MECH | the four-stage `lz`, the 13-bit `qm`, the specific `eoff` shape: re-shaped to the chosen design |
| | (new) family lemmas | NEW | `sv_equations` states a generate family as `forall i < P + 2, forall k < P + 1, st.boolAt "rr" (rmN (P + 1) (i + 1) 0 + k) = ...` (section 4.1, probe `p27`); the glue must show by induction on `i` that the row slice at `i` is the recurrence `rowR i` of the `BitVec` model. About eight lemmas: `rmN` arithmetic (`rmN (P+1) i 0 = i * (P + 1)`), slice extraction of a row, a row-mux, a row-shift, a row-subtract, the bit-select into `qq`, the activation chain |
| `reference/fdiv16.lean` (288) | the `kc_*` closed constants (`decide`), the `b_<signal>` chain, `solution` | MECH + NEW | 111 `have`s become about 75 plus one per family; the closed constants `kc_31_5 ...` are not closed any more: constants built by window writes (`kv`, `nrmth`, `ovfth`, the words) need one lemma each (about 25 lines) with hypotheses on `W`, `P` |

Tally by declaration spans of the five `Dp*` files and `DpGlue` (2,256 declaration lines of 2,385; the rest is
headers and comments): **AS IS 557 lines (25 %), MECH 1,424 (63 %), NEW 275 (12 %)**, plus `restore_spec` (AS IS) and
`CertF` (691 lines, DONE). The NEW lines are small in fdiv16 and grow in the parametric proof (the enumerations
become inductions): ESTIMATE 700 to 900 lines. The reusable half is the CERTIFICATE (`CertF`, `DpRound`'s interval half, `DpGlue`'s shape lemmas); the
re-derivation half is exactly the part that used enumeration or case splitting on numerals. No lemma needs a solver,
`bv_decide`, `native_decide` or Mathlib.

## 3. (b) The parametric reference: datapath, two designs, validation, scores

### 3.1 The datapath at `(W, P)`

Notation: `K = W + P` (storage), `T = P - 1` (trailing bits), `emax = 2^(W-1) - 1` (also the bias).

1. Unpack, classify (`a_nan`, `a_inf`, `a_zero` as in fdiv16 with `W`-bit exponent and `T`-bit fraction), effective
   exponent `xa = nza ? ea : 1`, significand `ma = {nza, fa}` (`P` bits, nonzero for a finite nonzero operand).
2. Normalize `ma` to `na in [2^(P-1), 2^P)` counting the shifts `lza` (a subnormal operand has up to `P - 1`).
3. **`P + 2` restoring-division steps** on `na`, `nb`: `qq = 2^(P+1) * na / nb` (`P + 2` bits, in `[2^P, 2^(P+2))`) and the
   remainder `rr[P+2] = 2 * (2^(P+1) * na mod nb)` (`restore_spec` at `n = P + 1`). `adj = ~qq[P+1]`, `qm` the `P + 1` bit
   quotient with the top bit set, `st0 = (qq[P+1] & qq[0]) | (rr[P+2] != 0)`.
4. Exponent sum `eoff = (xa - lza) - (xb - lzb) + emax + OFF - adj` modulo `2^EW`, with `OFF` a multiple of `2^W` so
   that `eoff[W-1:0]` IS the result exponent field. Thresholds: `eoff >= OFF + 1` normal (`nrm`), `eoff >= OFF + 2^W - 1`
   overflow (`ovf`); at `W = 5`, `OFF = 32`: the `33` and `63` of fdiv16.
5. Denormalize: `qs = qm >> sh` with `sh = nrm ? 0 : min(OFF + 1 - eoff, P + 1)` and a sticky bit that collects the
   dropped bits (at most `P + 1` shifts empty `qm`).
6. Round to nearest even by ADDING `inc = rb & (st1 | qs[1])` to `{ef, qs[P-1:1]}`: a carry runs into the exponent field,
   and the all-ones pattern it can reach is exactly infinity (the overflow-by-rounding case), so no second check.
7. Special-case table `c_nan`, `c_inf`, `c_zero`, `ovf` as in fdiv16; canonical NaN `0 1..1 10..0`.

### 3.2 The two designs

Both are in `h3/`, module `fdiv #(parameter int W = 5, parameter int P = 11)`, ports `a`, `b`, `q` all `[W+P-1:0]`.

* **D1 `fdivp.sv`** (165 lines): the natural parametric form. Counts as parameters: `NS = $clog2(P)` normalizer stages
  (shift by `2^(NS-1-i)`), `SW = $clog2(P+2)` shifter stages (`>> 2^j`), `OFF`/`EW`/`KOV`/`NRMTH`/`OVFTH`/`BIGTH` sized
  localparams computed with `2**`, replication `{W{1'b1}}` for the special words, a `localparam` inside the generate.
  It is a logarithmic-depth normalizer and shifter, the architecture of the 16-bit reference (not the same netlist: the shifter differs).
* **D2 `fdivp2.sv`** (190 lines): the SAME divider and special-case table with every construct the tactics refuse
  replaced by an affine one (section 4.1): no `$clog2`, no `2**e`, no replication, no sized localparam, no
  localparam in a generate, no genvar value. The counts are `P`-affine: a LINEAR normalizer (`P - 1` stages of a one-bit
  shift, an `EW`-bit register counting the shifts down), `P + 2` division steps, a LINEAR denormalizer (`P + 1` stages, an
  activation bit `act[j] = e_r[j] < nrmth` that shifts `qm` right by one and increments the exponent register until it
  reaches `OFF + 1`), `EW = W + P + 1`, `OFF = 2^(W+P)`; vector constants are written by window writes
  (`assign kv[W-2:0] = '1; ...`). Fragment-clean, bigger (section 3.4), and every
  stage is a one-bit step, so each proof is a plain induction (ESTIMATE: the easier of the two to prove).

### 3.3 Validation

* **MODEL**: `h3/fdivp_model.py` is a bit-accurate Python model of the datapath (`model`) plus two oracles:
  `oracle_int` (exact integer round-to-nearest-even of the quotient in units of the least subnormal, independent of
  the datapath) and `oracle_frac` (the `Fraction` oracle `svgolf/spec/validate/oracle.py`, the one validated against the
  Lean spec). The oracle chain, all MEASURED (outputs in `h3/results/`): the model equals `oracle_int` on EVERY pair of
  every format with `K <= 10` (28 formats, 9.3 x 10^6 pairs, `val_py.py`); `oracle_int` equals the `Fraction` oracle on
  every pair at `K <= 8` and on 2000 random vectors at every sampled format; the C++ oracle `oracle.h` equals
  `oracle_int` on every pair at `K <= 7` and on a stride-7 sample of the divisors at `K = 8, 9` (`cmp_oracle_cpp.py`).
* **Exhaustive Verilator** (`h3/tb_fdivp.cpp`, `h3/run_v.py`, against the C++ 128-bit oracle `h3/oracle.h`, valid for `P` up to about 40): ALL operand pairs at ALL 66 formats with `K = W + P <= 14` (`W, P >= 2`,
  3.82 x 10^9 pairs per design), D1 and D2: **0 mismatches** (MEASURED; the results are in `h3/results/`). Plus the two
  formats with 2^32 pairs, `(5, 11)` (binary16) and `(8, 8)` (bfloat16-like), exhaustively: both designs, **0 mismatches over all 2^32 pairs of each** (8.6 x 10^9 evaluations per design, MEASURED).
* **Sampled** (`h3/gen_vec.py`, `h3/tb_vec.cpp`, `h3/run_vec.py`: 200,000 vectors per format; the expected value is
  `oracle_int`, cross-checked against the `Fraction` oracle on 2000 of them): a quarter is the full cross product of
  the field extremes (both signs, exponents `0, 1, 2, emax-2 .. emax+2, 2^W-3 .. 2^W-1`, `emax +- P`, fractions `0, 1,
  all-ones, half`), the rest is uniform random, exponents near the bias with tie-shaped fractions (long runs of zeros or
  ones, a trailing `10..0`), exponent differences near the underflow and overflow boundaries, and power-of-two or
  subnormal divisors. D1 at (8,24), (8,8), (11,53), (5,11), (2,30), (4,20), (6,30), (10,40), (15,48), (2,62), (3,60), (12,20), (20,12), (16,16);
  D2 at (8,24), (8,8), (11,53), (5,11), (2,30), (6,30), (15,48); **0 mismatches** everywhere (MEASURED).
* What validation does NOT give: the symbolic theorem. It finds bugs in a design and in the contract (FORMAT.md's
  own rule); the proof is for every `(W, P)`.

### 3.4 Scores (`score/score.py`, area in NAND2-GE and depth)

| design | (2,2) | (5,11) binary16 | (8,8) bfloat16 | (8,24) binary32 | (11,53) binary64 |
|---|---|---|---|---|---|
| flat t4 (= `tasks/fdiv16/reference/fdiv16.sv`, fixed size) | | **1929.778 / 299** | | | |
| **D1** (natural, log stages) | 93.322 / 20 | **1911.446 / 300** (1290 gates) | 1251.195 / 181 | 7450.536 / 1256 (4905 gates) | not measured (the scorer did not finish within 9 minutes under load) |
| **D2** (fragment-friendly, linear stages) | 96.32 / 18 | 2314.058 / 295 (1618 gates) | 1498.496 / 179 | 9813.601 / 1279 (6899 gates) | not measured |

D1 at `(5,11)` is 1.0 % SMALLER than the hand-flattened reference (1911.446 against 1929.778 GE, depth 300 against
299; the difference is in the shifter and the normalizer, I did not analyse it further): generality costs no area. D2 is
+19.9 % over t4 at `(5,11)` and +21.1 % over D1 there; over D1 it is +19.8 % at `(8,8)` and +31.7 % at `(8,24)`. That is
the price of the linear normalizer/denormalizer and the wider exponent register, i.e. the price of staying inside
today's fragment. The depth at larger `P` is the serial divider: 300 at `P = 11`, 1256 (D1) and 1279 (D2) at `P = 24`,
roughly quadratic in `P` (each of the `P + 2` steps is a `P + 1` bit ripple compare and subtract: READ from the design).

## 4. (c) Tactic-fragment readiness on the tip

### 4.1 Construct by construct (MEASURED, `h3/probes/p*.sv`, `h3/probes.lean`, `h3/probes2b.lean`)

Each probe is a 5 to 20 line module with parameters `(W, P)` run through `load_sv` and `sv_structure?` /
`sv_equations?` (the refusal text is the finding). "D1" and "D2" name the design that uses the construct.

| probe | construct | tip `5d17a92e` | where used | workaround |
|---|---|---|---|---|
| `p01` | parametric vector widths `[W+P-1:0]`, `localparam integer K = W + P`, XOR | **accepted** (structure + equations) | both | - |
| `p02` | `localparam integer NS = $clog2(P)` | **refused** at `sv_structure` and `sv_equations`: "localparam `NS`: `$clog2` is outside the v1 fragment (it is not a linear function of the parameters; a localparam may use + - *, and / % by an integer literal)" | D1 (`NS`, `SW`, `EW`) | counts that are P-affine (D2's linear stages) |
| `p03` | `logic [P:0][P-1:0] r`, loop-indexed ROW `r[i+1] = r[i] << 1` with parametric dimensions | **accepted**: family `g`, rank relation printed; the `H2` gap G2 is CLOSED (gate 4a) | both | - |
| `p04` | `r[i+1] = r[i] << i` (a genvar as a shift amount) | **refused**: "site `g#0`: operand of a shift that is not a signal access, a sized literal or an unsized constant ..." | (neither: D1 shifts by `2**e`) | gate 4b (`wpb2g4b`, not merged: "a genvar as the amount of a shift"); NOT measured here |
| `p05` | `localparam integer SH = 2 ** i;` inside the generate | **refused**: "unsupported generate item `GenerateDecl:LocalParam`" | D1 (`SH`, `SJ`) | none inside a generate; compute outside or avoid exponential amounts |
| `p06` | replication `{{W{1'b1}}, {P{1'b0}}}` | **refused**: "replication (outside the v1 fragment)" | D1 (`w_nan`, `w_inf`, `w_zero`) | window fills (`assign q[K-1:P] = '1;`, accepted, `p07`) |
| `p07` | window writes with fills `q[K-1:P] = '1; q[P-1:0] = '0` | **accepted** | D2 (the vector constants and the words) | - |
| `p08` | `&a[K-2:T]`, `~|a[T-1:0]`, `a[P-1:0] >= b[P-1:0]` into one-bit signals | **accepted** | both | - |
| `p09`, `p22` | `a[W-1:0] >= P + 1` (a parameter expression as a comparison operand) | **refused**: "width conversion of a nested conversion or a constant that is not an unsized integer" (`plain#0`) | D1 (`BIGTH`, `NRMTH`, ...) | vector constants by window writes, compare vector with vector |
| `p20` | `a[W-1:0] >= 3`, `== 3` (small unsized literals) | **accepted** | both | - |
| `p21` | `a[P-1:0] == P` (a bare parameter as operand) | **refused**, same message as `p09` | D1 | vector constants (above) |
| `p23` | `a[W-1:0] + P` (parameter as an arithmetic operand) | **refused**, same message as `p09` | D1 (`eoff`'s `KOV`) | vector constants |
| `p24` | `localparam integer OFFV = 2 * W + 3;` used as a width | **accepted** (affine `integer` localparams are the supported kind) | D2 (`K`, `T`, `EW`) | - |
| `p25` | `localparam [W-1:0] ONES = 1;` (sized localparam) | **refused**: "localparam `ONES`: only `int`/`integer` (32-bit signed) localparams are in the v1 fragment" (the same refusal as `p19`'s `KOV`, here from the tactics) | D1 | `integer` localparams only |
| `p26` | `e == 5'd3` (a sized literal against a `W`-bit vector) | **accepted** | (neither) | - |
| `p10` | `act[i] = (a[W-1:0] > i)` (genvar VALUE in a comparison) | **refused**, same message as `p09` (`g#0`) | (D1 variant) | the activation chain of D2 (`act[j] = e_r[j] < nrmth`, vector against vector) |
| `p11` | `x = nz ? ea : 1;` `y = ea + b[W-1:0] + 1;` (unsized constants) | **accepted** | both | - |
| `p12` | `x = c ? a[W-1:0] : b[W-1:0]` (vector `?:`) | **accepted** | both | - |
| `p13` | `generate if (W > 2) ... else ...` | **refused**: "conditional generate (outside the v1 fragment)" | neither | not needed |
| `p14` | `logic [P-1:0] r [0:P]` (unpacked array) | **refused**: "out-of-tier module members are present" | neither | packed 2-D rows |
| `p15` | generate bound `i < W + P - 2`, `x[i] = a[i] & b[i+1]` | **accepted** (affine bounds and indices) | D2 | - |
| `p16` | `qq[P+1-k] = ge[k]` (a DESCENDING affine index) | **accepted** | both | - |
| `p17` | `a[P-1:0] << W` (a parameter as the shift amount) | **refused**, same message as `p04` | neither | - |
| `p18`, `p27` | the divider family: `ge[k] = (rr[k] >= nbx); dd[k] = rr[k] - nbx; qq[P+1-k] = ge[k]; rr[k+1] = ge[k] ? (dd[k] << 1) : (rr[k] << 1)` over `k < P + 2` | **accepted** (4 family sites; the equations come out as `forall i < P + 2, forall k < P + 1, st.boolAt "rr" (rmN (P+1) (i+1) 0 + k) = if st.boolAt "ge" i = true then XF.shlBits ... else XF.shlBits ...`, `eq_ge_g_0 : st.boolAt "ge" i = decide (XF.val ... >= XF.val ...)`) | both | - |
| `p19` | D1 as a whole through `load_design_sv2` | **refused at LOAD**: "localparam `KOV`: unsupported node `ConversionExpression:width` in a constant context" (a SIZED localparam `localparam [EW-1:0] KOV = ...`) | D1 | the design never reaches the tactics |
| `d2_probe` | D2 as a whole, `sv_structure?` | **accepted**: 74 plain sites plus the families `norm`, `div`, `den`, `efg`, `nanz`, rank relation printed (18 s, mostly the load) | D2 | - |

Reading: **D1 is outside the fragment in six independent ways and cannot even be loaded** (the checker's `design`
stage would stop it); **D2 is entirely inside it**. The six missing features that would make D1 acceptable, with my
estimate of their cost (ESTIMATES, none measured): an opaque `$clog2`/`2**e` localparam with facts as hypotheses
(the biggest, a design decision for the tactic owner), sized localparams in the loader (small), a `localparam` inside a
generate (small), replication with a parameter count (medium, `p06` shape), a parameter or genvar expression as a
constant operand of a comparison (medium), and a shift amount that is not a bare signal (`>> 2**j`; the hardest, 4b does
not cover it). None is needed if the reference is D2.

### 4.2 Gate 4b

The tip has gates c, d, 3a, 3b and 4a (rows `p03`, `p07`, `p08`, `p15`, `p16`, `p18` are their customers: part
selects, rows, window fills). Gate 4b, "a genvar as the amount of a shift", is committed on `wpb2g4b`/`wpb2g4c`
(`3755d02c`, `87f0e2b4`, 2026-11-01 23:12) and NOT merged into `svgolf-prep` (`git merge-base --is-ancestor` says so). I did
not build it (a second build tree would compete with the suite). Its only relevance here: D2 has NO run-time or
genvar shift amount (every shift is by one, by a constant), so D2 does not need it; D1 needs exponential amounts
`<< 2**(NS-1-i)`, which 4b (a BARE genvar) would not accept either.

### 4.3 Cost of the tactics on the parametric design

All MEASURED UNDER HEAVY LOAD (load average 135 to 155: the lead's suite, `yosys-abc` and other agents; `LEAN_NUM_THREADS=2`, `nice`).
Wall clock of a whole `lake env lean` run on a file with ONE tactic call; the baseline (import + `load_sv`, no tactic) is
**20 s**, the "net" column subtracts it. Synthetic chains (`h3/chain/c<N>_whole.sv`: `N` plain sites over `[K-1:0]`
vectors, `x_i = x_{i-1} & a` / `^ a`, parametric `(W, P)`, rank `fun p => p`; generator `h3/gen_chain.py`), so that the
site count is the only variable.

| design | sites | tactic | wall | net |
|---|---|---|---|---|
| `c10_whole` | 11 | `sv_structure (rank := ...)` + `all_goals (intros; omega)` | 38 s | 18 s |
| `c20_whole` | 21 | same | 69 s | 49 s |
| `c40_whole` | 41 | same | **> 190 s (timeout)** | > 170 s |
| `c10_whole` | 11 | `sv_equations` (only `inputsKnown` left) | 43 s | 23 s |
| `c20_whole` | 21 | same | 69 s | 49 s |
| `p27` (the divider family: 4 plain + 4 family sites) | 8 | `sv_structure` with a family rank, residuals closed by `all_goals (intros; sv_rowmajor; omega)` | simp 20.6 s (2.8 + 1.6 + 4.5 + 11.7) | about 20 s |
| `p27` | 8 | `sv_equations` (19 residual goals: `inRange_1..9`, `width_1..2`, `cover_1..5`, `bitRead`, `inputsKnown_1..2`) | simp 22.1 s + tactic 6.3 s + typeclass 3.4 s | about 36 s |
| `c10_win` (the unpack shape: two window writes and two window reads per stage) | 21 | `sv_structure` | simp 4.3 + 3.2 + 12.5 + 36.1 s | about 56 s |
| **D2 as a whole** | about 90 (74 plain + 16 family) | `sv_structure` with a hand rank (`h3/d2_struct.lean`) | **> 280 s at 4M heartbeats**; 41 s then a heartbeat stop at 1M | > 260 s |
| **D2 as a whole** | about 90 | `sv_equations?` / `sv_equations` (`h3/d2_eq.lean`) | **> 280 s at 3M heartbeats** (two runs) | > 260 s |

Reading (MEASURED data, the extrapolation is mine):

* **For a flat fdiv16 netlist the same tactics cost under 1 s (structure) and about 30 s (equations)** (H2): the closed
  site list is DECIDED (READ: `fdiv16.lean`, "`sv_structure` DECIDES its four obligations as closed statements"). A
  parametric netlist is not a closed term and the profiler puts the time in `simp` (about 21 s of `simp` in the profile of
  `c10_whole`, run `chainA2`): a fixed cost of about 15 to 20 s per call and a cost that grows faster than linearly in the number of
  sites: 11, 21, more than 41 sites cost 18, 49, more than 170 s, i.e. about `0.1 * n^2` seconds. Nothing overlaps in the chains (one
  signal per site), so the growth is not window-overlap work; where it comes from I did not find out (the tactic source
  is the owner's): a gap to REPORT, G5' of section 7.
* **Extrapolation to D2** (`n` about 90): about 800 s for `sv_structure` and about 800 s for `sv_equations`,
  i.e. 13 minutes each on this loaded machine (ESTIMATE; the quiet-machine factor is unmeasured and may be large, the load average was 135 to 155; both
  runs on D2 itself hit my 280 s ceiling, which is consistent with it). The long measurement of the real numbers is the
  first thing to do after the all-clear (one acquisition of 15 to 25 minutes: D2 `sv_structure` with `maxHeartbeats 0`).
* **The residual goals of a family** (`rmN` atoms): after `sv_structure` on a loop-indexed ROW family the rank
  obligations carry `rmN (P+1) (i+1) 0`, an opaque row offset, and plain `omega` fails (6 of the `p27` obligations:
  `omega could not prove the goal ... d := rmN (P+1) (i+1) 0, e := rmN (P+1) 0 0`). The library macro `sv_rowmajor`
  (`CombViewTactic.lean:228`, "NOT part of `sv_structure`: the player calls it, on goals that mention `rmN`") rewrites them
  to lexicographic `(row, column)` comparisons and then `omega` closes all of them: `all_goals (intros; sv_rowmajor;
  omega)` PASSED on `p27`. The design layer must therefore carry that closer for every family (D2 has five).


## 5. (d) The statement and the trusted-code review

### 5.1 What exists (WP-H1, `design/fdiv-param/`)

`TASK.md` (the design note: options A to D), `Spec.lean` (Option A, the statement over a new `CombTask2`),
`SpecLocal.lean` (Option C, the statement over the EXISTING `CombTask`), `Task.lean.patch` + `Comb2.lean` (the
`CombTask2` addition and its proof helpers), `task.draft.json` (`kind: comb-family`, two parameters, `statement.constant
= SvGolf.Tasks.FdivP.Statement`, probe points `W=2,P=2` ... `W=8,P=24`), `CertF.lean` (the certificate, DONE).

### 5.2 Review against the tip `5d17a92e` (READ, plus `git apply --check`)

* **The patch applies cleanly** to the tip (`git apply --check svgolf/design/fdiv-param/Task.lean.patch`, run in the
  `wph3` worktree). It is PURELY ADDITIVE: 35 lines after `end CombTask` in `SvGolf/Task.lean` (`structure CombTask2`,
  `CombTask2.atPoint`, `CombTask2.SatisfiedAt`, `CombTask2.Statement`); `Comb2.lean` (42 lines) adds four helper
  restatements to `SvGolf/Comb.lean`, each one line of `CombTask.satisfiedAt_of_comb` / `exists_run` at `t.atPoint N M`
  (the statement at one parameter pair IS `CombTask.SatisfiedAt` of `atPoint`, by `rfl`). Nothing existing changes.
* **Users of `CombTask`** (all unaffected by either option): `SvGolf/Task.lean`, `SvGolf/Comb.lean`; the trusted
  per-task statements `tasks/{_example, add, clmul, mul, aes_sbox, fdiv16}/Spec.lean` (four use `Statement :=
  task.Statement`: `_example`, `add`, `clmul`, `mul`; `aes_sbox` and `fdiv16` use `StatementFixed`); the negative tests that refute through
  `CombTask.not_statement_of` / `counterexample` (`tests/{add, clmul, mul, fdiv16}/negative/Refute.lean`) and
  `tests/mul/validate/RunAgree.lean`. A new task adds one `Spec.lean` and one `tests/fdivp/negative/Refute.lean`, nothing
  of the others moves.
* **check.py with TWO parameters** (READ; the script was not run on a two-parameter task, none exists yet): the
  parameter machinery is name-list based (`unsupported_check_points`, `probe_points`, `parse_point`, `point_str`, the
  extract stage's "exactly the parameters" test), so it is already N-ary. The one place that is not is
  `tactics_probe_text` (`check.py:1298`): `kind == "comb-family" and len(params) == 1`, else it returns `None` and
  `--tactics` prints "not checked: task kind ... is not a combinational task" for a two-parameter task. It is ADVISORY
  (never changes `accepted`), a few-line generalization to N binders; for gate 1 the probe can simply be run by hand
  (`h3/probes.lean` is that probe). I did not edit `check.py`.
* **The leaderboard** ranks at one scoring point: `scoring_point(task)` is `{name: int}` from `task["scoring"]["params"]`
  (`leaderboard/leaderboard.py:311`), so `{"W": 5, "P": 11}` works unchanged (READ; `tests/leaderboard` uses one-parameter
  toy tasks only).
* The 2-parameter `design` stage (`load_design_sv2` defines `name.sem : Nat -> Nat -> Design2`) is covered by the
  probes: D2 loads (`d2_probe`), D1 is refused at load (`p19`).

### 5.3 Proposal: the minimal trusted change is ZERO lines of the library

**Option C, `SpecLocal.lean` as the new trusted file `tasks/fdivp/Spec.lean` (about 110 lines, drafted and compiled at
WP-H1).** The statement is

    Statement sem := forall W P, 2 <= W /\ 2 <= P -> (task W P).StatementFixed (sem W P)

with `task W P : CombTask` the fixed-size task (`inputs := [("a", W+P), ("b", W+P)]`, `outputs := [("q", W+P)]`,
`fn := fdivBits W P`) and `fdivBits W P a b = divide <W, P> .roundTiesToEven a b` (the casts along `Format.k = W + P`
are value-preserving, `fdivBits_toNat`; `fdivBits_five_eleven`, `fdivBits_eight_twentyfour` are `rfl` to `fdiv16`,
`fdiv32`; `statement_fdiv16 : Statement sem -> Fdiv16.Statement (sem 5 11)`, so a parametric proof subsumes the 16-bit
one). Why C and not A for THIS task: (i) no trusted-library file changes, so no rebuild of `SvGolf` and of every task
library that imports it and no invalidation of the checker's cached results (`check.py` hashes `.lake/build` into its
cache key; ESTIMATE: a library rebuild is a full-suite cost); (ii) the proof side loses nothing, because
`CombTask.satisfiedAt_of_comb` applies to `task W P` at `N = 0` unchanged, which is all `CombTask2.satisfiedAt_of_comb`
restates; (iii) A is the better shape once a SECOND two-parameter task exists (the lead's own recommendation in
`TASK.md`), and then moves in one additive patch. **Decision requested: C now.**

Small non-trusted pieces for gate 1 (PLANNED): `tasks/fdivp/task.json` (from `task.draft.json`; `banlist`: `/ % **`),
a per-probe-point oracle wrapper for the checker's functional stage (a thin call of `svgolf/spec/validate/oracle.py` at
`(W, P)`; the vectors come from `h3/gen_vec.py`'s shapes), `tests/fdivp/negative/Refute.lean` (refutation at ONE
`(W, P)` through `Statement`'s `forall`, the same shape as `fdiv16`'s), the README, and the `check.py` N-ary tactics
probe if the lead wants `--tactics` for it (not needed for acceptance).

## 6. (e) Math-layer plan, sizes, implied time limit, go/no-go

### 6.1 Pieces

Assumes the reference is D2 (section 3.2; D1 cannot be loaded today). Sizes are ESTIMATES from the tally of section 2
(the fdiv16 spans, scaled by the verdict: MECH x1.3, NEW x3), with H2's own record as the calibration: H2's gate-0 estimate
was 1,750 to 2,000 lines for G1+G2 and the result was 2,673 (`Dp*` 2,385 + the solution 288), 35 to 50 % over, so the
planning figure carries that factor. Slot-hours are Lean acquisitions only (the agent time is elsewhere).

| piece | content | new lines | slot-hours | go / no-go |
|---|---|---|---|---|
| H3-0 | statement (`tasks/fdivp/Spec.lean` = `SpecLocal`), `task.json`, README, oracle wrapper, `Refute.lean` | 110 Lean + 250 other | 1 | **GO** (zero trusted-library change) |
| H3-1 | certificate for every format (`CertF`, `FormatFacts`) | 0 (DONE, 691 + 56) | 0 | **DONE** |
| H3-2 | normalizer: `P - 1` one-bit stages with an exponent register (`norm` family), by induction; unpack and classification at `(W, P)` | 300 | 1.5 | **GO** |
| H3-3 | divider: `remR`/`dig`/`qqN` at width `P` (`restore_spec` at `n = P + 1`), `adj`, `qm`, `st0` | 350 | 1.5 | **GO** (mechanical) |
| H3-4 | exponent sum at width `EW` (modular identity), thresholds `nrm`, `ovf` | 250 | 1.5 | **GO** |
| H3-5 | denormalizer: activation chain, sticky, increment, `mag` | 400 | 2 | **GO** |
| H3-6 | the packed-result certificate: `DpCert` + `DpFinal` at `(W, P)`: three regimes (normal, subnormal with shift, flush; overflow) | 900 | 4 to 5 | **GO**, the largest and the riskiest: no new idea, but the symbolic nonlinear steps (`na * 2^(P+1)`, `nb * qm`) have to be done by hand without `nlinarith` |
| H3-7 | special cases and the final composition `F_eq : Out a b = fdivBits W P a b` | 250 | 1.5 | **GO** |
| H3-8 | glue: the family lemmas (row slices by induction), the parametric constants (window-written vectors), the solution file | 600 | 3 | **GO**, new technique (`rmN` row arithmetic), medium risk |
| H3-9 | tactic runs on D2 (`sv_structure` with a rank, `sv_interface`, `sv_equations`) and the residual `inRange`/`width`/`cover` goals (19 for the one-family probe `p27`, hundreds for D2) | 100 | 2 to 10 (6.2) | **CONDITIONAL** on the cost, section 6.2 |
| total | | about 3,260 (planning figure 4,300) | about 19 (route 1 of 6.2) to 27 (D2 as it stands); planning 25 to 36 | |

Order: H3-0 and the design layer first (they decide the time limit), then H3-2..5 in parallel, H3-6 last.

### 6.2 The implied time limit, and what decides it

The solution stage compiles `Solution.lean`: load, `sv_structure`, `sv_interface`, `sv_equations`, the glue chain and
the final theorem. The arithmetic layer (`H3-2..7`) is a prebuilt task library (like `tasks/fdiv16/Dp*.lean`, imported,
not recompiled by the checker), so the stage is dominated by the two tactics. With D2 as it stands: load 10 s +
`sv_structure` about 800 s + `sv_equations` about 800 s + interface and glue (the H2 chain was a few thousand
heartbeats; ESTIMATE 30 to 90 s for 90 sites) = **T about 27 minutes on this heavily loaded machine (quiet-machine factor unmeasured), a 4T rule limit of about
110 minutes** (the fdiv16 figures are T = 32.43 s, limit 130 s). That is not a task anybody will submit to. Three ways out:

1. **Fewer sites (design side, free, my recommendation as the first step of G1).** Cost is about `n^2`: D2 has about
   25 signals that exist only to be named (`eall_*`, `ez_*`, `fz_*`, `a_nan`.., `nza`, `sa`, `sb`, `s`, `ea`, `eb`, `fa`,
   `fb`); merging them into fewer, larger expressions where the fragment allows it (a comparison or a reduction cannot
   be an operand of an operation, so not everywhere) could bring D2 to about 50 sites: `(50/90)^2 = 0.3`, about 4 minutes
   per tactic, T about 9 minutes, limit about 35 minutes (ESTIMATE, unmeasured; the chain data above are the only basis).
2. **A tactic-side fix** (owner of `LeanModels/Sv`, REPORT G5'): the source of the quadratic term is not diagnosed
   (if it is the pairs of sites, skipping pairs that write different signals would make it linear; that is a guess).
   It is what would make every parametric family tractable; it is outside this work package.
3. **A long limit** (the checker's `time_limit_s` is a task parameter): works with no change, costs every submission
   run, and every proof iteration of my own is a 25 minute compile. Not recommended.

H3-9 slot-hours (the row of the table above): with D2 as it stands about 15 compile iterations of 25 minutes (6 to 10
slot-hours); with route 1 about 2 to 3. This is the single largest uncertainty of the plan: **GO for the math layer
regardless** (it does not run the tactics on the whole design: it is a `BitVec` model `F` and its glue lemmas, checkable
piecewise), **CONDITIONAL for the design layer** on one measurement after the all-clear.


## 7. Gaps (REPORT; nothing was patched) and decisions requested

Gaps found at this gate, ranked by what they cost the parametric task. A gap is a report to the owner; the workaround
is what D2 uses.

* **G5'. The parametric `sv_structure` / `sv_equations` cost grows about quadratically in the number of sites** (11, 21,
  more than 41 plain sites: 18, 49, more than 170 s; `sv_equations` the same, 23 and 49 s at 11 and 21), with a fixed cost
  of 15 to 20 s per call, where the flat fdiv16 netlist costs under 1 s. The chains used for the measurement have one
  signal per site and nothing overlaps, so this is not window-overlap work; I did not locate the source (READ of
  `CombViewTactic`/`CombCover` is the tactic owner's). Impact: D2 at about 90 sites is about 13 minutes per tactic; this
  is the cost that sets the task's time limit. Workaround: fewer, larger sites (section 6.2). A fix would make every
  parametric floating-point task tractable.
* **G7. The residual `rmN` goals of a row family are left to the player.** `sv_structure` on a loop-indexed row family
  leaves rank obligations over `rmN` atoms that bare `omega` cannot close; `sv_rowmajor` (a library macro that says it is
  not part of `sv_structure`) closes them (`all_goals (intros; sv_rowmajor; omega)`, passed on `p27`). A PROVING.md line
  for this closer is missing; a tactic that calls it itself would remove a trap.
* **G8. A parameter, a parameter expression, or a genvar as a constant operand, a sized localparam, a `localparam` in a
  generate, replication, a non-bare shift amount, `$clog2`** (section 4.1: `p02`, `p04`, `p05`, `p06`, `p09`, `p10`, `p17`,
  `p19`, `p21`, `p22`, `p23`, `p25`): each refused with a precise message; none is needed by D2. Together they are the
  difference between D2 and the natural D1 (17 % of area at `(5,11)`, 24 % at `(8,24)`).
* **G9. `check.py --tactics` has no probe for a two-parameter task** (`tactics_probe_text` returns `None`:
  `kind == "comb-family" and len(params) == 1`). Advisory only; a few lines to make it N-ary; not needed for acceptance.
* **G10. The exact-rational oracles do not scale to a huge exponent field** (`(24, 8)`, `(28, 4)`: the Python integer
  oracle shifts by `2^23` bits): not a design problem, a validation limit; the exhaustive and sampled runs above stop at
  `W = 20`.

Decisions and requests (for the lead and the maintainers):

1. **Statement: Option C now** (zero trusted-library change; `CombTask2` stays an option for a second two-parameter task).
2. **Reference: D2, with a site-count reduction as the first step of gate 1**, unless the tactic owner takes G5'. D1's
   17 to 24 % area advantage is real but D1 cannot be loaded; the six features of G8 are the price of it.
3. **The all-clear for the long measurement** (one acquisition of 15 to 25 minutes, D2 `sv_structure` and
   `sv_equations` with `maxHeartbeats 0`, then the same on the reduced design): the first action of gate 1. I stopped at
   gate 0 as instructed and did not do it while the suite was running.
4. **Gate 4b status** (asked in the brief): `wpb2g4b`/`wpb2g4c` tip `87f0e2b4` (2026-11-01 23:12) is committed and NOT in
   `svgolf-prep`. It does not matter for D2; it would matter for a design with `x << i` and would still not cover the
   `>> 2**j` shifter of D1.
5. **The time limit** is a decision for the maintainers if the site count cannot be brought down: 35 minutes (reduced D2) or
   110 minutes (D2 as written) against 130 s for fdiv16, or a tactic fix first (G5').

## 8. Files (`svgolf/design/fdiv-param/h3/`)

| file | what |
|---|---|
| `fdivp.sv`, `fdivp2.sv` | D1 and D2 |
| `fdivp_model.py` | the bit-accurate model, `oracle_int`, `oracle_frac` (the repository's `spec/validate/oracle.py`) |
| `oracle.h`, `oracle_dump.cpp`, `cmp_oracle_cpp.py` | the 128-bit C++ oracle (`P <= ~40`) and its cross-check against the Python oracles |
| `tb_fdivp.cpp`, `run_v.py` | Verilator testbench and driver: exhaustive (`K <= 14`, and the 2^32 formats) or sampled |
| `gen_vec.py`, `tb_vec.cpp`, `run_vec.py`, `vec_batch.sh`, `vec_batch2.sh` (D2), `vec_batch3.sh`, `exh_more.sh` | corner-rich vector generation and the sampled runs at large formats |
| `val_py.py` | multiprocess exhaustive check of the model against both oracles |
| `probes/p*.sv`, `probes.lean`, `probes2b.lean`, `probes_run.sh` | the construct probes of section 4.1 (Lean files carry the scratchpad's absolute `load_sv` paths) |
| `d2_probe.lean`, `d2_struct.lean`, `d2_eq.lean` | the D2 tactic probes: `sv_structure?`, `sv_structure` with a rank, `sv_equations?` |
| `chain/*.sv`, `gen_chain.py`, `scal/*.lean`, `scal/log.txt`, `scal_run.sh`, `chainA.lean`, `chainA2.lean`, `chainB.lean` | the synthetic site-count scaling probes of section 4.3 (`scal/log.txt` is the wall-clock log quoted there) |
| `p27_meas.lean`, `p18_meas.lean`, `p18_run.sh`, `probes2b.lean` | the divider-family tactic measurements and the constant-operand probes |
| `results/` | exhaustive and sampled results, the oracle-chain checks, the score table |

# WP-H3, gate 1 (part 1): the math layer is PROVED for every format, and the word-level design D3

Status: NOTE, 2026-11-02, branch `wph3` (merged with `svgolf-prep` `cc61ae95`). Continues `H3-NOTE.md` (gate 0). Labels as there:
MEASURED (I ran it, the file is named), READ, MODEL, PLANNED, ESTIMATE. Timings of Lean runs were taken at load averages
of 35 to 150 and are NOT claims about a quiet machine (the lead's ruling: no time limit before a quiet measurement).

## 0. Summary

1. **The math layer of the parametric divider is a theorem, for ALL formats at once** (`tasks/fdivp/DpU.lean`):

       theorem OutN_fdivBits (W P : Nat) (h : 2 <= W /\ 2 <= P) (a b : BitVec (W + P)) :
           OutN <W, P> a.toNat b.toNat = (SvGolf.Tasks.FdivP.fdivBits W P a b).toNat

   `OutN` is the value of the output `q` of the word-level design D3 (below), signal by signal as a `Nat` model, and
   `fdivBits W P` is the task's own function (`divide <W, P> .roundTiesToEven`, the trusted spec). `#print axioms`:
   `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`, no `bv_decide`, no Mathlib. The
   binary16 instance is checked by an `example` against `fdiv16`. Compiles (MEASURED, module by module and as one file) in
   under a minute of Lean time in total.
2. **It is 1,483 new lines**, against my gate-0 estimate of 3,260 (planning 4,300): the parametric formulation reuses the
   format-generic half of the fdiv16 proof AS IS (`DpRound`'s `scale_*`, `low_*`, `up_*`, `SpecFacts.restore_spec`) and
   the certificate `CertF` of WP-H1 (691 lines, already for every format), and the three enumerating proofs became short
   inductions (`normIter_spec`, `core_t`/`core_f` for EVERY shift, no clamp).
3. **D3**, a word-level / family reference (`h3/d3/fdivp3.sv`, 34 sites against 90 for D2): validated exhaustively on all
   66 formats with `W + P <= 14` (3.82 x 10^9 pairs), on every pair of `(5,11)` and `(8,8)` (2 x 2^32), and on 12 larger
   formats up to `(11,53)` and `(2,62)` with 200,000 corner-rich vectors each: **0 mismatches**. Score at `(5,11)`:
   2166.076 GE, depth 289 (D2: 2314.058 / 295; D1: 1911.446 / 300; flat fdiv16: 1929.778 / 299).
4. **The tactics read D3 whole**: `sv_structure?` accepts it (26 plain sites + families `norm` 4, `div` 3, `lo` 1) in
   22 s of load and print their rank relations; `sv_equations?` at the DEFAULT heartbeats stops with a `simp` timeout (as on
   every parametric design). The first quiet measurement of D3's two tactics is still the action that waits for the lead's
   all-clear (the interpolated estimate from the chain data of gate 0 is in section 3).
5. **Next (design layer)**: the glue from the 34 sites' equations to this model (family lemmas for `norm`, `div`, `lo`),
   the solution file, and the heartbeat bracket; plan and size in section 4.

## 1. The math layer: files, statement, architecture

All in `svgolf/tasks/fdivp/`, registered in `tasks.lean`:

| file | lines | content |
|---|---|---|
| `FormatFacts.lean`, `CertF.lean` (WP-H1, copied unchanged from `design/fdiv-param/`) | 56, 691 | the rounding certificate for every format: `certF`, `certF_bridge`, `fdivF_cert`, field lemmas |
| `Spec.lean` (= `design/fdiv-param/SpecLocal.lean`) | 114 | the trusted statement (Option C: a family of fixed-size `CombTask`s), `fdivBits`, `statement_fdiv16` |
| `DpN.lean` | 176 | `normIter_spec` (the linear one-bit normalizer, by induction), `ydec_eq`, `core_t`, `core_f` (the guard/round/sticky decision is round-to-nearest-even of `qm / 2^(sh+1)` for EVERY shift `sh`), `mul2_*` helpers |
| `DpM.lean` | 440 | `scale_id'` (the exponent identity), `fields_gridF`, `cert_fin_grid`, `cert_inf_grid` (the fdiv16 lemmas with the binary16 numerals replaced by format constants, stated against `certNF`), `fin_cert_abs` (the finite, not overflowing case), `ovf_cert_abs` |
| `DpQ.lean` | 319 | THE MODEL (`eF`, `fF`, `sF`, `xeN`, `sigN`, `ZN`, `nyN`, `naN`, `yaN`, `qqN`, `rrN`, `adjN`, `qmN`, `st0N`, `EN`, `nrmE`, `ovfE`, `dshE`, `qsN`, `incN`, `efN`, `magN`, `nanN`, `infN`, `zeroN`, `cNanN`, `cInfN`, `cZeroN`, `ovfN`, `finN`, `OutN`), `mod3`, `bit_top`, `ovf_bits`, `Z_big`, `exp_facts`, `nrm_ovf_dsh`, `qm_st0`, `quot_abs` |
| `DpR.lean` | 140 | bridges (`BitVec` fields to `Nat`), `fin_op`, `sig_facts`, `xe_facts`, `norm_facts`, `mag_norm`, `mag_sub` |
| `DpS.lean` | 222 | `fin_cert_model`: for finite nonzero operands the datapath's result is accepted by `certF` (`infinity` on `ovf`) |
| `DpT.lean` | 154 | `frac_split`, `OutN_eq`: `OutN f a b = (divide f .roundTiesToEven a b).toNat` in every case of the special-value table |
| `DpU.lean` | 32 | `OutN_fdivBits` (the statement above) and the binary16 instance |

**Architecture.** The model follows the netlist, one `Nat` function per signal, with the exact modular arithmetic of
the circuit (`% 2^EW` registers, `E = ((ya + (Z - yb)) % Z + emax) % Z + (Z - adj)) % Z`). The proof of
`fin_cert_model` is: (1) a finite nonzero operand normalizes (`normIter_spec`: `na = sig * 2^la`, `na in [2^t, 2^p)`, the
register is `xe - la` modulo `Z`); (2) `restore_spec` at `n = p + 1` gives `qq`, `rr`, then `quot_abs`: `qm = M0 / nb`,
`M0 = 2^(p+adj) * na`, `qm in [2^p, 2^(p+1))`, `st0 <-> M0 mod nb != 0`; (3) `exp_facts` decodes the modular `E` as the true
exponent `Ei` (three applications of `mod3`, then `omega`: `E = Ei` or `Ei + Z`), `nrm_ovf_dsh` turns the sign/zero/overflow
tests of the netlist into `1 <= Ei`, `2^w - 1 <= Ei`, `dsh = 1 - Ei`; (4) the packed magnitude is `(Ep - 1) * 2^t + z` in the
normal regime and `z` in the subnormal one (`mag_norm`, `mag_sub`), with `z = qs/2 + inc`; (5) `fin_cert_abs`: `z` is a grid
point `z * 2^j`, `core_t`/`core_f` say it is the nearest-even rounding, the three field shapes (subnormal, normal, carry)
and the carry-into-infinity case are handled once, `cert_fin_grid`/`cert_inf_grid` close the certificate. No clamp of the
shift (the fdiv16 proof had a clamp at 12 and a flush region): `qs = qm / 2^dsh` for any `dsh`, `qs = 0` for `dsh >= p + 1`
is just arithmetic.

**What the design layer will use**: `OutN_fdivBits` and the model definitions as the targets of the equations of
`sv_equations` (section 4).

## 2. D3, the word-level design

`h3/d3/fdivp3.sv` (module `fdiv #(W, P)`, ports `a`, `b`, `q`, same as D1/D2), **34 sites**: unpack and classify 6
(`s`, `ea_nz`, `eb_nz`, `c_nan`, `c_inf`, `c_zero`, the last three written as ONE expression over reductions of windows),
normalizer 4 row-0 sites + family `norm` (4 sites: two significand rows and two exponent registers over `P - 1` stages),
division 2 + family `div` (3 sites: `qq[P+1-k] = (rr[k] >= nbx)`, `dd[k] = rr[k] - nbx`, `rr[k+1] = qq[..] ? dd[k] << 1 :
rr[k] << 1`), quotient 2 (`adj`, `qm`), exponent 5 (`onesW`, `emw = onesW >> 1`, `E`, `ovf`, `dsh`), round 4 (`qs`, `inc`,
`ef`, `mag`), output 3 + family `lo` (1 site: the low fraction bits). What changed against D2, and why each change is
the size of the result:

* **no constants by window writes** (D2's `kv`, `nrmth`, `ovfth`, the three special words: 11 sites): `emax` is
  `onesW >> 1` (one all-ones site and a constant shift), the thresholds `E >= 1` and `E >= 2^W - 1` are read off `E` in
  two's complement (sign bit, a reduction of the rest), the result fields are chosen by case with scalar conditions;
* **no denormalizer chain**: `qs = qm >> dsh` with `dsh = 1 - E` (a run-time shift by an `EW`-bit amount, gate 3a) and the
  sticky bit `(qs << dsh) != qm`: three sites instead of the `P + 1`-stage family of four;
* **the classification and unpack sites are folded**: reductions inside bitwise expressions and as `?:` conditions
  are accepted (probes `q01`, `q13`, `q14`, `q18`), so `a_nan ... b_zero` are not signals.

**Fragment probes for D3** (MEASURED, `h3/d3/probes3/q*.sv`, `h3/d3/probes3.lean`, one Lean run of 129 s under load):
ACCEPTED: a reduction inside a bitwise expression (`q01`), a comparison inside a bitwise expression (`q02`), a shift by
a wide amount compared with a vector (`q03`), `1 - e` with a constant left operand (`q04`), a constant `0` arm of `?:`
(`q06`), a run-time shift by an `EW`-bit vector (`q07`), `~e + 2` (`q08`), a comparison written into one BIT of a
vector (`q10`), an inline concatenation plus a one-bit signal (`q11`), the normalizer family with the `?:` condition a
bit select of another row (`q12`), a reduction as a `?:` condition (`q13`), `~e[EW-1] & (|e)` (`q14`), a one-bit signal as an
arithmetic operand (`q15`), a reduction of a row inline (`q16`), the low-bits family (`q17`), `ovf` inline (`q18`),
`ya - yb + em - adj` (`q19`), a concatenation as a comparison operand (`q20`). REFUSED: `'1`/`'0` fills inside an
expression (`q05`, `q21`: "unbased unsized literal inside an expression ... allowed as a whole right-hand side": written
as an all-ones SIGNAL `onesW` and a constant `0` arm instead), a reduction as a concatenation part (`q09`: "not inside a
concatenation part": `ea_nz` is a signal).

**An SV trap that Verilator found, recorded**: `E = ya - yb + emw - ~qq[P+1]` is WRONG: the unary `~` is
context-determined, so the 1-bit operand is zero-extended to `EW` bits BEFORE it is complemented. `adj` is a one-bit
signal (`assign adj = ~qq[P+1]`, then `- adj`). The first inlined version of D3 mismatched on 92 of 256 pairs at `(2,2)`.

**Validation** (MEASURED, `h3/d3/`, results in `h3/results/`): the Python model `model3` (`h3/fdivp_model.py`) equals the exact
integer oracle on every pair of every format with `K <= 10` (`h3/d3/val3.py`); Verilator on the SV: all 66 formats with `W + P <= 14`
(`exh_D3_K4-14.txt`: 3,817,748,736 pairs, 0 mismatches), `(5,11)` and `(8,8)` every one of the 2^32 pairs
(`exh_D3_2e32.txt`), 200,000 vectors at `(8,24)`, `(11,53)`, `(2,30)`, `(6,30)`, `(15,48)`, `(2,62)`, `(3,60)`, `(12,20)`,
`(20,12)`, `(16,16)`, `(4,20)`, `(10,40)` (`vec_D3.txt`), with the model equal to the oracle on the same vectors.

**Scores** (`score/score.py`, GE / depth / gates; flat fdiv16 reference 1929.778 / 299):

| design | (2,2) | (5,11) | (8,8) | (8,24) |
|---|---|---|---|---|
| D1 (natural, outside the fragment) | 93.322 / 20 | 1911.446 / 300 | 1251.195 / 181 | 7450.536 / 1256 |
| D2 (affine, 90 sites) | 96.32 / 18 | 2314.058 / 295 | 1498.496 / 179 | 9813.601 / 1279 |
| **D3 (word-level, 34 sites)** | 102.985 / 18 | **2166.076 / 289** (1515 gates) | 1369.84 / 184 | 8826.016 / 1261 (6062 gates) |

D3 is 6.4 % smaller than D2 at `(5,11)` and 10.1 % at `(8,24)`, and 1 to 6 levels shallower; the 12 % over the flat
reference at `(5,11)` is the linear normalizer's price (D1's logarithmic normalizer is outside the fragment).

## 3. What the tactics say about D3 (acceptance MEASURED, cost NOT yet)

* `sv_structure?` on the whole of D3: ACCEPTED (`h3/d3/d3_probe.out`): 26 plain sites, families `norm` (4), `div` (3), `lo` (1);
  a rank relation of about 170 lines for a certificate to satisfy (the writer of a window ranks below its readers; for the
  families, the rows' recurrences `rr[k+1]` after `rr[k]`, `na_r[i+1]` after `na_r[i]`). The 22 s of that run are the load
  and the elaboration of the design, not a tactic cost.
* `sv_equations?` at the default 200,000 heartbeats: `simp` timeout (as on D2 and on every parametric design); the run with
  `maxHeartbeats 20000000` is `h3/d3/d3_eq.lean` (informational, under load).
* **Estimate** (INTERPOLATION of the gate-0 chain data, not a measurement of D3): the chains cost 18 s, 49 s, more than 170 s of
  `sv_structure` for 11, 21, 41 plain sites (about `0.1 n^2` seconds under load 140); for `n = 34` that is about 115 s,
  against about 800 s for D2's 90 sites: a factor of 7. If the tactic fix of WP-LIN lands, the site count matters
  less; if it does not, D3 is already inside a tolerable range. The quiet measurement decides.

## 4. The design layer (next), plan and size

PLANNED, gate 1 part 2, after the all-clear: (1) `sv_equations` on D3 at a raised heartbeat bracket and the printed equations
(the shape table of H2-NOTE section 2 for D3's 34 sites); (2) `tasks/fdivp/DpGlue.lean`: reuse of the shape lemmas of
`tasks/fdiv16/DpGlue.lean` (`g_mux`, `g_sub`, `g_shl*`, `g_shr1`, `g_ge`, `g_cat`, `g_extract*`, `g_bit`: AS IS) plus the
family lemmas: the row recurrences `na_r`, `nb_r`, `ya_r`, `yb_r` (by induction on the stage against `normIter`, whose
`normStep` IS the circuit's stage), `rr`/`dd`/`qq` against `restRem`/`restQuo` (the `Nat` recurrence of `SpecFacts`), the low bits
`lo` (a bit-for-bit family), and the three run-time shift sites (`qs`, `inc`'s `(qs << dsh) != qm`, `dsh = 1 - E`) against
`Nat` division and `% 2^dsh`; about 12 lemmas, ESTIMATE 600 lines; (3) the solution file `tasks/fdivp/reference/fdivp.lean`
(structure with the rank, interface, `sv_equations`, the 34 `have b_<signal>` steps, `OutN_fdivBits`) and its `rmN` closers
(`all_goals (intros; sv_rowmajor; omega)`, measured at gate 0 on the divider family); ESTIMATE 400 lines; (4) the time
limit from a quiet measurement of the real chain on the final design (not before).

Pitfalls met in this part, for whoever continues (all cost one compile each): `lake env lean` resets `LEAN_PATH`, so an
overlay of oleans needs the toolchain's `lean` called directly with `--root`; an overlay directory named `tasks` shadows the
shared tree's `tasks` oleans (symlink `tasks/fdiv16` into it); `rw` closes a goal by `rfl` and a trailing `omega` then errors
("no goals"); `ac_rfl` does not evaluate `2 * 2` (a one-line lemma `mul_sq`); `conv_lhs` and `set` are Mathlib; `unfold a b c at h` fails
when one name does not occur in `h`; a `~` of a one-bit signal inside an `EW`-bit sum is complemented after extension (SV); the
module chain was debugged on ONE concatenated file (`lc/mkall.py` style: one run lists every error).

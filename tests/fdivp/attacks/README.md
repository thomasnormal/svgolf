# `tests/fdivp/attacks/`: correct-looking dividers that are wrong on some format

Each file without a `newton_` or `srt_` prefix is the reference D3 (`tasks/fdivp/reference/fdivp.sv`) with ONE change (the last
three of the table are the attacks of the former 16-bit task (binary16, now `(5, 11)` here) that have a parametric counterpart, ported 2026-11-03);
the `newton_` and `srt_` files are the attacks of the second and third references (below). Each passes every check up to the proof
(source gate, extraction at the probe points, banlist, `fourstate`, the `design` stage, scoring, the post-synthesis check
alone) and must FAIL the reference's proof at the `solution` stage (`tests/expected.json`, `lean: "reference"`): the proof
of `reference/fdivp.lean` applies `SvGolf.FdivParam.Glue.chain` to the 34 equations of the netlist, and a changed equation
no longer matches its hypothesis. The simulation records are in `tests/fdivp/results/attacks.txt`.

| design | the change | wrong on |
|---|---|---|
| `inc_tie_odd.sv` | `inc = qs[0] & (sticky \| ~qs[1])`: exact ties round to the ODD neighbour | every format; ties only (subnormal range): 8 of 256 pairs at `(2, 2)`, 1816 of 2^20 at `(4, 6)` |
| `dsh_wrap64.sv` | the denormalizing shift amount `dsh` is taken modulo 64 | `W >= 7` only: 104 of 2^20 pairs at `(7, 3)`, 2056 at `(8, 2)`; **right on all 2^32 pairs of `(5, 11)`**, wrong on 22,113 of 500,000 sampled at `(8, 24)` |
| `ew_narrow.sv` | the exponent register is `W + 2` bits instead of `W + P + 1` | `P` large against `W`: 1792 of 2^20 pairs at `(2, 8)`; **right on all 2^32 pairs of `(5, 11)`** and on 500,000 sampled at `(8, 24)`, `(11, 53)` |
| `zero_by_zero_inf.sv` | the `0 / 0` clause of `c_nan` is missing: `±0 / ±0` gives `±inf` | exactly 4 pairs of every format |
| `rr_sticky_dropped.sv` | the division's sticky bit ignores the last remainder (`\|rr[P+2]`) | a large share of the pairs of every format (138,736 of 2^20 at `(4, 6)`) |
| `ftz.sv` | flush to zero: a result with `E <= 0` (subnormal before rounding) is `±0` (ported from the former 16-bit task's `ftz.sv`) | every format: 32 of 256 pairs at `(2, 2)`, 145,924 of 2^20 at `(4, 6)` |
| `ovf_late.sv` | the overflow test one too late, `E >= 2^W` instead of `2^W - 1`: the all-ones exponent keeps its fraction (ported from the former 16-bit task's `ovf_late.sv`) | every format: 4 of 256 pairs at `(2, 2)`, 25,668 of 2^20 at `(4, 6)` |
| `dsh_sticky_short.sv` | the denormalizer's sticky test is two bits short, `(qs << dsh) != {qm[P:2], 2'b00}` (the parametric form of the former 16-bit task's `sticky_short.sv`) | subnormal results: right at `(2, 2)`, 32 of 2^14 pairs at `(3, 4)`, 384 of 2^20 at `(4, 6)`, 128 at `(2, 8)`, 504 at `(8, 2)` |

## The attacks of the Newton reference (`newton_*.sv`)

Each `newton_*.sv` is the Newton reference (`tasks/fdivp/reference/fdivp_newton.sv`) with ONE change in its core: the
seven deliberate mutants of the design's validation (2026-11-03), applied to the committed file. Each is submitted with
the Newton proof (`tests/expected.json`, `lean: "reference/fdivp_newton.lean"`) and must FAIL it at the `solution`
stage. Exhaustive Verilator counts (`validate/run_v.py`, 2026-11-04; the records are in
`tests/fdivp/results/attacks.txt`):

| design | the change | wrong on |
|---|---|---|
| `newton_f_minus2.sv` | the working precision `F = P + 2` instead of `P + 4` | every format: 48 of 256 pairs at `(2, 2)`, 670,984 of 2^20 at `(4, 6)` |
| `newton_ge1_const.sv` | the correction always adds 1 (`qq = qe + 1 + ge2`) | every format: 8 of 256 at `(2, 2)`, 150,424 of 2^20 at `(4, 6)` |
| `newton_ni_minus1.sv` | one Newton step fewer (`NI = $clog2((P + 9) / 8)`: none for `P <= 6`) | from `P = 3` on: right at `(2, 2)` and `(8, 2)`, 4756 of 2^14 at `(3, 4)`, 576,772 of 2^20 at `(4, 6)` |
| `newton_no_ge2.sv` | the correction stops at `qf + 1` (`ge2` dropped) | rarely, where the estimate is 2 below the quotient: over `W = 2`, `P = 2..12` only at `P = 6` (28 of 2^16 pairs); 196 of 2^20 at `(4, 6)`; **right on all 2^32 pairs of `(5, 11)`** |
| `newton_r0_off.sv` | the initial reciprocal's constant 47/32 instead of 45/32 | some `P`: over `W = 2`, `P = 2..12` at `P = 6`, 11 and 12; 77,636 of 2^20 at `(4, 6)` |
| `newton_rnz_no2mb.sv` | the sticky bit forgets the remainder `2·mb` (an exact quotient `qf + 2` taken for inexact) | rarely: over `W = 2`, `P = 2..12` only at `P = 6` (20 of 2^16); 140 of 2^20 at `(4, 6)`; **right on all 2^32 pairs of `(5, 11)`** |
| `newton_rnz_nomb.sv` | the sticky bit forgets the remainder `mb` (an exact quotient `qf + 1` taken for inexact) | every format, exact quotients only: 4 of 256 at `(2, 2)`, 892 of 2^20 at `(4, 6)` |

How the Newton proof fails on them (`message_contains` in `tests/expected.json`): five at the application of its
`Glue.chain`, where the changed site's printed equation no longer matches its hypothesis (`eq_r_plain_13` for
`newton_f_minus2`, `eq_qq_plain_21` for `newton_ge1_const` and `newton_no_ge2`, `eq_rnz_plain_22` for the two sticky
attacks); `newton_ni_minus1` at the same application but by the heartbeat limit of `solution` (the equation of `qp` reads
`r[NI]` with the step count `clog2((P + 9) / 8) + 0`, and unifying it with the chain's `+ 1` makes Lean reduce `clog2` at a
symbolic `P`); `newton_r0_off` at the value check of the constant of `r[0]` (`decide`: 47 is not 45).

`newton_no_ge2` and `newton_rnz_no2mb` are the strongest of them: they are wrong only where the estimate is two below the
quotient, which the Newton error bound allows but which is rare, so they are right at every small format except `P = 6`
and right at the scoring point. Only a proof for every `P` sees them.

## The attacks of the SRT reference (`srt_*.sv`)

Each `srt_*.sv` is the SRT reference (`tasks/fdivp/reference/fdivp_srt.sv`) with ONE change in its core: the ten
deliberate mutants of the design's validation (`tests/fdivp/results/srt_mutants.txt`, S0, re-derived on the committed
text), applied to the committed file. Each is submitted with the SRT proof (`tests/expected.json`,
`lean: "reference/fdivp_srt.lean"`) and must FAIL it at the `solution` stage. Exhaustive Verilator counts (2026-11-05;
every pair at `W = 2`, `P = 2..12` in `srt_mutants.txt`, nine small formats in `tests/fdivp/results/attacks.txt`):

| design | the change | wrong on |
|---|---|---|
| `srt_qds_t2_d0.sv` | selection constant `t2` at `da = 0`: 75 instead of 76 | from `P = 5` on: right at `(2, 2)`, `(3, 4)`, `(7, 3)`, `(8, 2)`; 20 of 2^14 at `(2, 5)`, 612 of 2^20 at `(4, 6)` |
| `srt_qds_t1_d0.sv` | selection constant `t1` at `da = 0`: 66 instead of 68 | from `P = 5` on: 24 of 2^14 at `(2, 5)`, 2716 of 2^20 at `(4, 6)` |
| `srt_qds_tm_d7.sv` | selection constant `tm` at `da = 7`: 38 instead of 41 | from `P = 5` on: 20 of 2^14 at `(2, 5)`, 1356 of 2^20 at `(4, 6)` |
| `srt_no_corr.sv` | no final correction (`qq = u[N]`) | from `P = 3` on: 28 of 2^10 at `(2, 3)`, 126,504 of 2^20 at `(4, 6)` |
| `srt_drop_carry.sv` | one carry of the carry-save row dropped (`cy[k][3]`) | every format: 20 of 256 at `(2, 2)`, 81,264 of 2^20 at `(4, 6)` |
| `srt_no_cin.sv` | the `+1` of the negated multiple `-q·dv` (`q > 0`) dropped | every format: 72 of 256 at `(2, 2)`, 562,084 of 2^20 at `(4, 6)` |
| `srt_sticky_sign.sv` | the sticky bit reads the residual's sign (`rnz = ~sign & (rs != 0)`) | from `P = 3` on: 32 of 2^10 at `(2, 3)`, 74,036 of 2^20 at `(4, 6)` |
| `srt_stages_m1.sv` | one stage fewer (`N = H`) | every format: 84 of 256 at `(2, 2)`, 792,708 of 2^20 at `(4, 6)` |
| `srt_otfc_um.sv` | on-the-fly conversion: `UM'` for `q = 0` taken from `U` (`g0` for `g1`) | from `P = 3` on: 40 of 2^10 at `(2, 3)`, 227,588 of 2^20 at `(4, 6)` |
| `srt_otfc_digit.sv` | on-the-fly conversion: the pair appended to `U` for `q = -1` is `10`, not `11` | every format: 20 of 256 at `(2, 2)`, 227,804 of 2^20 at `(4, 6)` |

How the SRT proof fails on them (`message_contains` in `tests/expected.json`; `check.py --no-score`, 2026-11-05, each
`solution` stage 63 to 67 s): all ten at the application of its `Glue.chain`, at the argument that is the printed
equation of the changed site: `eq_t2_plain_20`, `eq_t1_plain_21` and `eq_tm_plain_23` for the three table constants
(the chain takes the constants as the vectors the equations print and `core` checks their values by `decide`),
`eq_qq_plain_29` for `srt_no_corr`, `eq_wc_srt_10` for the two carry-save attacks, `eq_rnz_plain_30` for
`srt_sticky_sign`, `eq_rs_plain_28` for `srt_stages_m1` (the residual reads the family at `N = H`, where the chain has
`H + 1`), `eq_ums_srt_16` and `eq_uq0_srt_12` for the two conversion attacks. The phrase pinned is the error's TAIL,
`` <argument>\n'Submission.solution' depends on axioms``: Lean prints the application up to the bad argument, and the
axioms that follow carry `sorryAx`. The head (`Application type mismatch: The argument …`) is not pinned: with the full
type of a table or of the carry vector in the message it falls outside the last 4000 characters `check.py` keeps of a
compile error.

The three table attacks are the every-`P` test of this reference: right at every format with `P < 5`, because a stage
reaches the bad cell of the table only from `P = 5`; the exact check of all the table's cells in the proof (`srt_tbl`)
is what rules them out for every `P`.

The two format-dependent attacks are the point of a task that is "for ALL formats": a check at the scoring point alone
(the post-synthesis check, the advisory oracle) cannot see them, only the proof can. What the sampling checks say, on the
4443 vectors of the full post-synthesis mode at `(5, 11)`: the post-synthesis check passes all five (it compares ls-sv with
the design's own netlist, not with the function), and the advisory oracle flags `inc_tie_odd` (4 vectors),
`zero_by_zero_inf` (4) and `rr_sticky_dropped` (590) but not `dsh_wrap64` and `ew_narrow`.

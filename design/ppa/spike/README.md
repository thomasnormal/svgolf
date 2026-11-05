# The PPA spike: weighted delay, toggle energy, AT/EDP on the existing designs

Measured 10/30 on the 5 `add` and 7 `mul` designs of the repository (the `add` reference, the Sklansky,
Kogge-Stone and comparison-carry baselines, Yosys' own `+`; the four proved `mul` references, the two Dadda
baselines, Yosys' own `*`), at the scoring point N = 16 and, for sensitivity, N = 8, 32 and 64 (adders only at 64;
`dadda_ks_32` exceeds `score.py`'s 1800 s limit). Nothing in the repository outside `design/ppa/` was touched. The
whole sweep reruns in about six minutes:

```
cd svgolf/design/ppa/spike
./run_all.sh                 # fetch liberty (6.7 MB, sha256-pinned), score, measure, remap, FPGA counts, tables
./determinism_check.sh       # results bit-identical under different PYTHONHASHSEEDs; netlist byte-identical
python3.12 derive_ge.py      # score/ge.json against the library's cell areas
python3.12 report.py --n 16  # prints the tables below (also data/report_N16.md)
```

Needs: `python3.12` with `pyslang` (the source gate of `score/score.py`), Yosys 0.53 on `PATH` (or `$SVGOLF_YOSYS`),
network once for `fetch_lib.py` (or `PPA_NANGATE45_LIB=/path/to/NangateOpenCellLibrary_typical.lib`). Everything else
is the standard library. No Verilator, no Lean.

## Files

| file | what |
|---|---|
| `designs.py`, `gen_netlists.py` | the design list; runs the **pinned** `score/score.py` on each and keeps its scored netlist (`data/netlists/<name>_N<n>.v`) and score JSON |
| `fetch_lib.py` | the Nangate45 typical liberty at ORFS commit `6c6fc7e2`, sha256 `8d540a4d4cf6d09d27c87ad067857a9c0c2eeb023ab7a56e058cd3113db4e9b1` |
| `liberty.py` | Liberty reader (groups, NLDM tables with bilinear interpolation, arcs, internal power, boolean `function` compiler); 0.33 s for the 6.7 MB file |
| `netlist.py` | reader for the structural Verilog `write_verilog -noattr -noexpr` produces (generic `$_X_` gates or liberty cells) |
| `engine.py` | gate graph over liberty cells; unit depth; **logical-effort delay**; **NLDM STA**; bit-parallel simulation; toggle counts; **inertial-delay event simulation** (glitches); area and leakage |
| `vectors.py` | the pinned stimulus: vector `k` = SHA-256 of `"svgolf-ppa-spike/<seed>/<k>"`, uniform over all input bits |
| `run_spike.py` | the measurement: one JSON per N (`data/results_N<n>.json`) |
| `flow_a.py` | Flow A1: `abc -liberty` re-mapping of the same canonical RTLIL (`&nf`, or sized with `-constr` and a delay-target sweep), then the same measurements |
| `mklib8.py` | cuts a 9-cell subset (136 kB) out of the pinned liberty |
| `fpga_yosys.py` | Yosys-only FPGA counts: `abc -lut 4/6` LUTs and levels, `synth_ice40`, `synth_xilinx -family xc7` |
| `derive_ge.py` | derives `score/ge.json` from the liberty and diffs it |
| `report.py` | tables, ranks, Kendall tau, Pareto sets, N sweep, mapper comparison |
| `data/report_N16.md` | the complete output of `report.py` (all tables) |
| `data/*.json`, `data/netlists/` | the measurements and the 40 scored netlists with their score JSONs that they were taken from (so `run_spike.py` reruns without Yosys); `data/flow_a/` (mapped netlists and logs, 12 MB) is regenerable and git-ignored; `.cache/` holds the fetched liberty |

## Models, exactly

* **Unit depth:** the score's `ltp` depth. The reader reproduces it on all 12 netlists (12 of 12 equal), which
  validates the netlist parser.
* **Logical effort (LE), unit-size gates, in tau:** `delay(gate) = p + C_load / C_inv`, `C_load` = sum of fan-out
  input capacitances in units of an inverter's + 4 per primary-output bit; no wire. Table (Sutherland, Sproull,
  Harris, *Logical Effort*; Harris' lecture catalogue): INV p 1, input cap 1; NAND2 p 2, cap 4/3; NOR2 p 2, cap 5/3;
  AND2 = NAND2 + INV, p 4, cap 4/3; OR2 = NOR2 + INV, p 4, cap 5/3; XOR2/XNOR2 p 4, cap 4 (g = 4); MUX2 p 4, data cap
  2, select cap 4 (g = 2). ANDNOT/ORNOT are expanded as INV + NOR2/NAND2 for every model.
* **NLDM:** Nangate45 typical, rise/fall arrival and slew per net, worst-slew merge, all conditional arcs, no wire,
  PI slew 10 ps, PO load 6.8 fF (4 x `INV_X1`), all cells the `_X1` size the netlist's gate kind maps to
  (`AND`->`AND2_X1`, `XOR`->`XOR2_X1`, `MUX`->`MUX2_X1`, `NOT`->`INV_X1`, ...). The effective tau of the LE table
  against NLDM is 3.8 to 5.0 ps per tau (FO4 = 5 tau = 19 to 25 ps: plausible for 45 nm).
* **Energy per operation:** 2001 vectors (2000 consecutive transitions); `E_sw = sum toggles * 1/2 C V^2` (C = fan-out
  pin caps, + 6.8 fF on outputs, primary inputs included, V = 1.1 V); `E_int` = liberty `internal_power`
  (mean of the cell's tables at worst input slew and load; the declared units of the library, V x mA x ns, would
  make them pJ, but they are read as fJ because that makes `E_int` 0.6 to 1.0 times `E_sw` (adders 0.6 to 0.9,
  multipliers 0.96), where a pJ reading would make it 1000 times larger than the switching energy, which is not
  physical for a NAND2; this is an assumption, flagged in `metrics.md`);
  `E_leak = sum cell leakage * T_crit`. **Zero-delay** = functional toggles; **glitch-aware** = event simulation
  of the first 1000 vector pairs with the STA's rise/fall gate delays and inertial filtering, asserted to settle
  to the zero-delay values on every pair.
* Derived: `AT = lib_GE * T`, `AT^2`, `EDP = E_op * T`, `ED^2P`, perf per energy = `1/E_op`; `E_op` in the combined
  figures is the glitch-aware dynamic energy + leakage.

## Validation of the instrument

| check | result |
|---|---|
| netlist reader and depth | `ltp` depth reproduced on 12 of 12 designs at N = 16 (and at the other N) |
| STA against an independent STA | on 72 `abc -liberty -constr` netlists (12 designs x 6 delay targets) ABC's own `stime -p` and the engine agree: mean 1.3%, max 5.5% |
| library-priced area against the score | `lib_GE / score_GE - 1` between 0.0% and +1.2% over the 12 designs; the difference is entirely `ANDNOT`/`ORNOT` (1.667 GE as INV + NOR2/NAND2 against 1.333) |
| `ge.json` | equals the Nangate45 `_X1` area ratios for 8 of 11 gate types; ANDNOT, ORNOT and BUF differ (`derive_ge.py`) |
| determinism | `determinism_check.sh`: byte-identical JSON under `PYTHONHASHSEED=1` and `2`; scored netlist byte-identical on re-synthesis (found and fixed: float sums over a `set` of net names were hash-seed dependent) |
| sampling noise | zero-delay `E_op` over three stimulus seeds: spread at most 0.5% (add), 1.0% (mul) at 2000 transitions; the glitch-aware ratio over 300 and 1000 pairs agrees within 1% |
| glitch simulation | the event simulator's settled values equal the zero-delay values on every pair of every design (assertion) |

## Results, N = 16 (full tables: `data/report_N16.md`)

`GE`, `depth`: the present score. `T_LE` in tau, `T` = NLDM in ns. `E0` = zero-delay dynamic energy, `Eg` =
glitch-aware, fJ per operation. `AT` = lib_GE x T; `EDP` = (Eg + leakage) x T, fJ.ns.

**add** (the `add` reference is the ripple adder; the others are baselines without a proof)

| design | GE | depth | T_LE | T (ns) | E0 | Eg | glitch x | AT | EDP |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (reference) | 112.0 | 33 | 178.7 | 0.676 | 199.6 | 233.9 | 1.17 | 75.7 | 159.0 |
| add_sklansky | 127.7 | 28 | 157.3 | 0.636 | 213.0 | 254.1 | 1.19 | 81.2 | 162.6 |
| add_kogge | 149.7 | 24 | 136.0 | 0.534 | 239.8 | 274.6 | 1.14 | 80.3 | 147.4 |
| add_cmpcarry | 196.0 | 17 | 95.0 | 0.434 | 273.1 | 327.5 | 1.19 | 85.9 | 143.0 |
| add_yosys (`+`, banned) | 118.0 | 33 | 194.7 | 0.760 | 203.3 | 246.4 | 1.21 | 89.7 | 188.6 |

**mul**

| design | GE | depth | T_LE | T (ns) | E0 | Eg | glitch x | AT | EDP |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| mul_array (reference) | 1962.6 | 88 | 593.0 | 2.981 | 2372 | 12416 | **5.23** | 5851 | **37321** |
| mul_tree (reference) | 2034.9 | 63 | 370.7 | 1.652 | 2428 | 4879 | 2.01 | 3363 | 8159 |
| mul_wallace (reference) | 2113.9 | 62 | 369.3 | 1.611 | 2475 | 4631 | 1.87 | 3411 | 7560 |
| mul_tree_h (reference) | 2025.9 | 62 | 361.3 | 1.616 | 2422 | 4861 | 2.00 | 3274 | 7949 |
| mul_dadda_rc (baseline) | 1953.6 | 61 | 352.0 | 1.446 | 2323 | 4059 | 1.75 | 2831 | 5942 |
| mul_dadda_ks (baseline) | 2076.5 | 48 | 286.0 | 1.326 | 2448 | 4532 | 1.85 | 2785 | 6077 |
| mul_yosys (`*`, banned) | 2081.2 | 59 | 366.0 | 1.642 | 2446 | 4639 | 1.90 | 3421 | 7716 |

Glitch factor of the array multiplier against N: 2.6 (N = 8), 5.2 (16), 11.2 (32); trees stay at 1.5 to 2.3.

## Does the ranking change? (the answer to "do the new metrics matter")

Ranks and Kendall tau are in `data/report_N16.md`; the findings, with the strength of each:

1. **Weighted delay mostly confirms unit depth.** Kendall tau(depth, NLDM delay) is +1.00 for the adders at N = 16
   (+0.80 at N = 32 and 64) and +0.70 for the multipliers (+1.00 at N = 8, +0.47 at N = 32); LE tracks depth even
   more closely (+0.80 to +1.00) and NLDM agrees with LE (+0.6 to +1.0). The flips are near-ties and, systematically,
   everything involving `ANDNOT`/`ORNOT`, whose hidden inverter the unit-depth `ltp` does not count (Yosys' `*`: 59
   levels become 61 gate levels; Yosys' `+` falls behind the ripple adder: 0.760 against 0.676 ns at the same depth
   33). **Kogge-Stone beats Sklansky on weighted delay at N = 16** (0.534 against 0.636 ns, as 24 against 28 levels)
   **and N = 64, and loses to it at N = 32** (1.066 against 0.964 ns; 47 against 43 levels): no change from the unit
   depth, whose non-monotone behaviour with N comes from the generator, not the metric.
2. **Delay per level is not constant, and that is what moves the product figures.** NLDM delay per unit level is
   20.5 ps for the ripple adder, 22 to 23 for the prefix adders, 25.6 for the comparison-carry adder, 26 for the
   tree multipliers and **33.9 for the array multiplier** (XOR-heavy full-adder chains). Consequences: the **AT
   leader among the adders flips**: area x unit depth ranks comparison-carry first (3332) and ripple last (3696)
   among the four legal adders; area x NLDM delay ranks ripple first (75.7) and comparison-carry fourth (85.9).
   The whole AT range is only 13% in NLDM, so this is a model-sensitive near-tie, not a finding to build on.
   Area x depth underprices the array multiplier's slowness: array against `mul_tree_h` is 1.37x in GE x depth, 1.79x
   in AT (NLDM), 2.6x in glitch-aware energy and **4.7x in EDP**.
3. **Zero-delay toggle energy is an area proxy.** Kendall tau against GE is +1.00 for the adders and +0.90 for the
   multipliers; the energy ranking carries almost nothing the area did not. The seven multipliers span 6.5% in
   zero-delay energy (2323 to 2475 fJ) with 1% sampling noise.
4. **Glitch-aware energy is a different quantity.** It correlates with depth (tau +0.70), not with area (tau -0.14),
   and the array multiplier jumps from 2nd lowest zero-delay energy to **last, 2.5x the tree multipliers (12.4 pJ
   against 4.6 to 4.9)**. The magnitude depends on the delay model (inertial filtering at one gate delay is
   conventional and, if anything, generous to glitches); the direction (long unbalanced ripple chains glitch,
   balanced trees less) is the textbook one. Publish zero-delay and glitch-aware side by side and decide which one
   ranks.
5. **Among the proved multiplier references the ordering by (area, depth) and by the new figures differs only
   where the numbers are within noise.** (area, depth): frontier {array, tree_h}; (area, T): {array, tree_h, wallace}
   (wallace is faster than tree_h by 0.3%); (area, T, glitch-aware energy): the same three; (energy, T): {wallace}
   alone. The question "does the Wallace tape lose to the heap tree on energy" has no stable answer: zero-delay
   energy 2475 against 2422 fJ (tree_h wins by 2.2%, about twice the sampling noise), glitch-aware 4631 against 4861
   (Wallace wins by 4.7%), EDP 7560 against 7949 (Wallace wins by 5%); and a different mapper (the 9-cell subset
   `&nf`) moves the delays by 5% to 12% (`tree_h` 1.633, `wallace` 1.797 ns). **Treat differences under about 10% as
   noise until the flow is pinned and a second mapper agrees.**
6. **The mapper matters as much as the metric.** The same canonical RTLIL mapped by `abc -g`, by `abc -liberty` on
   the full Nangate45 and on the 9-cell subset gives delay rankings of the seven multipliers with Kendall tau +0.90 /
   +0.43 / +0.52 between the three pairs (adders +0.8 to +1.0); the area ranking +0.90 / +0.62 / +0.52. Dadda
   + Kogge-Stone is the fastest multiplier in every mapping; the middle of the field reorders.
7. **FPGA counts rank the multipliers differently from GE.** LUT4 order: dadda_rc 624 < tree_h 636 < tree 637 <
   yosys 698 < dadda_ks 703 < wallace 705 < **array 716**; GE order has the array 2nd smallest. LUT4 levels: array 38,
   trees 22, Dadda + KS 17. The comparison-carry adder shows the carry loophole (48 LUT4 + 133 `SB_CARRY`).
   Generic `abc -lut` and `synth_ice40` agree within about 25%, `synth_xilinx` does not (array: 552 LUT6 generic, 890
   LUT + 339 MUXF target-specific).
8. **The Pareto picture of the existing designs is dominated by the Dadda baselines in every metric tried**
   (they have no proof, so they are not entries): the frontier of all seven multipliers is {dadda_rc, dadda_ks}
   under (GE, depth), (GE, T), (GE, T, Eg) and (Eg, T); adding zero-delay energy as a third axis lets Yosys' `*` in.
   The new metrics do not reorder the field; they price the trades inside it.

## Limits of this spike

No wire parasitics, so Kogge-Stone's long wires and Sklansky's fan-out wires are not charged (the physical flow D
is the only one that sees them). All gates are `_X1` in A0 (no sizing; A1 sizes). One library, one corner, one
supply. Uniform random inputs only. The glitch model is inertial delay with STA-derived fixed gate delays (no slew
effects, no pulse degradation); the internal-power tables are averaged over their conditions. N = 16 for most
statements (N = 8, 32, 64 for sensitivity: the flips above change with N). ABC's result depends on the netlist
structure it receives, which is the pinned flow's own residual (README, "Canonical layout"); every number here is a
function of that mapping. The STA was validated against ABC's `stime`, not against OpenSTA (not installed).

# svGolf PPA cost models: study and spike (WP-X0, 10/30)

> **Update, WP-X1 (10/30): the library is now `sky130_fd_sc_hd` (tt_025C_1v80), not Nangate45** (Nangate's licence restricts
> benchmarking the library; the maintainers chose SkyWater). [sky130.md](sky130.md) redoes the study on
> sky130 with measurements: the library facts and the GE table (NOT is 1.0 GE, ANDNOT/ORNOT are single 1.667 GE cells,
> flip-flops 5.33 / 6.67 GE), a cell policy and fixed timing setup, the pinned abstract-gate flow priced in sky130 cells (A0')
> against a real `abc -liberty` mapping (A1') on the add, mul and aes_sbox designs, a noise policy with measured tie bands,
> energy over several seeds, the post-synthesis simulation of sky130 netlists in Verilator, and a migration plan that is
> additive by default (legacy `area_ge_v1`/`depth_v1` unchanged, new versioned sky130 fields). Everything below this note is
> the WP-X0 Nangate45 study and stays as the legacy report; where the two disagree (library, GE table, recommended flow
> details), sky130.md governs.

Decided 10/30: no depth budget, no AND-count track; the scores that matter are the **PPA family**: performance
(real delay, fmax), power (dynamic energy, performance per watt), area, the combined figures **AT, EDP,
perf/W**, the **FPGA** equivalents (LUT, FF, BRAM, fmax) and the **physical-design** ones (wirelength, congestion,
parasitic-aware timing). Today svGolf scores area (NAND2 gate equivalents, pinned Yosys + ABC) and unit depth (`ltp`)
and keeps the (area, depth) Pareto frontier. This directory is the study of what to add, and a measured spike on
the existing `add` and `mul` designs.

| file | what |
|---|---|
| this file | answer first, tables, plan, decisions, risks |
| [tools.md](tools.md) | what is installed, what is missing, how to get each tool (macOS arm64 and Linux), sizes, times |
| [libraries.md](libraries.md) | Nangate45 / ASAP7 / Sky130 / GF180 / IHP, licences, sizes, the GE derivation |
| [metrics.md](metrics.md) | exact definitions, inputs, clocked vs combinational, gaming and defence, determinism |
| [flows.md](flows.md) | flows A to D, per-run time, pins, and the changes to `score/`, `check.py`, `postsynth`, the leaderboard, the README |
| [spike/](spike/README.md) | the measured spike: scripts (rerun in six minutes), data, tables, validation |

## 1. The answer in ten lines

1. **Nothing has to be installed to start.** Everything the first three stages need is Yosys 0.53 + ABC 1.01 +
   Python 3.12, which svGolf already requires, plus one 6.7 MB liberty file fetched at a pinned hash. OpenSTA,
   OpenROAD, nextpnr and ORFS are not installed here; **none has a macOS arm64 binary except `nextpnr-ice40`
   (Homebrew) and the 525 MB OSS CAD Suite** (which has nextpnr but no OpenSTA/OpenROAD); Docker's daemon is off and
   the ORFS image is amd64-only.
2. **`score/ge.json` is exactly the Nangate45 `_X1` area ratios** (NAND2_X1 = 0.798 um^2 = 1 GE; INV .667, AND/OR 1.333,
   XOR 2, MUX 2.333) for 8 of its 11 entries; only ANDNOT/ORNOT (no single cell: INV + NOR2/NAND2 = 1.667 GE against
   the table's 1.333) and BUF differ. So adopting Nangate45 makes the old area score and a library-priced area
   agree to 0.0% to +1.2% on the 12 designs measured.
3. **A 90-line Python NLDM static timing pass is a legitimate scorer.** Against ABC's own `stime` on 72 mapped
   netlists it agrees to 1.3% on average (5.5% worst); it runs in 0.02 s on the 1400-gate multiplier and is
   bit-identical across runs and hash seeds (measured).
4. **Weighted delay mostly confirms unit depth** (Kendall tau +0.8 to +1.0 for the adders, +0.5 to +1.0 for the
   multipliers over N = 8 to 64), and its flips are near-ties plus everything hidden behind `ANDNOT`/`ORNOT` inverters. Kogge-Stone
   still beats Sklansky at N = 16 (0.534 against 0.636 ns) and loses at N = 32 (as in unit depth).
5. **The new figures matter where delay per level differs:** the array multiplier costs 33.9 ps per level against
   about 26 for the trees. Against the proved heap tree `mul_tree_h` it is 1.37x in GE x depth, 1.79x in AT, 2.6x in
   glitch-aware energy, **4.7x in EDP**, while being 3% smaller. The area/depth frontier keeps it; every
   delay-aware combined figure buries it.
6. **Zero-delay toggle energy is an area proxy** (tau +0.90 to +1.00 against GE); **glitch-aware energy is a
   different quantity** (tau -0.14 against GE, +0.70 against depth; array multiplier glitching 2.6x, 5.2x, 11.2x
   at N = 8, 16, 32). Which one ranks is a decision; both are cheap.
7. **The mapper is as large an effect as the metric.** Three mappings of the same canonical RTLIL (`abc -g`, `abc
   -liberty` full, `abc -liberty` 9-cell) rank the seven multipliers' delays with tau +0.90, +0.43, +0.52; ties and
   differences under about 10% are noise, in every metric.
8. **FPGA counts rank the multipliers differently from GE** (array: 2nd smallest in GE, largest in LUT4s with
   38 levels against 22), and expose loopholes the ASIC flow lacks: comparison operators become carry chains
   (48 LUT4 + 133 carry cells for the comparison-carry adder), `*` becomes DSP blocks.
9. **Recommended:** make **flow A0** (the scored netlist weighted by a pinned Nangate45 liberty: delay, energy,
   AT/EDP/ED^2P, area in um^2) the official extension, in about 4 to 5 days; add Yosys-only FPGA counts as extra
   columns in 1 to 2; use OpenSTA, nextpnr and ORFS as **maintainer-side Linux CI cross-checks and extra
   columns**, not as contestant requirements.
10. **Decisions for the maintainers are in section 7**; the biggest are whether energy ranks by the zero-delay or the
    glitch-aware figure, whether FPGA/physical are extra columns (recommended) or contests, and whether to keep the
    ANDNOT/ORNOT pricing.

## 2. Tools (details: [tools.md](tools.md))

| present | missing |
|---|---|
| Yosys 0.53 (passes `sta`, `ltp`, `abc -liberty/-D/-constr`, `stat -liberty`, `synth_ice40/ecp5/xilinx`, `dfflibmap`, `read_liberty` all present), ABC 1.01, Verilator 5.042, Icarus 12.0, ngspice 47, python3.12 (pyslang, numpy, scipy, networkx), cmake, bison, flex, eigen, tcl-tk, boost, conda, Docker CLI (**daemon off**) | **OpenSTA** (GPL-3.0; source build, needs CUDD; no brew/conda package), **OpenROAD** (no macOS binary; Ubuntu `.deb`; Docker amd64 only; Bazel source build), **ORFS/LibreLane** (Nix or Docker), **nextpnr-ecp5** (no Homebrew formula; `nextpnr-ice40` 0.11.1 has one), **Nix** |

Measured on the installed Yosys: `sta` finds no timing arcs on `$_AND_`... cells ("No timing paths found"), so
the "pinned static timing pass" cannot be Yosys `sta`; `abc -D` only acts together with `-constr` (inert otherwise).

## 3. Library (details: [libraries.md](libraries.md))

**Nangate45 typical, fetched from OpenROAD-flow-scripts at commit `6c6fc7e2`, sha256 `8d540a4d...`** (6.7 MB, one
corner, 135 cell groups, has internal power and leakage, complete ORFS physical platform). Licence caveat: the ORFS
copy ships Apache-2.0, the file's own header still has Nangate's 2011 restriction notice: fetch, do not vendor.
ASAP7 (BSD-3, about 10 MB in 5 files) and Sky130hd (Apache-2.0, 12.8 MB) are later "technology" options; GF180 and IHP
are real-silicon but add nothing here.

## 4. Metric table (details: [metrics.md](metrics.md))

| metric | pinned definition (tool) | needs | deterministic? | main gaming surface -> defence |
|---|---|---|---|---|
| **delay `T`** (comb.) | longest PI to PO NLDM arrival, ps, rise/fall, slew propagation, PI slew 10 ps, PO load 6.8 fF, no wire (Python STA; OpenSTA as CI cross-check) | liberty, netlist | **yes, bit-identical** (measured) | structural false paths over-count (penalizes skip designs); unsupported cells/loops -> fail closed; sizing/`-D` knobs fixed by the flow |
| **fmax** (clocked) | `1/T_clk,min`, four path classes + clk-to-q + setup, ideal clock | + flop cells | yes | multi-cycle/false paths cannot be declared by the player |
| **dynamic energy `E_op`** | pinned SHA-256 stimulus, 2001 vectors, `sum toggles x 1/2 C V^2` + liberty internal energy; zero-delay and glitch-aware (event sim) variants (Python; OpenSTA `report_power` from SAIF as cross-check) | liberty, stimulus, workload | yes if toggles are integers (measured); sampling noise 0.5% to 1.0% at 2000 transitions | vector dependence -> salt from canonical text + secret, large K; workload statement per task; constant inputs impossible in comb.; model dependence of glitches -> publish both |
| **leakage** | `sum cell_leakage_power`, `E_leak = P_leak T` (0.7% to 4.4% of the zero-delay `E_op` here) | liberty | yes | none beyond area |
| **perf/W** | `1/E_op` for a comb. block (no delay content); with leakage `1/(E + P_leak T)`; clocked: `fmax x IPC / P` | | derived | never rank by it alone |
| **AT, AT^2, EDP, ED^2P** | `area x T`, `area x T^2`, `E x T`, `E x T^2` (ED^2P is voltage-invariant) | | derived | show components and the Pareto set; scalar is a view |
| **FPGA LUT/FF/BRAM/DSP/carry, levels** | pinned `synth_ice40`/`synth_ecp5`/`synth_xilinx`; `abc -lut K` + `ltp` for levels | Yosys, target | yes (Yosys) | carry chains, DSP, BRAM inference -> separate columns or ban; target-specific mappers differ (xc7 890 LUT + 339 MUXF vs 552 generic LUT6) |
| **FPGA fmax** | nextpnr `Max frequency`/`Max delay <async>`, fixed `--freq`, seed list, `--threads 1` | nextpnr, device | **unverified** (seeded) | seed picking -> median of fixed seeds; CI double-run |
| **wirelength, congestion, utilization, post-route timing/power** | ORFS: HPWL/routed wirelength, GRT overflow, core area, OpenSTA + SPEF | OpenROAD, platform, floorplan params | **unverified**; pin container digest, threads, seeds | floorplan knobs and pin placement fixed by the flow; report core area; maintainers only |

For clocked designs (T6) the changes are collected in [metrics.md](metrics.md) section 9: flops are cells (DFF_X1 = 5.667 GE),
`T_clk,min` replaces `T`, energy gains the clock pin and a pinned trace with idle cycles, throughput is `fmax/II`
(CPUs: CPI on a pinned program x `T_clk`).

## 5. Flows (details: [flows.md](flows.md))

| flow | adds over the previous | per-run time | new tools | official? |
|---|---|---|---|---|
| **A0** scored netlist + Nangate45 weights | delay in ps, area in um^2, `E_op` (zero-delay, glitch-aware), AT/EDP | 0.6 s zero-delay; +3 to 8 s glitch-aware, N = 16 multipliers (*measured*) | none | **yes** |
| **A1** `abc -liberty` remap (sized, delay-target sweep) | recognisable tape-out netlist, area/delay curve per design | 0.3 to 4 s per mapping (*measured*) | none | research column; `-D` inert without `-constr`; mapper changes ranks |
| **B** OpenSTA + simulation activity | second opinion on delay, standard power report | < 1 s (*estimate*) | OpenSTA (build) | CI cross-check on Linux |
| **C** `synth_ice40/ecp5` + nextpnr | LUT/FF/BRAM/DSP, LUT levels, routed fmax | Yosys ~ 1 min for the 12 designs (*measured*); PnR seconds to a minute (*estimate*) | nextpnr (brew ice40, or OSS CAD Suite) | extra columns (Yosys half now, nextpnr in CI) |
| **D** ORFS physical | wirelength, congestion, post-route timing/power | 1 to 2 min native, several x under emulation (*estimate*) | OpenROAD, Docker/Nix | maintainers' nightly extra columns |

Cross-cutting changes (all in [flows.md](flows.md)): `score/ppa.py` + `ppa_pins.json` + `derive_ge.py` test; `task.json`
`scoring.ppa` (stimulus, metrics; default off so old tasks are unchanged); the PPA pass reads **the very netlist file**
the postsynth stage simulates and the record stores its sha256, plus a Verilator-versus-scorer-evaluator self-test;
leaderboard record `/2` (integer `t_ps`, `e_*_aj`, `leak_pw`, `area_um2_m`, `liberty_sha256`, `ppa_script_sha256`,
stimulus), `pareto --objectives area,t,e` with three 2-D projections and presets (`smallest-area@t<=X`, `best-edp`,
`best-at`, `best-ed2p`, `best-perf-per-energy`); README "Scoring" paragraph.

## 6. The spike (details and all tables: [spike/README.md](spike/README.md), `spike/data/report_N16.md`)

Ranks at N = 16 (1 = best). Present score = GE and depth; new = NLDM delay, AT (lib GE x NLDM), glitch-aware energy,
EDP.

| mul design | GE | depth | T (ns) | AT | Eg (fJ) | EDP | GE rank | depth rank | T rank | AT rank | Eg rank | EDP rank |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| array (proved) | 1962.6 | 88 | 2.981 | 5851 | 12416 | 37321 | 2 | 7 | 7 | 7 | 7 | 7 |
| tree (proved) | 2034.9 | 63 | 1.652 | 3363 | 4879 | 8159 | 4 | 6 | 6 | 4 | 6 | 6 |
| wallace (proved) | 2113.9 | 62 | 1.611 | 3411 | 4631 | 7560 | 7 | 4 | 3 | 5 | 3 | 3 |
| tree_h (proved) | 2025.9 | 62 | 1.616 | 3274 | 4861 | 7949 | 3 | 4 | 4 | 3 | 5 | 5 |
| dadda_rc (baseline) | 1953.6 | 61 | 1.446 | 2831 | 4059 | 5942 | 1 | 3 | 2 | 2 | 1 | 1 |
| dadda_ks (baseline) | 2076.5 | 48 | 1.326 | 2785 | 4532 | 6077 | 5 | 1 | 1 | 1 | 2 | 2 |
| yosys `*` (banned) | 2081.2 | 59 | 1.642 | 3421 | 4639 | 7716 | 6 | 2 | 5 | 6 | 4 | 4 |

| add design | GE | depth | T (ns) | AT | Eg (fJ) | EDP | GE rank | depth rank | T rank | AT rank | Eg rank | EDP rank |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| ripple (proved) | 112.0 | 33 | 0.676 | 75.7 | 233.9 | 159.0 | 1 | 4 | 4 | 1 | 1 | 3 |
| sklansky | 127.7 | 28 | 0.636 | 81.2 | 254.1 | 162.6 | 3 | 3 | 3 | 3 | 3 | 4 |
| kogge | 149.7 | 24 | 0.534 | 80.3 | 274.6 | 147.4 | 4 | 2 | 2 | 2 | 4 | 2 |
| cmpcarry | 196.0 | 17 | 0.434 | 85.9 | 327.5 | 143.0 | 5 | 1 | 1 | 4 | 5 | 1 |
| yosys `+` (banned) | 118.0 | 33 | 0.760 | 89.7 | 246.4 | 188.6 | 2 | 4 | 5 | 5 | 2 | 5 |

(`yosys` shares depth rank 4 with ripple.) Readings: delay ranks equal depth ranks except the banned baselines
(hidden inverters); energy ranks equal area ranks for the adders; the multiplier energy and EDP ranks move
(array 2nd to last in energy once glitches count); AT ranks differ from GE x depth ranks for the adders (ripple 4th to
1st, comparison-carry 1st to 4th) but the AT spread is only 13%. Pareto sets of the **proved** multipliers:
(GE, depth) {array, tree_h}; (GE, T) and (GE, T, Eg) {array, tree_h, wallace}; (Eg, T) {wallace}.

## 7. Recommendation, staged by value per effort

| stage | what | effort | new tools | status of the evidence |
|---|---|---|---|---|
| **1** | Port the spike to `score/ppa.py` (liberty reader, netlist reader, NLDM STA, tests incl. the `ge.json` derivation and golden values for the 12 designs); `ppa_pins.json`; `score.py` emits `ppa{t_ps, area_um2_m, leak_pw}`; record fields; README "Scoring" paragraph. Delay and library-priced area become extra columns beside GE and depth | **2 days** | none | working code exists (600 lines), validated vs ABC `stime` |
| **2** | Energy: zero-delay + glitch-aware, salted stimulus, `scoring.ppa` in `task.json`, the scorer-vs-Verilator self-test, postsynth netlist-hash tie; derived AT/AT^2/EDP/ED^2P/perf-per-energy; leaderboard record `/2`, `pareto --objectives`, projections, presets, golden board test | **2 to 3 days** | none | working in the spike; the integration with `check.py`/`leaderboard.py` is the cost |
| **3** | FPGA columns from Yosys only: LUT4/LUT6, levels, carry/DSP/BRAM, `synth_ice40` pinned; banlist-style rules for carry/DSP/BRAM inference per task | **1 to 2 days** | none | measured (`fpga_yosys.py`) |
| **4** | Linux CI: build OpenSTA at a pinned tag and fail if the Python STA differs by more than 5% on any reference; OSS CAD Suite (date-pinned) with nextpnr for FPGA fmax (seed list, `--threads 1`); double-run determinism checks | **about 1 week** | OpenSTA, OSS CAD Suite | estimates; nothing installed here |
| **5** | Optional, weeks: A1 liberty flow as an alternative flow; clocked-design metrics with T6 (flops, `T_clk,min`, per-cycle energy, CPI x T); ORFS nightly extra columns (Docker/Nix on Linux) | **2 to 4 weeks** | OpenROAD, Docker/Nix | unmeasured; determinism open |

Stages 1 to 3 (about 5 to 7 days) need no installation by anyone and no change to the accepted-submission rules;
they add columns and views only. Order by value per effort: delay (stage 1) > the combined AT/EDP and the
energy columns (stage 2) > FPGA counts (stage 3) > everything that needs a new tool.

### Decisions for the maintainers

1. **Official flow:** A0 now (recommended), A1 later or never? A0 keeps every existing record valid and the GE
   language; A1 re-issues every record and the mapper ranking is unstable (tau 0.4 to 0.9).
2. **FPGA and physical: extra columns (recommended) or separate contests?** Extra columns on the same accepted
   records keep one proof requirement and one board per task; a separate contest needs its own baselines, pins
   and acceptance. Physical is nightly and maintainer-run either way.
3. **Cell library:** Nangate45 typical (recommended). Accept the licence caveat (fetch from ORFS at the pinned
   hash, never mirror)? Later add ASAP7 or Sky130 as a second "technology"?
4. **ANDNOT/ORNOT pricing:** keep 1.333 GE as today and document that the library realisation is 1.667 (no
   record changes), or reprice (new flow hash, all records re-issued)?
5. **Which energy ranks:** zero-delay (area proxy, robust, no delay model) or glitch-aware (a different quantity,
   model-dependent magnitude, ranks the array multiplier last by 2.5x)? Recommendation: record both, rank by
   glitch-aware, say so in the README.
6. **Stimulus and workload:** uniform random inputs, 2001 vectors, salted from the canonical text plus a secret
   for official runs, per-task `workload` statement. Agree?
7. **Pareto:** keep (area, depth) as the default board and make `--objectives area,t,e` opt-in per task
   (recommended), or switch the default?
8. **Containers:** no container requirement on contestants; OSS CAD Suite (date-pinned) as the optional pinned
   toolbox; Docker/Nix only in maintainers' Linux CI.
9. **Unit depth stays?** Recommended yes: exact, integer, mapper-light; `T` is the physical column beside it.

### Risks

* **Non-determinism.** Python scorer: none (measured). nextpnr and OpenROAD: unverified across machines and thread
  counts; mitigations are pins plus a CI double-run and "median of a fixed seed list".
* **Contestant burden.** Stages 1 to 3: zero new installs. Stages 4 and 5: none for contestants by design.
* **Run time per submission.** +0.6 to 8 s (A0), about +1 s per design for the Yosys FPGA counts; against a 45 to
  180 s check this is noise. nextpnr and ORFS are CI-side.
* **Cheating surfaces.** Stimulus overfitting (salt, large K), STA blind spots (fail closed on any unmodelled
  cell/construct), FPGA inference loopholes (carry, DSP, BRAM), tool-knob control (none given to the player), the
  scorer itself as trusted code (it joins the integrity tripwire's file list), clocked-design tricks (T6).
* **Model risk.** One predictive 45 nm library; no wires in A0; mapper noise of 10 to 20% between similar
  multipliers; glitch magnitude depends on the delay model; uniform inputs. Say "ranking, not picoseconds".
* **16 GB Mac realism.** Stages 1 to 3 run in under a second to a minute per design and about 100 MB; do not
  attempt ORFS or an OpenROAD source build on the same machine as a Lean slot job; Docker Desktop with amd64
  emulation would need several GB and is slow. Use Linux CI.
* **Licences.** Nangate header on the liberty file; OpenSTA is GPL-3.0 (run as a subprocess); OSS CAD Suite bundles
  mixed licences (distribute nothing, pin by date).
* **Spike limits.** 90-line STA validated against ABC's STA, not OpenSTA; internal-power units assumed (fJ);
  N = 16 mostly; see [spike/README.md](spike/README.md).

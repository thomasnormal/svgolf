# Flows A to D: what each adds, what it costs, what changes in svGolf

Times marked *measured* are from this machine (M2 Pro, 12 cores) at N = 16 / 32 with the spike's code; times
marked *estimate* are mine and were not measured (the tool is not installed). The baseline is today's pinned
flow (`score/score.py`): 0.4 to 0.7 s for the `add` designs, 0.7 to 2.5 s for the `mul` designs at N = 16,
2 to 6 s at N = 32 (*measured*), inside a `check.py` run of 45 to 180 s.

## Flow A: ASIC-lite in the present Yosys flow

Two variants; the spike measured both.

**A0, "weight the scored netlist".** Keep `canon.ys` and `svgolf.ys` exactly as they are (so every existing
record stays valid). After the flow, a new scorer module reads the netlist it wrote and the pinned liberty:

1. rewrite each Yosys gate as the Nangate45 `_X1` cell (`ANDNOT`/`ORNOT` as `INV_X1` + `NOR2_X1`/`NAND2_X1`; the
   only non-1:1 step, and the reason the area and unit depth of the expansion differ slightly from the score:
   `mul_yosys` 59 levels become 61, areas move by 0.0% to +1.2%);
2. **delay** `T_crit`: NLDM STA as defined in `metrics.md` section 1;
3. **energy** `E_op`: bit-parallel simulation over the pinned stream, toggle counts, `1/2 C V^2` + liberty
   internal energy; glitch-aware variant by event simulation; leakage from the liberty.

*Adds over today:* a delay in picoseconds that knows an XOR from a NAND and a fan-out of 16 from 2, an energy per
operation, the derived AT/EDP/ED^2P/perf-per-energy, and an area in um^2 that agrees with the GE score
(`libraries.md`). *Per-run time (measured):* liberty parse 0.33 s (once per process); STA 0.02 s and zero-delay simulation of 2001
vectors 0.04 s for the 1400-gate array multiplier, so the zero-delay pass is 0.6 s end to end including Python
start-up; the glitch-aware pass over 1000 vector pairs adds 3 to 8 s for a 16-bit multiplier (24 s over 300 pairs at
N = 32) and 0.2 s for an adder. *Tools/versions to pin:* Yosys as
now; the liberty (commit and sha256); the scorer script's sha256; the stimulus specification.
*Reproducibility:* bit-identical (measured, `spike/determinism_check.sh`); no new tool, no thread, no seed beyond the
stimulus.

**A1, "map onto the library".** Replace `abc -g <gate list>` by `abc -liberty LIB -constr C [-D ps]` (or the `&nf`
default without `-constr`), so ABC itself optimizes against real delays and areas, with sizing. The spike ran it on
the same canonical RTLIL: with the full Nangate45 (135 cell groups) and with a generated 9-cell subset
(`spike/mklib8.py`, the gate kinds of today's flow). *Adds over A0:* a netlist that a tape-out flow would
recognize (multi-input AOI/OAI cells, sizing), delay/area trade-off controlled by `-D` (a Pareto curve per design
instead of a point). *Costs / findings (measured):* (i) `-D` is inert without `-constr` (identical netlists for any D);
(ii) the delay ranking of the multipliers depends on the mapper: Kendall tau of the NLDM delay ranking between
`abc -g` + expansion, full-library `&nf` and 9-cell `&nf` is +0.90 / +0.43 / +0.52 over the seven `mul` designs
(+0.8 to +1.0 for `add`), so delay differences below roughly 10 to 20% between structurally similar multipliers are
mapper noise, whichever flow is chosen; (iii) A1 changes every record and the commutation/ordering residuals the
README documents would have to be re-measured; (iv) ABC runtime with liberty on very large inputs is unmeasured
(`dadda_ks_32` already exceeds the 1800 s limit under `abc -g`). *Per-run time (measured):* 0.3 to 4 s per mapping at
N = 16, same order as A0. **Recommendation: A0 is the official flow, A1 stays a research column** until a month of
data says the two disagree where it matters.

**The pinned STA is validated.** On 72 netlists produced by `abc -liberty -constr` (all 12 designs x 6 delay targets),
the spike's STA and ABC's own `stime -p` (an independent implementation, different slew treatment, input driven by
`BUF_X1`) agree to a mean absolute difference of 1.3%, maximum 5.5%. That is the evidence that a 90-line Python STA
is a legitimate scorer, and it is the check to repeat against OpenSTA when a Linux CI has it.

**Changes needed (A0):**

* `score/`: new `ppa.py` (liberty reader, netlist reader, STA, simulator; the spike's `liberty.py`, `netlist.py`,
  `engine.py`, `vectors.py` are the starting point, about 600 lines of standard-library Python), `ppa_pins.json`
  (liberty URL, commit, sha256; PO load; PI slew; V; stimulus parameters), `fetch_lib.py`, `derive_ge.py` as a test
  (the table of `libraries.md`); `score.py` returns an extra `ppa` object and `liberty_sha256`,
  `ppa_script_sha256`; `tests/expected.json` gains the golden `t_ps`/`e_aj` of the 12 designs.
* `check.py` / `task.json`: `scoring.ppa` = `{ "stimulus": {"kind": "uniform", "vectors": 2001, "salted": true},
  "metrics": ["t", "e"] }` per task (default: off, so an old task is unchanged), and a `workload` statement for tasks
  where uniform random inputs are the wrong benchmark.
* **Post-synthesis consistency (the scored netlist must be the netlist the function check sees):** the PPA pass
  takes the netlist file `score.py --netlist` wrote, which is the file `postsynth.py` simulates and re-reads; the
  checker passes its sha256 to the PPA pass and the record stores it, so the number belongs to a netlist whose
  function was compared with ls-sv. The expansion to Nangate cells is a pure, deterministic function of that file.
  The scorer's own evaluator is a second implementation of gate semantics: add a self-test that runs it and Verilator
  on the same vectors for every scored netlist (cheap: 0.4 microseconds per vector in Verilator) and rejects on any
  difference. For A1 netlists, `postsynth.py` needs cell models: emit them from the liberty `function` strings
  (`module NAND2_X1(...)`, 30 lines), and its "fresh Yosys re-reads the netlist and counts the scored gates" step
  becomes `read_liberty -lib` + `stat -liberty`.
* Leaderboard: section 7 below.
* README: a "Scoring" paragraph and the metric table of `metrics.md`.

## Flow B: ASIC with OpenSTA, activity from a simulation of the mapped netlist

*What it adds over A:* an industry-standard second opinion on delay (SDC, rise/fall, `report_checks` with the
path), and the standard power report (`report_power`: internal, switching, leakage groups, from a SAIF/VCD of the
pinned vectors simulated by Verilator or Icarus on the mapped netlist). *Cost:* OpenSTA is not packaged for macOS
(`tools.md`): source build with CUDD; Linux CI only. Run time per design *estimate* under a second; the simulation
to produce activity is the existing Verilator build (about 1.5 s) plus a VCD/SAIF writer. *Pin:* OpenSTA tag, the
SDC (three lines: `set_input_transition`, `set_load`, `create_clock -name vclk` for combinational blocks with
`set_input_delay`/`set_output_delay` 0), liberty sha256. *Reproducibility:* deterministic for a pinned build
(single-threaded analysis). *Use:* cross-check of A (a CI job that reports the difference between the Python STA
and OpenSTA on every reference and fails above, say, 5%); not an additional burden on contestants. OpenSTA is GPL-3.0
(dual-licensed); invoking it as a subprocess does not affect the repository's license.
*Honest limit:* its SAIF/VCD power uses the library's state-dependent models differently from the spike's mean
over tables, so absolute energies will not match; compare rankings.

## Flow C: FPGA with Yosys `synth_ice40` / `synth_ecp5` / `synth_xilinx` + nextpnr

*What it adds:* a cost model with the opposite biases: LUT counts and LUT levels instead of gates and gate depth,
carry chains, flip-flops, BRAM and DSP inference, and (nextpnr) routed delay and fmax. *Measured here (Yosys half,
`spike/fpga_yosys.py`):* at N = 16 the multipliers rank differently in LUT4s than in GE (the array multiplier moves
from 2nd smallest to largest and has 38 LUT4 levels against 22), and the adders' comparison-carry design hides 133
carry cells behind 48 LUTs (`metrics.md` section 6). The Yosys part for all 12 designs (six syntheses each) takes about a minute. *nextpnr (not installed):* place and route of a 700 to 1700
LUT4 block takes *estimate* a few seconds to a minute on iCE40/ECP5; fmax depends on the seed.
*Tools/versions to pin:* Yosys (the OSS CAD Suite date), nextpnr version, device and package (for example
`--hx8k --package ct256`, speed grade), `--freq`, seed list, `--threads 1`. *Reproducibility:* Yosys yes; nextpnr
seed-pinned, reproducibility across machines unverified (CI double-run).
*Changes:* `scoring.fpga` in `task.json` (target, frequency, seeds), record fields `lut4`, `lut4_levels`, `carry`,
`ff`, `bram`, `dsp`, `fmax_khz`; a banlist-equivalent for inference loopholes (carry, DSP, BRAM) decided per task;
the post-synthesis check does not apply to FPGA netlists directly: the FPGA run starts from the same canonical RTLIL
the function check saw, and a Verilator simulation of the `synth_*` output netlist (Yosys can write simulatable
Verilog with the vendor `cells_sim.v`) is the corresponding equivalence step.

## Flow D: physical design (ORFS-style) for wirelength, congestion, parasitic-aware timing and power

*What it adds:* the only flow that sees wires: placed-and-routed wirelength, congestion, achieved utilization,
post-route timing with extracted parasitics and the matching power. It is also where Kogge-Stone's long wires,
Sklansky's fan-out and the array multiplier's regular layout stop being guesses. *Cost:* OpenROAD/ORFS, no macOS
binaries (`tools.md`): Docker with amd64 emulation (daemon off here), Nix, or a Bazel source build; a full
flow on a 2000-gate Nangate45 block takes *estimate* one to two minutes natively and several times that
under emulation; non-determinism is the open risk (`metrics.md` section 7). *Pin:* container image digest,
platform commit, floorplan parameters (core utilization, aspect), `-threads 1`, seeds, median of a fixed seed list.
*Recommendation:* a maintainers' nightly job on Linux that produces extra columns for the records on the board; not a
contest track, not a gate on acceptance, and not part of the contestant's local loop.

## 7. Leaderboard changes (all flows)

* **Record schema `svgolf-leaderboard-record/2`**: `score` gains `ppa` (`t_ps`, `e_zero_aj`, `e_glitch_aj`,
  `leak_pw`, `area_um2_m` as integer milli-um^2, plus FPGA `lut4`, `lut4_levels`, `carry`, ... when that lane is
  on) and `checker` gains `liberty_sha256`, `ppa_script_sha256`, `stimulus` (kind, vectors, `salted`), `netlist_sha256`
  (the file the postsynth stage simulated). `/1` records stay valid and appear on the area/depth board only;
  everything numeric stays an integer so `record_hash` canonicalization is unchanged (floats were already the
  fragile part of `/1`).
* **Pareto in more than two scores:** `pareto --objectives area,t,e` with the same "no one beats or ties on all and
  beats on one" rule (ties kept), layers as now; the board prints the frontier plus the three 2-D projections
  (area-delay, area-energy, delay-energy) because a 3-D frontier is not readable as a list. `--objectives
  area,depth` stays the default so nothing changes until a task opts in.
* **Presets** (rankings on top of the frontier, like the existing `depth_budget` ranking): `smallest-area@t<=X`
  (X from the command line or `task.json`'s `leaderboard.presets`), `best-edp`, `best-at`, `best-ed2p`,
  `lowest-energy@t<=X`, `best-perf-per-energy`. Presets are views of recorded integers; they never need a rescore.
* **Comparability** follows the existing rule: the board ranks only records whose pinned hashes equal the current
  flow (now including `liberty_sha256` and `ppa_script_sha256`); the others are listed under "Not ranked".

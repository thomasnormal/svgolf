# Metric definitions: what we would pin, what it needs, how it is gamed, whether it is deterministic

Conventions for every metric below (they are the ones `area_mge` already follows): the value is reported as an
**integer in a fixed small unit** (picoseconds, attojoules, milli-GE, ...), computed from integers or from
IEEE-754 double arithmetic in a fixed order, so that equal inputs give byte-equal records; the record carries
the sha256 of everything the number depends on (liberty file, scorer script, stimulus specification, tool
versions); and boards rank only records whose hashes equal the current pinned flow (the existing policy).

"Combinational" is what every task is today. "Clocked" is track T6 (PLAN2.md): the differences are collected in
the last column and in section 9.

## 1. Delay (and fmax)

| | |
|---|---|
| **Definition** | `T_crit`: the longest primary-input to primary-output arrival time, in ps, from a rise/fall NLDM static timing analysis of the scored netlist mapped onto the pinned liberty: arrival and slew per (net, edge); each cell arc evaluated by bilinear interpolation of `cell_rise/cell_fall` and `rise_transition/fall_transition` at (input slew, load); load = sum of fan-out pin capacitances + a fixed 6.8 fF on every primary-output bit (4 x `INV_X1` input capacitance); primary inputs ideal, slew 10 ps; **no wire capacitance**; worst arrival wins, worst slew is merged per net and edge (graph-based analysis, the OpenSTA convention); conditional (`when`) arcs all taken, so the result is structural (no false-path analysis). Rounded to integer ps. Spike implementation: `Design.sta_nldm` in `spike/engine.py`, 90 lines |
| **Tool / command** | Python scorer (`score/ppa.py`, to be written from the spike) over the Yosys-written netlist; cross-check: OpenSTA `read_liberty L; read_verilog N; link_design top; set_input_transition 0.01 [all_inputs]; set_load 6.8 [all_outputs]; report_checks -path_delay max -unconstrained` (Linux CI) |
| **Needs** | liberty (pinned sha256), the netlist, nothing else; no constraints file |
| **Combinational vs clocked** | clocked: `T_clk,min` = max over input-to-register, register-to-register, register-to-output and input-to-output paths of arrival + setup (clk-to-q at the launching flop, ideal clock, zero skew, hold ignored or checked separately); `fmax = 1/T_clk,min`; latency in cycles comes from the task statement, throughput = fmax / initiation interval |
| **Gaming and defence** | (i) *False paths*: structural STA counts a path no input can sensitize (a carry-skip adder's skip path), so such designs are **penalized, not rewarded**; the bias is against clever skip/select designs, say so in the README, and optionally record an informational observed-delay from the glitch simulation. (ii) *Constructs STA mishandles* (combinational loops, latches, tri-states, multiple drivers, `x`): the scorer rejects every cell and construct it does not model (fail closed, as the GE table does today for unpriced cells) and the `fourstate` stage already refuses loops. (iii) *Tool knobs*: with a mapping flow (`abc -liberty -D`) the delay target changes sizing, so the target is part of the pinned flow, never the player's. (iv) *Wire load, PO load, input drive* are constants of the flow. (v) *Logic synthesis removes* what is unobservable: that is the point of scoring the synthesized netlist |
| **Deterministic?** | **Yes, bit-identical.** Pure Python, IEEE-754 double (+ - * / only), deterministic iteration order. Measured: `spike/determinism_check.sh` reproduces the JSON byte for byte under different `PYTHONHASHSEED`s, and the scored netlist is byte-identical on re-synthesis. One trap found and fixed in the spike: summing floats over a `set` of net names made the energy depend on the hash seed (last digit); iterate sorted |
| **Validation (measured)** | on 72 netlists mapped by `abc -liberty -constr` the spike STA agrees with ABC's own `stime`: mean 1.3% (max 5.5%) |

## 2. Dynamic power and energy per operation

| | |
|---|---|
| **Definition** | `E_op` in aJ: the mean over `K` consecutive vector transitions of a pinned input stream of `sum_nets toggles * 1/2 C_net V^2  +  sum_gates (rises * E_int,rise + falls * E_int,fall)`, with `C_net` = fan-out pin capacitances (+ PO load on primary outputs; primary-input nets count too, they are driven by the environment), `V` = the liberty's nominal voltage (1.1 V), `E_int` = the cell's liberty `internal_power` tables (mean over its tables) at (worst input slew, load). Two variants: **zero-delay** (functional toggles, each net toggles at most once per transition) and **glitch-aware** (event-driven simulation with inertial delays, rise/fall gate delays taken from the STA; pulses shorter than the gate delay are swallowed). Power at full throughput = `E_op / T_crit` |
| **Tool / command** | Python: bit-parallel evaluation of the netlist (liberty `function` strings compiled once) for zero-delay; `timed_toggle_counts` for glitch-aware. Cross-check: Verilator/Icarus dump a VCD or SAIF of the same vectors, OpenSTA `read_saif`/`read_vcd` + `report_power` (internal + switching + leakage groups) |
| **Needs** | liberty with `internal_power` and pin capacitances; a **stimulus**: the pinned stream (spike: vector `k` = SHA-256 of `"svgolf-ppa-spike/<seed>/<k>"`, uniform over all input bits); a workload statement per task (uniform for `add`/`mul`); a delay annotation for the glitch variant |
| **Combinational vs clocked** | clocked: per-cycle energy = data toggles + clock-pin toggles (two transitions per flop per cycle, activity 1) + clock-tree estimate; the stimulus must be a pinned input trace with its idle cycles (and, for a CPU, a pinned program), energy per task = cycles x per-cycle energy |
| **Gaming and defence** | (i) *Pin inputs constant*: not available in a combinational task (the platform drives every input); in a clocked task the trace includes idle/enable phases chosen by the platform. (ii) *Vector dependence*: a combinational design cannot remember vectors, so it can only specialize by comparators on the stimulus (area it pays for); defence: seed the stream from the canonical text hash and a secret salt for official runs (as `postsynth` already does), `K` large. Sampling noise measured: at 2000 transitions the zero-delay energy moves by at most 1.0% between three seeds (mul) and 0.5% (add), so differences under about 2% are noise at that `K`. (iii) *Workload mismatch*: uniform random inputs favour different designs than small-operand workloads; state the workload in `task.json`. (iv) *Model dependence of glitches*: the zero-delay number is nearly an **area proxy** (Kendall tau against GE +0.90 over the seven `mul` designs), the glitch-aware number is not (tau -0.14) and shows array multipliers glitching 5 times (N = 16) to 11 times (N = 32) more than trees; the magnitude depends on the delay model, so publish both and choose which one ranks. (v) *Logic synthesis removes* dead toggling logic: fine |
| **Deterministic?** | Yes if the stimulus is a pinned function of integers and the toggle counts are integers (they are); energies are then a fixed-order float sum, or better an **integer sum of per-net integer weights** (aJ), which removes even the floating-point question. Event ordering in the glitch simulation is by (time, sequence number): deterministic |

## 3. Leakage

`P_leak = sum of cell_leakage_power` (state-independent average from the liberty, nW); `E_leak,op = P_leak * T_crit`
(measured: 0.7% to 4.4% of the zero-delay `E_op` for the 16-bit designs, so second-order here, more important for large idle
blocks and clocked designs). Needs only the netlist and liberty. Deterministic. Gaming: none beyond area; for
clocked designs, power gating is not in the cell set (do not admit isolation/retention cells). The liberty also
has `when`-conditional leakage; a state-dependent leakage under the stimulus is possible (and a vector-dependence
channel): do not use it.

## 4. Performance per watt

For a combinational block run back to back at its minimum period, `performance = 1/T`, `power = E_op/T`,
hence **performance per watt = 1/E_op**: it carries no delay information (a slower design with the same energy per
operation ties). It is useful only with leakage (`1/(E_dyn + P_leak T)`), under a power or frequency cap, or for
clocked designs where throughput is `fmax x IPC`. Report it as operations per picojoule, derive it from
`E_op`, and do not rank by it alone; the delay-aware figures are EDP and ED^2P.

## 5. Combined figures

| figure | definition | reading |
|---|---|---|
| **AT** | `area_ge x T_crit` (GE.ns) | cost of speed in silicon; the classic |
| **AT^2** | `area_ge x T_crit^2` | the VLSI-theory form (Thompson), weights delay more |
| **EDP** | `E_op x T_crit` (fJ.ns) | energy-delay product, the usual "efficient and fast" figure |
| **ED^2P** | `E_op x T_crit^2` | invariant to supply-voltage scaling to first order (E ~ V^2, T ~ 1/V), so the figure least tied to the library's 1.1 V |

All four are *views* computed from the recorded scores, never new measured quantities, so they cannot be
cheated except through their components; the board shows the components and the Pareto frontier, with presets
(section 8 of `flows.md`). A scalar product hides trade-offs (a tiny area for huge delay can tie): never the only
ranking.

## 6. FPGA family (LUT, FF, BRAM, DSP, carry, fmax)

| | |
|---|---|
| **Definition** | counts after the pinned Yosys script for the pinned target: `synth_ice40` (SB_LUT4, SB_CARRY, SB_DFF*, SB_RAM40_4K), `synth_ecp5`, or `synth_xilinx -family xc7` (LUT1..6, MUXF7/8, CARRY4, FDRE, RAMB, DSP48); **LUT levels** from `abc -lut K; ltp -noff`; **fmax / max delay** from nextpnr: `nextpnr-ice40 --hx8k --package ct256 --json d.json --freq F --seed S`, reading `Max frequency for clock` (clocked) or `Max delay <async> -> <async>` (combinational) |
| **Needs** | Yosys, nextpnr and the chip database of the pinned target (device, package, speed grade are part of the flow), a target frequency, seeds |
| **Measured (Yosys half only)** | `spike/fpga_yosys.py` at N = 16: generic `abc -lut 4` and `synth_ice40` agree within about 25% (e.g. `mul_array` 716 vs 761 LUT4); `synth_xilinx` is far from generic LUT6 on the same netlist (`mul_array`: 552 LUT6 generic against 890 LUT + 339 MUXF). **The LUT ranking of the multipliers differs from the GE ranking**: the array multiplier is 2nd smallest in GE and the largest in LUT4s (716) and levels (38 against 22) |
| **Gaming and defence** | *carry chains*: a comparison operator maps to the dedicated carry (`synth_ice40`: the comparison-carry adder uses 48 LUT4 + **133** SB_CARRY, the `+` adder 16 + 16): count carry cells as their own column and either weight them or ban the operators that infer them (in a task that bans `+` or `-` the banlist rejects run-time ordering comparisons since 2026-11-05, because Yosys builds each as an `$alu`; `cmp_carry.sv` is a banned baseline); *DSP* inference through `*` (banned today; the Yosys `*` multiplier maps to 0 LUTs on xc7 because it becomes DSP48 blocks); *BRAM/LUTRAM* inference from array constants (count BRAM, or ban memories); *fmax* depends on the requested frequency and on the seed (pin both; report the median of a fixed seed list) |
| **Deterministic?** | Yosys: yes (as the present flow). nextpnr: placement is seeded (`--seed`) and the project documents the option, but **bit-for-bit reproducibility across machines and thread counts is not established here** (not measured: nextpnr is not installed): pin version (OSS CAD Suite date), `--threads 1` where available, seeds, and verify by running twice in CI before trusting it for a ranking |
| **Clocked** | FF count is a first-class column (`DFF_X1 = 5.667 GE` also in the ASIC area); fmax is the nextpnr clock report; latency and II from the statement |

## 7. Physical-design family (wirelength, congestion, utilization, parasitic-aware timing and power)

| | |
|---|---|
| **Definition** | ORFS-style flow on the pinned platform: `floorplan` (core utilization and aspect ratio fixed by the flow), I/O placement, global placement, resize/repair, (CTS if clocked), global and detailed route, RC extraction. Reported: routed wirelength (um, from the detailed-route report), global-route overflow / congestion (`report_congestion`), core area and achieved utilization (`report_design_area`), **post-route timing** (OpenSTA with the extracted SPEF: `T_crit` with wire parasitics), post-route power (`report_power` with SPEF and the same SAIF) |
| **Needs** | OpenROAD + Yosys + KLayout (or OpenLane/LibreLane), the platform (LEF/tech/RCX rules), floorplan parameters, pin constraints, a clock (virtual, for combinational blocks) and SDC, seeds |
| **Gaming and defence** | floorplan knobs (utilization, aspect ratio, density) and I/O pin placement change wirelength and congestion: all fixed by the flow and applied after flattening; utilization is a trade (a loose floorplan lowers congestion and inflates area): report core area, not cell area, as the physical "area"; random placement seeds: pin or take the median of a fixed list; hierarchy tricks: the flow flattens |
| **Deterministic?** | **Not established, assume no across machines.** OpenROAD's docs claim a deterministic global placement across compilers and OSes; routing is multi-threaded; floating-point differences between x86 and arm are likely. Pin the container digest, `-threads 1`, seeds, and run twice in CI. Treat as "reproducible within a pinned container on one architecture", which is why it is a maintainers' job, not a contestant's |
| **Clocked** | CTS adds clock-tree skew, power and area; timing becomes setup/hold-slack aware; this is where the physical flow earns its keep (and costs the most) |

## 8. How determinism is pinned, in one table

| metric | deterministic in practice | pin |
|---|---|---|
| area (GE / um^2), depth (`ltp`), LUT counts | yes | Yosys version, script hashes (existing) |
| `T_crit` (Python NLDM STA) | yes, bit-identical (measured) | liberty sha256, scorer sha256, PI slew / PO load constants |
| `E_op` zero-delay and glitch-aware | yes, bit-identical (measured) | + stimulus spec (seed, `K`, salt) |
| leakage | yes | liberty sha256 |
| AT, EDP, perf/W | yes (arithmetic on the above) | none |
| OpenSTA numbers | yes for a pinned build | build tag, flags; **cross-check only** |
| FPGA fmax (nextpnr) | seed-dependent; reproducibility unverified | OSS CAD Suite date, seed list, `--threads 1`, target frequency |
| physical (ORFS) | unverified | container digest, `-threads 1`, seeds, median of a list |

## 9. What changes for clocked designs (T6) in one place

* **Area:** flip-flops are cells (`DFF_X1` 5.667 GE); the GE table gains flop rows from the liberty and the score
  stops refusing `$_DFF_*`; the clock input is not logic.
* **Delay:** `T_clk,min` with clk-to-q and setup, four path classes, ideal clock first; hold and skew belong to the
  physical flow. Multi-cycle paths and false paths cannot be declared by the player (no SDC from the player):
  a design that needs them is penalized.
* **Energy:** clock-pin toggling every cycle, data toggling from the pinned trace, idle cycles in the trace.
* **Throughput:** `fmax / initiation interval`; for a CPU, `CPI` on a pinned program (from a simulation of the
  design, which the checker already has for the proof's sake) times `T_clk,min`.
* **Gaming surface grows:** gating the clock or tying enables lowers power if the trace allows it; reset and
  initial-state tricks; latency padding; a design that only works at the pinned program. The statement
  (state machine against a spec for every input trace) is what closes the functional side; the cost model must
  only measure, on platform-chosen traces, the netlist whose function is proved.

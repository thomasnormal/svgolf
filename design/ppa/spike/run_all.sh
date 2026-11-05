#!/bin/sh
# Reproduce the whole PPA spike (about 6 minutes on an M2 Pro; Yosys 0.53, Verilator not needed).
# Needs: python3.12 with pyslang (score/srcgate.py), yosys on PATH (or $SVGOLF_YOSYS), network once for
# fetch_lib.py (6.7 MB Nangate45 liberty, sha256-pinned; or set PPA_NANGATE45_LIB).
set -e
cd "$(dirname "$0")"
python3.12 fetch_lib.py
python3.12 derive_ge.py   # ge.json against the library's areas

# 1. the scored netlists of the pinned flow (score/score.py), all points
python3.12 gen_netlists.py --n 8
python3.12 gen_netlists.py --n 16
# dadda_ks_32 exceeds score.py's 1800 s Yosys limit (tests/mul/baselines/README.md); N = 64 adders only
python3.12 gen_netlists.py --n 32 --only add_ripple add_sklansky add_kogge add_cmpcarry add_yosys \
    mul_array mul_tree mul_wallace mul_tree_h mul_dadda_rc mul_yosys
python3.12 gen_netlists.py --n 64 --only add_ripple add_sklansky add_kogge add_cmpcarry add_yosys

# 2. unit depth vs logical effort vs NLDM delay, area, toggle energy (zero-delay and glitch-aware)
python3.12 run_spike.py --n 16 --pairs 1000
python3.12 run_spike.py --n 8  --pairs 500
python3.12 run_spike.py --n 32 --pairs 300
python3.12 run_spike.py --n 64 --pairs 300
python3.12 run_spike.py --n 16 --no-timed --seed 2 --tag _seed2     # sampling noise of the zero-delay energy
python3.12 run_spike.py --n 16 --no-timed --seed 3 --tag _seed3

# 3. Flow A: abc -liberty re-mapping (unsized &nf, sized sweep over delay targets, energy points)
python3.12 flow_a.py --n 16
python3.12 flow_a.py --n 16 --sized
python3.12 flow_a.py --n 16 --pairs 400 --tag _energy
python3.12 flow_a.py --n 16 --sized --D 0 --pairs 400 --tag _energy

# 3b. the same remapping onto the 9-cell subset (generated from the pinned liberty)
python3.12 mklib8.py
python3.12 flow_a.py --n 16 --lib .cache/svgolf8.lib --pairs 400 --tag _energy

# 4. FPGA lane, Yosys half (LUT4/LUT6 counts and levels; synth_ice40, synth_xilinx)
python3.12 fpga_yosys.py --n 16

# 5. tables
python3.12 report.py --n 16 > data/report_N16.md

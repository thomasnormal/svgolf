#!/bin/sh
# The spike's numbers must be bit-identical across runs and hash seeds.
# Runs the energy/timing pass twice under different PYTHONHASHSEEDs and compares the JSON bytes.
set -e
cd "$(dirname "$0")"
PYTHONHASHSEED=1 python3.12 run_spike.py --n 16 --pairs 60 --only add_kogge mul_tree --tag _det1 > /dev/null
PYTHONHASHSEED=2 python3.12 run_spike.py --n 16 --pairs 60 --only add_kogge mul_tree --tag _det2 > /dev/null
cmp data/results_N16_det1.json data/results_N16_det2.json && echo "results: bit-identical across PYTHONHASHSEED"
# the netlist the flow writes is identical on a second synthesis
python3.12 ../../../score/score.py ../../../tests/add/baselines/add_n_sklansky.sv --top add_n --param N=16 --netlist data/_nl2.v > /dev/null
cmp data/_nl2.v data/netlists/add_sklansky_N16.v && echo "scored netlist: byte-identical on re-synthesis"
rm -f data/_nl2.v data/results_N16_det1.json data/results_N16_det2.json

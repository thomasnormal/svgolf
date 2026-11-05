#!/bin/bash
cd "$(dirname "$0")"
rm -f exh32_d3.txt
for wp in "5 11" "8 8"; do set -- $wp; nice -n 19 python3.12 run_v.py $1 $2 --sv fdivp3.sv --work build3_big --jobs 3 >> exh32_d3.txt; done
echo finished > exh32_d3.done

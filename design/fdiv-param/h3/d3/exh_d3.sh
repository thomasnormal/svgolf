#!/bin/bash
cd "$(dirname "$0")"
rm -f exh_d3.txt
nice -n 19 xargs -P 2 -L 1 sh -c 'python3.12 run_v.py $0 $1 --sv fdivp3.sv --work build3 --jobs 1 >> exh_d3.txt' < fmts_all.txt
echo finished > exh_d3.done

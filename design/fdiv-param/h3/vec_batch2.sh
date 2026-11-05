#!/bin/bash
cd "$(dirname "$0")"
for fp in "8 24" "8 8" "11 53" "5 11" "2 30" "6 30" "15 48" "2 62" "3 60" "12 20" "20 12" "16 16"; do
  set -- $fp
  nice -n 19 python3.12 run_vec.py $1 $2 200000 7 --model --sv fdivp2.sv >> vec_results_d2.txt 2>&1
done
echo finished >> vec_results_d2.txt

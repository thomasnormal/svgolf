#!/bin/bash
cd "$(dirname "$0")"
rm -f vec_d3.txt
for fp in "8 24" "11 53" "2 30" "6 30" "15 48" "2 62" "3 60" "12 20" "20 12" "16 16" "4 20" "10 40"; do
  set -- $fp
  nice -n 19 python3.12 run_vec.py $1 $2 200000 7 --model3 --sv fdivp3.sv >> vec_d3.txt 2>&1
done
echo finished >> vec_d3.txt

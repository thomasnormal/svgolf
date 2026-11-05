#!/bin/bash
cd "$(dirname "$0")"
for fp in "8 24" "8 8" "11 53" "5 11" "2 30" "4 20" "6 30" "10 40" "15 48" "2 62" "3 60" "12 20" "20 12" "24 8" "28 4" "16 16" "7 9" "9 7" "11 21" "13 27"; do
  set -- $fp
  nice -n 19 python3.12 run_vec.py $1 $2 200000 7 --model >> vec_results.txt 2>&1
done
echo finished >> vec_results.txt

#!/bin/bash
cd "$(dirname "$0")"
for fp in "16 16" "7 9" "9 7" "11 21" "13 27"; do
  set -- $fp
  nice -n 19 python3.12 run_vec.py $1 $2 200000 7 --model >> vec_results3.txt 2>&1
done
echo finished >> vec_results3.txt

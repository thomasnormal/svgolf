#!/bin/bash
cd "$(dirname "$0")"
# D2 at K = 13, 14 exhaustive
nice -n 19 xargs -P 3 -L 1 sh -c 'python3.12 run_v.py $0 $1 --sv fdivp2.sv --work build2 --jobs 2 >> exh14b.txt' < fmts14.txt
# the two 2^32 formats, both designs
for sv in fdivp.sv fdivp2.sv; do
  for wp in "5 11" "8 8"; do
    set -- $wp
    nice -n 19 python3.12 run_v.py $1 $2 --sv $sv --work build_big --jobs 4 >> exh32_$sv.txt
  done
done
echo finished > exh_more.done

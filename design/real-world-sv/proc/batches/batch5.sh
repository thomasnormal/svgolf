#!/bin/bash
. "${SCRATCH:?set SCRATCH to a scratch directory}/wpproc/env.sh"
unset SVGOLF_LEAN_WRAP
cd $WT/svgolf
mkdir -p $W/res $W/stages $W/dumps
run() { T=$1; F=$2; B=$(basename $F .sv); rm -rf $W/stages/$B; s=$(date +%s)
  PYTHONDONTWRITEBYTECODE=1 timeout 600 python3.12 check.py $T $F --unproved --tactics --no-trusted-build --no-score --sandbox off --ppa off --stage-dir $W/stages/$B > $W/res/$B.json 2> $W/res/$B.err
  python3 $W/sumres.py $B; echo "   ($B $(( $(date +%s) - s )) s)"; }
dump() { stage=$1; probe=$2; out=$3; s=$(date +%s)
  LEAN_PATH=$W/stages/$stage/build lake env lean $W/lowered/$probe > $W/dumps/$out 2>&1; echo "EXIT $?" >> $W/dumps/$out; echo "dump $out $(( $(date +%s) - s )) s"; }
run tasks/mul $W/lowered/t1_rows_n_assign.sv
run tasks/mul $W/lowered/t2_rows_n_alwayscomb.sv
run tasks/mul $W/lowered/t3_rows_2n_assign_plain.sv
dump t1_rows_n_assign Probe_eq_plain.lean t1_eq.out
dump t2_rows_n_alwayscomb Probe_eq_proc.lean t2_eq.out
dump t3_rows_2n_assign_plain Probe_eq_plain.lean t3_eq.out
echo BATCH5-DONE

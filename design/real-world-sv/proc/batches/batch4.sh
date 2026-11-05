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
run tasks/mul $W/lowered/s1_chain_assign_rows.sv
run tasks/mul $W/lowered/s2_chain_bit_alwayscomb.sv
dump s1_chain_assign_rows Probe_struct_plain.lean s1_struct.out
dump s1_chain_assign_rows Probe_eq_plain.lean s1_eq.out
dump s2_chain_bit_alwayscomb Probe_struct_proc.lean s2_struct.out
dump s2_chain_bit_alwayscomb Probe_eq_proc.lean s2_eq.out
echo BATCH4-DONE

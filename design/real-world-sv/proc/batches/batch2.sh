#!/bin/bash
# runs INSIDE one slot acquisition. v5 (proposed lowering of the natural clmul), v8 (unrolled), v6 (in-fragment shape probe), dumps
. "${SCRATCH:?set SCRATCH to a scratch directory}/wpproc/env.sh"
unset SVGOLF_LEAN_WRAP
cd $WT/svgolf
mkdir -p $W/res $W/stages $W/dumps
run() { T=$1; F=$2; B=$(basename $F .sv); rm -rf $W/stages/$B; s=$(date +%s)
  PYTHONDONTWRITEBYTECODE=1 timeout 600 python3.12 check.py $T $F --unproved --tactics --no-trusted-build --no-score --sandbox off --ppa off --stage-dir $W/stages/$B > $W/res/$B.json 2> $W/res/$B.err
  python3 $W/sumres.py $B; echo "   ($B $(( $(date +%s) - s )) s)"; }
run tasks/mul $W/lowered/v6_chain_alwayscomb_shape.sv
run tasks/mul $W/lowered/v5_clmul_chain_alwayscomb.sv
run tasks/aes_sbox $W/lowered/v8_unrolled_clmul4.sv
dump() { stage=$1; probe=$2; out=$3; s=$(date +%s)
  LEAN_PATH=$W/stages/$stage/build lake env lean $W/lowered/$probe > $W/dumps/$out 2>&1; echo "EXIT $?" >> $W/dumps/$out; echo "dump $out $(( $(date +%s) - s )) s"; }
dump v6_chain_alwayscomb_shape Probe_struct_proc.lean v6_struct.out
dump v6_chain_alwayscomb_shape Probe_eq_proc.lean v6_eq.out
dump v1b_clmul_chain_rowshift Probe_struct_plain.lean v1b_struct.out
echo BATCH2-DONE

#!/bin/bash
# runs INSIDE one slot acquisition (no nested slot acquisition)
. "${SCRATCH:?set SCRATCH to a scratch directory}/wpproc/env.sh"
unset SVGOLF_LEAN_WRAP
cd $WT/svgolf
mkdir -p $W/res $W/stages
run() { # task file
  T=$1; F=$2; B=$(basename $F .sv)
  rm -rf $W/stages/$B
  s=$(date +%s)
  PYTHONDONTWRITEBYTECODE=1 timeout 600 python3.12 check.py $T $F --unproved --tactics --no-trusted-build --no-score --sandbox off --ppa off --stage-dir $W/stages/$B > $W/res/$B.json 2> $W/res/$B.err
  python3 $W/sumres.py $B
  echo "   ($B $(( $(date +%s) - s )) s)"
}
for spec in "$@"; do run ${spec%%=*} ${spec##*=}; done
echo BATCH-DONE

#!/bin/bash
unset SVGOLF_LEAN_WRAP
SH="${LEAN_SURFACES:?set LEAN_SURFACES to a lean-surfaces checkout}"
W="${SCRATCH:?set SCRATCH to a scratch directory}/wph3/g0"
cd $SH/svgolf
s=$(date +%s)
timeout 280 lake env lean $W/$1.lean > $W/$1.out 2>&1
echo "exit $? in $(( $(date +%s)-s )) s" >> $W/$1.out

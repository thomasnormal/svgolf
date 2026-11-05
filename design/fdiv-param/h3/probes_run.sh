#!/bin/bash
# one acquisition: the construct probes against the SHARED tree's built tactics (read-only: lake env lean)
unset SVGOLF_LEAN_WRAP
SH="${LEAN_SURFACES:?set LEAN_SURFACES to a lean-surfaces checkout}"
W="${SCRATCH:?set SCRATCH to a scratch directory}/wph3/g0"
cd $SH/svgolf
s=$(date +%s)
timeout 280 lake env lean $W/probes.lean > $W/probes.out 2>&1
echo "exit $? in $(( $(date +%s)-s )) s" >> $W/probes.out

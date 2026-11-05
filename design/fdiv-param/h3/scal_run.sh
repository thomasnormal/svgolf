#!/bin/bash
# one acquisition: wall-clock per file (each file = import + load_sv + ONE tactic call); timeout per file in \$TO
unset SVGOLF_LEAN_WRAP
SH="${LEAN_SURFACES:?set LEAN_SURFACES to a lean-surfaces checkout}"
W="${SCRATCH:?set SCRATCH to a scratch directory}/wph3/g0"
TO=${TO:-100}
cd $SH/svgolf
for f in "$@"; do
  s=$(date +%s)
  timeout $TO lake env lean $W/scal/$f.lean > $W/scal/$f.out 2>&1
  rc=$?
  echo "$f exit $rc wall $(( $(date +%s)-s )) s errors $(grep -c 'error' $W/scal/$f.out)" >> $W/scal/log.txt
done

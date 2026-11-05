#!/bin/bash
# usage: run1.sh FILE.lean OUT TIMEOUT : one lake env lean run of a file against the shared tree's built tactics
unset SVGOLF_LEAN_WRAP
cd "${LEAN_SURFACES:?set LEAN_SURFACES to a lean-surfaces checkout}"/svgolf
s=$(date +%s)
timeout ${3:-600} lake env lean $1 > $2 2>&1
echo "exit $? in $(( $(date +%s)-s )) s" >> $2

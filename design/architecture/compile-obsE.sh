#!/bin/bash
# compile-obsE.sh: compile ObsCombE.lean (the CombTask transport to E-core-0) with the observation drafts it
# imports, in a scratch copy (same scheme as compile-obs.sh, whose module list does not include ObsCombE).
# Needs, built beforehand from the repository root:
#   lake build LeanModels.Sv.Kernel.Core0Obs LeanModels.Sv.Kernel.Core1Obs LeanModels.Sv.ObserveFrame \
#     LeanModels.Sv.Hier2 LeanModels.Sv.REdgeRun2
# and the built svgolf libraries.
#   SVGOLF_LEAN_WRAP=<slot wrapper>  command prefix for lake/lean (optional)
#   SCRATCH=<dir>                    where the scratch .olean files go (default: a fresh temp dir)
#   MODULES="SeqTask CounterCycle CounterE": the counter's cycle step from E (D-X1h); CounterCycle
#                                    needs python3.12 with pyslang for `load_sv`, as in compile-obs.sh
#   MODULES="SeqTask CounterCycle TaskV2 ObsComb CounterObs CounterE CounterEObs": the counter's
#                                    Obs-level inclusion (D-X1h)
#   STAGE=<dir>                      a check.py staging tree (`--stage-dir`) of an accepted record:
#                                    its build/ goes on the path, for the record instances
#                                    ObsCombEExample / ObsCombEAdd (`MODULES=ObsCombEAdd`, after
#                                    the default modules have been compiled into the same SCRATCH)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
SVGOLF=$(cd "$HERE/../.." && pwd)
SCRATCH=${SCRATCH:-$(mktemp -d)}
MODULES=${MODULES:-"SeqTask TaskV2 ObsComb ObsCombE"}
mkdir -p "$SCRATCH/src" "$SCRATCH/build"
cp "$HERE/../sequential/SeqTask.lean" "$HERE/../sequential/CounterCycle.lean" "$SCRATCH/src/"
cp "$HERE"/TaskV2.lean "$HERE"/ObsComb.lean "$HERE"/ObsCombE.lean "$HERE"/ObsCombEExample.lean \
  "$HERE"/ObsCombEAdd.lean "$HERE"/CounterE.lean "$HERE"/CounterObs.lean "$HERE"/CounterEObs.lean \
  "$SCRATCH/src/"
cd "$SVGOLF"
LP="$(lake env printenv LEAN_PATH):$SCRATCH/build${STAGE:+:$STAGE/build}"
for m in $MODULES; do
  echo "== $m"
  ${SVGOLF_LEAN_WRAP:-} lake env env LEAN_PATH="$LP" lean -R "$SCRATCH/src" \
    -o "$SCRATCH/build/$m.olean" "$SCRATCH/src/$m.lean"
done
echo "scratch: $SCRATCH"

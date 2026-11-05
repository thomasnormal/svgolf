#!/bin/bash
# compile-obs.sh: compile the observation-interface drafts of this directory (TaskV2, ObsComb, ObsSeq, CounterObs,
# CounterMachine, PreTask, RegFile, ObsCombRedrive, ContractTask)
# and the sequential sketches they import (../sequential/SeqTask.lean, CounterCycle.lean) in a scratch copy:
# nothing is written into the repository or into the built libraries. Same scheme as
# ../sequential/compile.sh. Needs, built beforehand from the repository root,
#   lake build LeanModels.Sv.Observe LeanModels.Sv.ObserveFrame LeanModels.Sv.CycleMachine \
#     LeanModels.Sv.REdgeRun2 LeanModels.Sv.FlatMemRun2 LeanModels.Sv.ObserveRedrive \
#     LeanModels.Sv.ContractFA
# and the built svgolf libraries; CounterCycle needs python3.12 with pyslang for `load_sv`.
#   SVGOLF_LEAN_WRAP=<slot wrapper>  command prefix for lake/lean (optional)
#   SCRATCH=<dir>                    where the scratch .olean files go (default: a fresh temp dir)
#   MODULES="TaskV2 ..."             which modules to compile, in order (default: all eleven)
#   STAGE=<dir>                      a check.py staging tree (`--stage-dir`) of an accepted record:
#                                    its build/ goes on the path, for the record instances
#                                    ObsRecExample / ObsRecAdd / ObsRecMul (`MODULES=ObsRecAdd`,
#                                    after the default modules have been compiled into the same SCRATCH)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
SVGOLF=$(cd "$HERE/../.." && pwd)
SCRATCH=${SCRATCH:-$(mktemp -d)}
MODULES=${MODULES:-"SeqTask CounterCycle TaskV2 ObsComb ObsSeq CounterObs CounterMachine PreTask RegFile ObsCombRedrive ContractTask"}
mkdir -p "$SCRATCH/src" "$SCRATCH/build"
cp "$HERE/../sequential/SeqTask.lean" "$HERE/../sequential/CounterCycle.lean" "$SCRATCH/src/"
cp "$HERE"/TaskV2.lean "$HERE"/ObsComb.lean "$HERE"/ObsSeq.lean "$HERE"/CounterObs.lean \
  "$HERE"/CounterMachine.lean "$HERE"/PreTask.lean "$HERE"/RegFile.lean \
  "$HERE"/ObsCombRedrive.lean "$HERE"/ContractTask.lean "$HERE"/ObsRecExample.lean "$HERE"/ObsRecAdd.lean "$HERE"/ObsRecMul.lean \
  "$SCRATCH/src/"
cd "$SVGOLF"                      # load_sv reads tests/seq_counter/reference/cnt.sv relative to svgolf/
LP="$(lake env printenv LEAN_PATH):$SCRATCH/build${STAGE:+:$STAGE/build}"
for m in $MODULES; do
  echo "== $m"
  ${SVGOLF_LEAN_WRAP:-} lake env env LEAN_PATH="$LP" lean -R "$SCRATCH/src" \
    -o "$SCRATCH/build/$m.olean" "$SCRATCH/src/$m.lean"
done
echo "scratch: $SCRATCH"

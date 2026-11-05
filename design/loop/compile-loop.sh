#!/bin/bash
# compile-loop.sh: compile the loop proof of this directory (LoopTask.lean: Bridge S as a task lemma;
# LoopTaskE.lean: the task statement over E-core-0, derived from E;
# g1/ClmulNested.lean: the nested procedural
# clmul, tests/clmul/attacks/proc_nested_for.sv, satisfies the clmul Statement for every N; g2/PriEnc.lean,
# g2/PopCount.lean: a priority encoder and a population count against local specs; `statement`
# provisional over run2, `statement_E0` derived from E; NoRun2.lean checks the E chains) in a scratch
# copy: nothing is written into the repository or into the built libraries. Same
# scheme as ../architecture/compile-obs.sh. Needs, built beforehand from the repository root,
#   lake build LeanModels.Sv.Loop2Clmul LeanModels.Sv.Loop2Slot LeanModels.Sv.ObserveFrame LeanModels.Sv.Hier2
# and the built svgolf libraries; `load_sv` needs python3.12 with pyslang.
#   SVGOLF_LEAN_WRAP=<slot wrapper>  command prefix for lake/lean (optional)
#   SCRATCH=<dir>                    where the scratch .olean files go (default: a fresh temp dir)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
SVGOLF=$(cd "$HERE/../.." && pwd)
SCRATCH=${SCRATCH:-$(mktemp -d)}
MODULES=${MODULES:-"SeqTask TaskV2 ObsComb ObsCombE LoopTask LoopTaskE ClmulNested PriEnc PopCount NoRun2"}
mkdir -p "$SCRATCH/src" "$SCRATCH/build"
cp "$HERE/../sequential/SeqTask.lean" "$HERE/../architecture/TaskV2.lean" "$HERE/../architecture/ObsComb.lean" \
  "$HERE/../architecture/ObsCombE.lean" "$SCRATCH/src/"   # A's and P's, unchanged
cp "$HERE/LoopTask.lean" "$HERE/LoopTaskE.lean" "$HERE/g1/ClmulNested.lean" "$HERE/g2/PriEnc.lean" "$HERE/g2/PopCount.lean" \
  "$HERE/NoRun2.lean" "$SCRATCH/src/"
cd "$SVGOLF"                      # load_sv reads its .sv paths relative to svgolf/
LP="$(lake env printenv LEAN_PATH):$SCRATCH/build"
for m in $MODULES; do
  echo "== $m"
  ${SVGOLF_LEAN_WRAP:-} lake env env LEAN_PATH="$LP" lean -R "$SCRATCH/src" \
    -o "$SCRATCH/build/$m.olean" "$SCRATCH/src/$m.lean"
done
echo "scratch: $SCRATCH"

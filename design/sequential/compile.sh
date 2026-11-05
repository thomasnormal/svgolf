#!/bin/bash
# compile.sh: compile the sketches of this directory in a scratch copy (nothing is written into the
# repository or into the built libraries). Run it from anywhere. Needs the built svgolf libraries
# (`lake build` in svgolf/) and python3.12 with pyslang for `load_sv`.
#   SVGOLF_LEAN_WRAP=<slot wrapper>  command prefix for lake/lean (optional)
#   SCRATCH=<dir>                    where the scratch .olean files go (default: a fresh temp dir)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
SVGOLF=$(cd "$HERE/../.." && pwd)
SCRATCH=${SCRATCH:-$(mktemp -d)}
mkdir -p "$SCRATCH/src" "$SCRATCH/build"
cp "$HERE/SeqTask.lean" "$HERE/CounterCycle.lean" "$HERE/CounterInst.lean" "$HERE/CounterTraces.lean" "$HERE/CounterG0.lean" "$SCRATCH/src/"
cd "$SVGOLF"                      # load_sv reads tests/seq_counter/reference/cnt.sv relative to svgolf/
LP="$(lake env printenv LEAN_PATH):$SCRATCH/build"
for m in ${MODULES:-SeqTask CounterCycle CounterInst CounterTraces CounterG0}; do
  echo "== $m"
  ${SVGOLF_LEAN_WRAP:-} lake env env LEAN_PATH="$LP" lean -R "$SCRATCH/src" \
    -o "$SCRATCH/build/$m.olean" "$SCRATCH/src/$m.lean"
done
echo "scratch: $SCRATCH"

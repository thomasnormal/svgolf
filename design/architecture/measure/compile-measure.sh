#!/bin/bash
# compile-measure.sh: typecheck the measurement instruments of this directory that are kept current (today:
# CombFragCensus.lean, the E-fragment census behind CFRAG.md). Nothing is written into the repository: `lean` without
# `-o` only elaborates. X2Preempt.lean and X12StdDo.lean are historical, pinned to the commits they measured
# (edce9ef8 and c7b56d30), and not built here. Needs, built beforehand from the repository root,
#   lake build LeanModels.Sv.Ingest2 LeanModels.Sv.CombFragE
#   SVGOLF_LEAN_WRAP=<slot wrapper>  command prefix for lean (optional)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
cd "$ROOT"
for m in CombFragCensus; do
  echo "== $m"
  ${SVGOLF_LEAN_WRAP:-} lake env lean "$HERE/$m.lean"
done

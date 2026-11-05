#!/bin/bash
# Lean checks for the trusted spec svgolf/tasks/fdivp/IEEE754.lean, through the svgolf Lake
# project (run from anywhere):
#   1. `lake build tasks.fdivp.IEEE754`: the trusted spec (definitions, #guard golden
#      vectors, kernel `decide`s); the proofs of its five characterization theorems are
#      the section `IEEE754Proofs` of the task's reference proof (reference/fdivp.lean),
#      which check.py checks (tests/run.py --only fdivp, step `references`);
#   2. the batch runner Run.lean used by validate.py (compile only).
# Environment: LEAN_WRAP (optional command prefix, e.g. a slot-limiting wrapper).
set -euo pipefail
SVGOLF="$(cd "$(dirname "$0")/../../.." && pwd)"
WRAP=(${LEAN_WRAP:-})
cd "$SVGOLF"
echo "== spec: lake build tasks.fdivp.IEEE754"
"${WRAP[@]}" lake build tasks.fdivp.IEEE754
echo "== runner: tasks/fdivp/spec_validate/Run.lean"
"${WRAP[@]}" lake env lean tasks/fdivp/spec_validate/Run.lean
echo "OK"

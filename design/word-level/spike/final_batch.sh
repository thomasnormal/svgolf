#!/bin/bash
# final_batch.sh: every spike file, ONE slot acquisition (run as `$SLOT bash final_batch.sh` from the worktree root)
cd "$(dirname "$0")"
D=svgolf/design/word-level/spike
./mk.sh B2Shape.lean S2c_shape.body S2d_shape.body S2e_xf.body S2g_rd.body S2z_axioms.body
./mk.sh B2ShapePrint.lean S2f_print.body
python3 dwify.py B2Shape.lean B2ShapeDw.lean
cd ../../../..
for f in S1Recognizer S2a_ext S3Glue S4Example; do
  echo "=== $f"; s=$(date +%s); lake env lean -DmaxHeartbeats=40000 $D/$f.lean 2>&1 | grep -v "^$\|Hint\|\[apply\]\|Note:" | cut -c1-600 | head -60; echo "--- $f $(( $(date +%s) - s )) s"
done
for f in B2Shape B2ShapeDw B2ShapePrint; do
  echo "=== $f"; s=$(date +%s); lake env lean -DmaxHeartbeats=40000 $D/$f.lean 2>&1 | grep -v "^$\|Hint\|\[apply\]\|Note:\|unused simp\|instExpr2$" | cut -c1-900 | head -80; echo "--- $f $(( $(date +%s) - s )) s"
done

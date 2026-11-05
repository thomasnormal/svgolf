#!/bin/bash
# usage: lc.sh TIMEOUT file1 file2 ... : compile the files (paths relative to wt/svgolf, e.g. tasks/fdivp/DpN.lean) in order,
# writing oleans to lc/olean/<module path>.olean; stops at the first failure. Output of each in lc/out/<name>.out.
unset SVGOLF_LEAN_WRAP
S="${SCRATCH:?set SCRATCH to a scratch directory}/wph3"
WT=$S/wt/svgolf
OL=$S/lc/olean
mkdir -p $S/lc/out
TO=$1; shift
cd "${LEAN_SURFACES:?set LEAN_SURFACES to a lean-surfaces checkout}"/svgolf
LP="$OL:$(lake env printenv LEAN_PATH)"
LEANBIN=$(lake env which lean)
for f in "$@"; do
  m=${f%.lean}; mkdir -p $OL/$(dirname $m)
  n=$(echo $m | tr '/' '_')
  s=$(date +%s)
  LEAN_PATH="$LP" timeout $TO $LEANBIN --root=$WT -o $OL/$m.olean $WT/$f > $S/lc/out/$n.out 2>&1
  rc=$?
  echo "exit $rc in $(( $(date +%s)-s )) s" >> $S/lc/out/$n.out
  echo "$f exit $rc $(( $(date +%s)-s )) s errors $(grep -c 'error' $S/lc/out/$n.out)"
  [ $rc -ne 0 ] && exit $rc
done
exit 0

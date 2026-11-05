#!/bin/bash
# usage: probe_task.sh TASKDIR FILE.sv   -> one summary line (+ error text)
SP="${SCRATCH:?set SCRATCH to a scratch directory}"
T=$1; F=$2; B=$(basename $F .sv)
cd "${LEAN_SURFACES:?set LEAN_SURFACES to a lean-surfaces checkout}"/svgolf
rm -rf $SP/stages/$B
mkdir -p $SP/stages $SP/res
PYTHONDONTWRITEBYTECODE=1 timeout 900 nice -n 19 python3.12 check.py $T $F --unproved --tactics --no-trusted-build --no-score --sandbox off --ppa off --stage-dir $SP/stages/$B > $SP/res/$B.json 2> $SP/res/$B.err
python3 - "$B" <<'PY'
import json,os,sys
SP=os.environ["SCRATCH"]
b=sys.argv[1]
try: j=json.load(open(f"{SP}/res/{b}.json"))
except Exception as e: print(b,"NO-JSON",e); sys.exit()
stage=j.get("stage"); err=" ".join(str(e) for e in j.get("errors",[]))[:500].replace("\n"," ")
tac=j.get("tactics")
tm=""
if tac: tm=" | TACTICS in_fragment=%s: %s" % (tac.get("in_fragment"), str(tac.get("message"))[:600].replace("\n"," "))
print("%s  stage=%s  %s%s" % (b, stage, err if stage!="unproved" else "(all non-proof stages pass)", tm))
PY

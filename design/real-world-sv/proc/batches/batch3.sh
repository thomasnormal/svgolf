#!/bin/bash
# batch3: typeless-port designs through check.py with the ONE-LINE ImplicitType spike applied for the duration of the batch only
. "${SCRATCH:?set SCRATCH to a scratch directory}/wpproc/env.sh"
unset SVGOLF_LEAN_WRAP
cd $WT
cp extractors/sv/extract.py $W/extract.py.batch3.bak
python3 - <<'PY'
p='extractors/sv/extract.py'
s=open(p).read()
old="""            if type_syntax is not None and type_syntax.kind in (
                    SyntaxKind.BitType, SyntaxKind.LogicType, SyntaxKind.RegType):"""
new="""            if type_syntax is not None and type_syntax.kind in (
                    SyntaxKind.BitType, SyntaxKind.LogicType, SyntaxKind.RegType,
                    SyntaxKind.ImplicitType):"""
if old in s: open(p,'w').write(s.replace(old,new))
PY
cd $WT/svgolf
mkdir -p $W/res $W/stages
run() { T=$1; F=$2; B=$(basename $F .sv); rm -rf $W/stages/$B; s=$(date +%s)
  PYTHONDONTWRITEBYTECODE=1 timeout 600 python3.12 check.py $T $F --unproved --tactics --no-trusted-build --no-score --sandbox off --ppa off --stage-dir $W/stages/$B > $W/res/$B.json 2> $W/res/$B.err
  python3 $W/sumres.py $B; echo "   ($B $(( $(date +%s) - s )) s)"; }
run tasks/mul $W/lowered/v9_typeless_ansi_inputs.sv
run tasks/mul $W/lowered/v10_typeless_nonansi.sv
cd $WT && cp $W/extract.py.batch3.bak extractors/sv/extract.py
echo BATCH3-DONE

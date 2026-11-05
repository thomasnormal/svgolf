#!/bin/bash
# mk.sh OUT body1 body2 ...: imports + S0_glue.body + S2b_defs.lean (minus last line) + the bodies + closing line
cd "$(dirname "$0")"
out=$1; shift
python3 - "$out" "$@" <<'PY'
import sys
out=sys.argv[1]; bodies=sys.argv[2:]
d=open('S2b_defs.lean').read().rstrip('\n').split('\n')
assert d[-1]=='end LeanModels.Sv.B2'
d=d[:-1]
i=[n for n,l in enumerate(d) if l.startswith('namespace LeanModels.Sv.B2')][0]
glue=open('S0_glue.body').read()
txt='\n'.join(d[:i])+'\n\n/-! ## The glue of part 3 (plain Lean) -/\n\n'+glue+'\n'+'\n'.join(d[i:])+'\n'
for b in bodies: txt+=open(b).read()
txt+='\nend LeanModels.Sv.B2\n'
open(out,'w').write(txt)
PY

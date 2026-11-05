import json, itertools
from gen_lib import *
duts.clear()
dut('p_local', [('a',1),('b',1),('c',1)], [('y',1)],
    "always_comb begin logic t; t = a ^ b; y = t & c; end",
    prod(['a','b','c'], [['0','1','x'], ['0','1','x'], ['0','1','x']]),
    'block-local temporary (begin logic t; ...): same value as a module-level temporary')
dut('p_partial', [('c',1),('a',1),('b',1)], [('y',2)],
    "always_comb begin if (c) y[0] = a; else y[1] = b; end",
    prod(['c','a','b'], [S1, ['0','1'], ['0','1']]),
    'per-bit latch: each bit is written on one path only; the other bit keeps its previous value (x at time 0)')
dut('p_rowwrite', [('c',1),('a',2),('b',2)], [('y',2)],
    "always_comb begin if (c) y = a; else y = b; end",
    [dict(c=c,a=a,b=b) for c in S1 for (a,b) in [('10','01'),('1x','0z'),('x1','1x')]],
    'vector target: the taken arm is copied bitwise, x/z included')
dut('p_widthext', [('c',1),('a',1)], [('y',4)],
    "always_comb begin if (c) y = a; else y = 4'b1111; end",
    prod(['c','a'], [S1, ['0','1','x']]),
    'a narrower right-hand side is zero-extended to the target (the width rule WidthObl forbids it in the fragment)')
dut('p_tern_ctx', [('a',1),('c',1)], [('y',4)],
    "assign y = c ? ~a : 4'b0000;",
    prod(['a','c'], [['0','1','x'], S1]),
    '~a in a 4-bit context is extended FIRST: ~{000a} = 111~a (context-determined), the trap for width-mismatched operands')
open('probe2.sv','w').write(tb_text())
json.dump(duts, open('probe2.json','w'), indent=1)
print(len(duts))

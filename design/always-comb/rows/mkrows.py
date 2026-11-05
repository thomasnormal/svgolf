#!/usr/bin/env python3
"""Stage the WP-G differential rows: one example directory per row (sem2/<name>/<name>.sv) and the
cases2.json fragment (cases_wpg.json). Gate 2 copies the directories into Examples/system-verilog/sem2/,
runs extractors/sv/extract.py --top <name> per row to make the .sv.json envelope, appends the cases to
harness/sv/cases2.json and pins them with xcelium_batch.py prepare/run --case <name>."""
import json, os

rows = []
def row(name, header, body, ins, outs, stim, **extra):
    sv = f"// {header}\nmodule {name} (\n" + ",\n".join(
        [f"  input  logic {'[%d:0] ' % (w-1) if w > 1 else ''}{n}" for n, w in ins] +
        [f"  output logic {'[%d:0] ' % (w-1) if w > 1 else ''}{n}" for n, w in outs]) + "\n);\n" + body + "\nendmodule\n"
    os.makedirs(name, exist_ok=True)
    open(f"{name}/{name}.sv", "w").write(sv)
    sig = [n for n, w in ins] + [n for n, w in outs]
    r = dict(name=name, example=f"sem2/{name}", top=name, signals=sig, stimulus=stim)
    r.update(extra)
    rows.append(r)

X1 = ['0', '1', 'x', 'z']
V2 = ['00', '01', '10', '11', '0x', 'x0', '1x', 'x1', 'xx', 'zz', '0z', '1z', 'xz']

# 1. procedural if: 1-bit and 2-bit conditions, !c versus the swapped twin, ~c
stim = []
for c in X1:
    for (a, b) in [('1', '0'), ('0', '1')]:
        stim.append(dict(c=c, a=a, b=b, v='00'))
for v in V2:
    stim.append(dict(c='1', a='1', b='0', v=v))
row('wpg_if_x', "WP-G four-state contract: a procedural `if` takes the ELSE branch unless the condition has a definite 1 bit "
    "(1-bit x/z -> else; 2-bit: 1x, x1, 1z are true, 0x, xx, zz are false). `if (!c)` with c = x is the else branch, NOT the "
    "swap of `if (c)` (y3 vs y4 differ at c = x); `if (~c)` likewise. Pinned against Xcelium 24.03.",
    "  always_comb begin if (c) y1 = a; else y1 = b; end\n"
    "  always_comb begin if (v) y2 = a; else y2 = b; end\n"
    "  always_comb begin if (!c) y3 = a; else y3 = b; end\n"
    "  always_comb begin if (c) y4 = b; else y4 = a; end\n"
    "  always_comb begin if (~c) y5 = a; else y5 = b; end",
    [('c', 1), ('a', 1), ('b', 1), ('v', 2)], [('y1', 1), ('y2', 1), ('y3', 1), ('y4', 1), ('y5', 1)], stim)

# 2. chains, nesting, default-then-override, two targets, taken/untaken x
stim = []
for c1 in X1:
    for c2 in X1:
        stim.append(dict(c1=c1, c2=c2, a='1', b='0', d='1', e='0'))
for (c1, c2, a, b, d, e) in [('1', '1', '1', 'x', '0', '0'), ('0', '1', 'x', '1', '0', '0'), ('1', '0', 'x', '1', '0', 'z'),
                             ('0', '0', '1', '1', 'x', '0'), ('0', '0', '1', '1', '0', 'z')]:
    stim.append(dict(c1=c1, c2=c2, a=a, b=b, d=d, e=e))
row('wpg_if_chain', "WP-G four-state contract: else-if chain (an x/z first condition falls to the second test), nested if/else, "
    "default then override (no latch), two targets under one if, and the value of the TAKEN arm only (x/z in the untaken arm "
    "never reaches the target; in the taken arm it does, z included). Pinned against Xcelium 24.03.",
    "  always_comb begin if (c1) y = a; else if (c2) y = b; else y = d; end\n"
    "  always_comb begin if (c1) begin if (c2) z = a; else z = b; end else z = d; end\n"
    "  always_comb begin w = 1'b0; if (c1) w = a; end\n"
    "  always_comb begin if (c1) begin u = a; v = b; end else begin u = b; v = a; end end",
    [('c1', 1), ('c2', 1), ('a', 1), ('b', 1), ('d', 1), ('e', 1)], [('y', 1), ('z', 1), ('w', 1), ('u', 1), ('v', 1)], stim)

# 3. conditional expression ?:
stim = []
for c in X1:
    for (a, b) in [('1100', '1010'), ('1111', '1111'), ('10x0', '1010'), ('1z10', '1x10'), ('0000', '0000')]:
        stim.append(dict(c=c, v='00', a=a, b=b, d='0', e='1'))
for v in V2:
    stim.append(dict(c='1', v=v, a='1100', b='1010', d='x', e='1'))
for c in X1:
    for d in X1:
        stim.append(dict(c=c, v='00', a='1100', b='1010', d=d, e='1'))
row('wpg_tern_x', "WP-G four-state contract: the conditional EXPRESSION `c ? a : b` is not the procedural `if`: a condition that is "
    "x/z MERGES the two arms bit by bit (equal known bits survive, every other bit is x), a condition with a definite 1 bit "
    "selects the first arm (so a 2-bit 1x selects it, 0x merges). Scalar and vector arms, a vector condition, a nested ?:, "
    "and the same ?: as the right-hand side of a procedural assignment. Pinned against Xcelium 24.03.",
    "  assign t1 = c ? a[0] : b[0];\n  assign t4 = c ? a : b;\n  assign tv = v ? a : b;\n"
    "  assign tn = c ? a[0] : (d ? b[0] : e);\n"
    "  always_comb begin tp = c ? a : b; end",
    [('c', 1), ('v', 2), ('a', 4), ('b', 4), ('d', 1), ('e', 1)], [('t1', 1), ('t4', 4), ('tv', 4), ('tn', 1), ('tp', 4)], stim)

# 4. ! versus ~
stim = [dict(a=a, v='00') for a in X1] + [dict(a='0', v=v) for v in V2]
row('wpg_not', "WP-G four-state contract: `!` is LOGICAL and self-determined (a 1-bit result, then zero-extended: !x = x, !2'b1x = 0, "
    "!2'b0x = x, !2'b00 = 1), `~` is BITWISE and context-determined (the operand is extended to the context FIRST: ~a "
    "assigned to 4 bits is 111~a). Pinned against Xcelium 24.03.",
    "  assign n1 = !a;\n  assign b1 = ~a;\n  assign n4 = !a;\n  assign b4 = ~a;\n"
    "  assign nl = !v;\n  assign nb = ~v;\n  assign nl4 = !v;\n  assign nb4 = ~v;\n  assign nn = !(!v);\n  assign nr = !(~v);",
    [('a', 1), ('v', 2)], [('n1', 1), ('b1', 1), ('n4', 4), ('b4', 4), ('nl', 1), ('nb', 2), ('nl4', 4), ('nb4', 4), ('nn', 1), ('nr', 1)], stim)

stim = [dict(a=a, c=c) for a in ['0', '1', 'x'] for c in X1]
row('wpg_tern_ctx', "WP-G four-state contract: `c ? ~a : 4'b0000` with a 1-bit a: the arm ~a is context-determined, extended to 4 bits "
    "before the inversion (111~a), and a merge of 111~a with 0000 under c = x is xxx~a-or-x. Pinned against Xcelium 24.03.",
    "  assign y = c ? ~a : 4'b0000;", [('a', 1), ('c', 1)], [('y', 4)], stim)

# 5. blocking order and a module-level temporary
stim = [dict(a=a, b=b, c=c) for a in ['0', '1', 'x'] for b in ['0', '1', 'x'] for c in ['0', '1', 'x']]
row('wpg_order', "WP-G four-state contract: blocking assignments run in order inside the body: the last write to a window wins "
    "(y = a; y = b gives b), and a module-level temporary assigned then read in the same body carries the value just "
    "written (z = (a ^ b) & c). Pinned against Xcelium 24.03.",
    "  logic t;\n  always_comb begin y = a; y = b; t = a ^ b; z = t & c; end",
    [('a', 1), ('b', 1), ('c', 1)], [('y', 1), ('z', 1)], stim)

# 6. the carry-select cell of the Gate 3 fixture, both as two bodies and as one multi-target body
stim = [dict(p=p, c=c, a=a) for p in X1 for c in X1 for a in ['0', '1']]
row('wpg_carry', "WP-G four-state contract and the Gate 2/3 cell: co = p ? c : a written as an if/else, s = p ^ c in the same body "
    "(multi-target), and the one-target twin. A z carry-in passes through the TAKEN arm unchanged (co = z at p = 1, c = z), "
    "an x/z propagate takes the else arm (co = a). Pinned against Xcelium 24.03.",
    "  always_comb begin if (p) co = c; else co = a; s = p ^ c; end\n"
    "  always_comb begin if (p) co1 = c; else co1 = a; end",
    [('p', 1), ('c', 1), ('a', 1)], [('co', 1), ('s', 1), ('co1', 1)], stim)

# 7. block-local declaration: refused by the loader today (LocalDecl), evidence from Xcelium
stim = [dict(a=a, b=b, c=c) for a in ['0', '1', 'x'] for b in ['0', '1'] for c in ['0', '1', 'x']]
row('wpg_local', "WP-G: a block-local temporary (`begin logic t; ...`) has the value semantics of a module-level temporary (Xcelium 24.03). "
    "The symbolic tier refuses it today (the envelope's LocalDecl statement is not ingested): REFUSAL row, the Xcelium trace "
    "is quoted in `measured`.",
    "  always_comb begin logic t; t = a ^ b; y = t & c; end",
    [('a', 1), ('b', 1), ('c', 1)], [('y', 1)], stim,
    refusal="unknown statement kind \"LocalDecl\"",
    measured="WP-G Gate 1 2026-10-30: Xcelium 24.03-s004 runs `begin logic t; t = a ^ b; y = t & c; end` with the value semantics "
             "of a module-level temporary: all 18 cycles of this stimulus equal y = (a ^ b) & c computed with the four-state AND/XOR tables "
             "(a=1,b=1 gives y=0 for every c including x; a=x,b=0,c=1 gives x; a=0,b=0,c=x gives 0). The symbolic tier refuses the envelope "
             "at ingestion (`Ingest2.parsePStmt`: the extractor's LocalDecl statement is not ingested); block-local temporaries are a later step (WP-G S3).")

# 8. per-bit latch
stim = [dict(c=c, a=a, b=b) for (c, a, b) in [('0', '0', '1'), ('1', '1', '0'), ('0', '1', '0'), ('1', '0', '1'), ('x', '1', '1'), ('1', '0', '0'), ('z', '0', '1')]]
row('wpg_partial', "WP-G no-latch rule: each bit of y is written on ONE path only; the other bit keeps its previous value "
    "(x before the first write). The settle semantics admits and runs it (CombGuard2 admits latches), the proof layer's "
    "lowering refuses it (selfReadFree). Pinned against Xcelium 24.03.",
    "  always_comb begin if (c) y[0] = a; else y[1] = b; end",
    [('c', 1), ('a', 1), ('b', 1)], [('y', 2)], stim)


# 9. reductions (S2): partial results survive unknown bits (| with a 1, & with a 0)
V4 = ['0000', '1111', '1010', '0101', '1x00', '0x00', 'x000', '1x11', '0x11', 'x111', 'xxxx', 'zzzz', '0z0z', '11z1', '10x1', '01x0', 'x1x1', '000z']
stim = [dict(v=v) for v in V4]
row('wpg_red', "WP-G four-state contract (S2): reduction operators on a 4-bit vector. `|v` is 1 when some bit is a definite 1 even with x/z "
    "elsewhere, 0 when all bits are 0, else x; `&v` is 0 when some bit is a definite 0, 1 when all bits are 1, else x; `^v` is x as soon as "
    "one bit is x/z; the negated forms invert a known result and keep x. Pinned against Xcelium 24.03.",
    "  assign ro = |v;\n  assign ra = &v;\n  assign rx = ^v;\n  assign rno = ~|v;\n  assign rna = ~&v;\n  assign rnx = ~^v;",
    [('v', 4)], [('ro', 1), ('ra', 1), ('rx', 1), ('rno', 1), ('rna', 1), ('rnx', 1)], stim)

# 10. logical && and || (S2): a deciding operand decides even when the other is x; vector operands use "some definite 1" / "all definite 0"
X4 = ['0', '1', 'x', 'z']
V2L = ['00', '01', '10', '11', '0x', 'x0', '1x', 'x1', 'xx', 'zz']
stim = [dict(a=a, b=b, v='00', w='00') for a in X4 for b in X4]
stim += [dict(a='1', b='1', v=v, w=w) for v in V2L for w in ['00', '01', '1x', '0x', 'xx']]
row('wpg_logic', "WP-G four-state contract (S2): logical `&&` and `||` (1-bit result). `&&` is 0 as soon as one operand is all-zero, 1 when both have a "
    "definite 1 bit, else x; `||` is 1 as soon as one operand has a definite 1 bit, 0 when both are all-zero, else x. Vector operands "
    "(`1x` counts as true, `0x` is unknown) and a negated operand. Pinned against Xcelium 24.03.",
    "  assign la = a && b;\n  assign lo = a || b;\n  assign lva = v && w;\n  assign lvo = v || w;\n  assign lm = a && !b;\n  assign ln = !(a || b);",
    [('a', 1), ('b', 1), ('v', 2), ('w', 2)], [('la', 1), ('lo', 1), ('lva', 1), ('lvo', 1), ('lm', 1), ('ln', 1)], stim)

json.dump(rows, open('cases_wpg.json', 'w'), indent=1)
print(len(rows), "rows,", sum(len(r['stimulus']) for r in rows), "cycles")

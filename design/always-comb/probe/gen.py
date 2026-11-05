#!/usr/bin/env python3
"""Generate the WP-G four-state contract probe: DUT modules + one testbench (xrun, one run)."""
import itertools, json, sys

# Each DUT: name, inputs [(name,width)], outputs [(name,width)], body (module items), stimulus list of dicts of binary strings.
S1 = ['0','1','x','z']

def prod(names, vals):
    return [dict(zip(names, p)) for p in itertools.product(*vals)]

duts = []
def dut(name, ins, outs, body, stim, note=''):
    duts.append(dict(name=name, ins=ins, outs=outs, body=body, stim=stim, note=note))

# --- A. procedural if -------------------------------------------------------------------------
dut('p_if1', [('c',1),('a',1),('b',1)], [('y',1)],
    "always_comb begin if (c) y = a; else y = b; end",
    prod(['c','a','b'], [S1, ['0','1'], ['0','1']]),
    'procedural if, 1-bit condition: c in {0,1,x,z}')
V2 = ['00','01','10','11','0x','x0','1x','x1','xx','zz','0z','1z','xz']
dut('p_if2', [('v',2),('a',1),('b',1)], [('y',1)],
    "always_comb begin if (v) y = a; else y = b; end",
    [dict(v=v,a='1',b='0') for v in V2],
    'procedural if, 2-bit condition (truthiness: some definite 1 bit)')
dut('p_ifnot', [('c',1),('a',1),('b',1)], [('y',1)],
    "always_comb begin if (!c) y = a; else y = b; end",
    prod(['c','a','b'], [S1, ['0','1'], ['0','1']]),
    'if (!c) with c=x: !x = x, so the ELSE branch runs (not the swap of if (c) b else a)')
dut('p_ifnot2', [('c',1),('a',1),('b',1)], [('y',1)],
    "always_comb begin if (c) y = b; else y = a; end",
    prod(['c','a','b'], [S1, ['0','1'], ['0','1']]),
    'the swapped twin of p_ifnot')
dut('p_ifbnot', [('c',1),('a',1),('b',1)], [('y',1)],
    "always_comb begin if (~c) y = a; else y = b; end",
    prod(['c','a','b'], [S1, ['0','1'], ['0','1']]),
    'if (~c): bitwise not of x is x -> else branch')
dut('p_ifchain', [('c1',1),('c2',1),('a',1),('b',1),('d',1)], [('y',1)],
    "always_comb begin if (c1) y = a; else if (c2) y = b; else y = d; end",
    prod(['c1','c2'], [S1, S1]) and [dict(c1=c1,c2=c2,a='1',b='0',d='1') for c1 in S1 for c2 in S1],
    'else-if chain: an x/z first condition falls to the second test')
dut('p_ifnest', [('c',1),('e',1),('a',1),('b',1),('d',1)], [('y',1)],
    "always_comb begin if (c) begin if (e) y = a; else y = b; end else y = d; end",
    [dict(c=c,e=e,a='1',b='0',d='1') for c in S1 for e in S1],
    'nested if/else: x condition in the inner if takes its else')
dut('p_deflt', [('c',1),('a',1)], [('y',1)],
    "always_comb begin y = 1'b0; if (c) y = a; end",
    prod(['c','a'], [S1, ['0','1']]),
    'default then override (no latch): c=x leaves the default')
dut('p_untaken', [('c',1),('a',1),('b',1)], [('y',1)],
    "always_comb begin if (c) y = a; else y = b; end",
    [dict(c='1',a='1',b='x'), dict(c='0',a='x',b='1'), dict(c='1',a='x',b='1'), dict(c='0',a='1',b='z'), dict(c='1',a='z',b='0')],
    'x/z in the UNTAKEN branch does not reach y; in the taken branch it does')
dut('p_order', [('a',1),('b',1),('c',1)], [('y',1),('z',1)],
    "logic t; always_comb begin y = a; y = b; t = a ^ b; z = t & c; end",
    prod(['a','b','c'], [['0','1','x'], ['0','1','x'], ['0','1','x']]),
    'blocking order: the last write wins; a temporary written then read in the same body')
dut('p_two', [('c',1),('a',1),('b',1)], [('y',1),('w',1)],
    "always_comb begin if (c) begin y = a; w = b; end else begin y = b; w = a; end end",
    prod(['c','a','b'], [S1, ['0','1'], ['0','1']]),
    'two targets under one if: x condition takes the else arm for both')
dut('p_cond_vec_unary', [('v',2),('a',1),('b',1)], [('y',1)],
    "always_comb begin if (|v) y = a; else y = b; end",
    [dict(v=v,a='1',b='0') for v in V2],
    'reduction condition |v = the truthiness of v')
dut('p_cond_lnot_vec', [('v',2),('a',1),('b',1)], [('y',1)],
    "always_comb begin if (!v) y = a; else y = b; end",
    [dict(v=v,a='1',b='0') for v in V2],
    'if (!v), v a vector: !2b0x = x -> else; !2b1x = 0 -> else; !2b00 = 1 -> then')

# --- B. conditional expression ?: ----------------------------------------------------------------
dut('e_tern1', [('c',1),('a',1),('b',1)], [('y',1)],
    "assign y = c ? a : b;",
    prod(['c','a','b'], [S1, ['0','1','x','z'], ['0','1','x','z']]),
    '?: scalar: c in {0,1,x,z}, arms in {0,1,x,z}: merge bitwise when c is x/z')
dut('e_tern4', [('c',1),('a',4),('b',4)], [('y',4)],
    "assign y = c ? a : b;",
    [dict(c=c,a=a,b=b) for c in S1 for (a,b) in [('1100','1010'),('1111','1111'),('10x0','1010'),('1z10','1x10'),('0000','0000')]],
    '?: vector arms, 1-bit condition: per-bit merge; equal known bits survive')
dut('e_ternv', [('v',2),('a',4),('b',4)], [('y',4)],
    "assign y = v ? a : b;",
    [dict(v=v,a='1100',b='1010') for v in V2],
    '?: with a 2-bit condition: some 1 bit -> then arm; all 0 -> else arm; otherwise merge')
dut('e_tern_proc', [('c',1),('a',4),('b',4)], [('y',4)],
    "always_comb begin y = c ? a : b; end",
    [dict(c=c,a='1100',b='1010') for c in S1],
    '?: as a procedural right-hand side behaves as the continuous one (merge), unlike the procedural if')
dut('e_ternnest', [('c',1),('d',1),('a',1),('b',1),('e',1)], [('y',1)],
    "assign y = c ? a : (d ? b : e);",
    [dict(c=c,d=d,a='1',b='0',e='1') for c in S1 for d in S1],
    'nested ?: with x conditions')
dut('e_tern_not', [('c',1),('a',1),('b',1)], [('y',1)],
    "assign y = !c ? a : b;",
    prod(['c','a','b'], [S1, ['0','1'], ['0','1']]),
    '!c ? a : b with c=x: !c = x, the merge of a and b (the arms are NOT swapped relative to c ? b : a only when known)')

# --- C. ! versus ~ ---------------------------------------------------------------------------------
dut('u_not1', [('a',1)], [('n1',1),('b1',1),('n4',4),('b4',4)],
    "assign n1 = !a; assign b1 = ~a; assign n4 = !a; assign b4 = ~a;",
    [dict(a=a) for a in S1],
    '1-bit operand: ! is self-determined (1 bit, then zero-extended); ~ is context-determined (extended first)')
dut('u_notv', [('v',2)], [('nl',1),('nb',2),('nl4',4),('nb4',4)],
    "assign nl = !v; assign nb = ~v; assign nl4 = !v; assign nb4 = ~v;",
    [dict(v=v) for v in V2],
    '2-bit operand: ! reduces (some 1 bit -> 0, all known 0 -> 1, else x); ~ is bitwise')
dut('u_notnot', [('v',2)], [('y',1),('z',1)],
    "assign y = !(!v); assign z = !(~v);",
    [dict(v=v) for v in V2],
    '!!v is not the identity on x: and !(~v) differs from v==all ones')

# --- D. fragment-relevant: a rank-ordered carry body -------------------------------------------------
dut('p_carry', [('p',1),('c',1),('a',1)], [('co',1),('s',1)],
    "always_comb begin if (p) co = c; else co = a; s = p ^ c; end",
    prod(['p','c','a'], [S1, S1, ['0','1']]),
    'the carry-select cell: co = p ? c : a as an if, s = p ^ c')

def tb_text():
    out = []
    out.append("`timescale 1ns/1ns")
    for d in duts:
        ports = ", ".join([f"input logic [{w-1}:0] {n}" if w > 1 else f"input logic {n}" for n, w in d['ins']] +
                          [f"output logic [{w-1}:0] {n}" if w > 1 else f"output logic {n}" for n, w in d['outs']])
        out.append(f"// {d['note']}")
        out.append(f"module {d['name']} ({ports});")
        out.append("  " + d['body'])
        out.append("endmodule")
    out.append("module tb;")
    for d in duts:
        for n, w in d['ins']:
            out.append(f"  reg [{w-1}:0] {d['name']}_{n};")
        for n, w in d['outs']:
            out.append(f"  wire [{w-1}:0] {d['name']}_{n};")
        conns = ", ".join([f".{n}({d['name']}_{n})" for n, w in d['ins']] + [f".{n}({d['name']}_{n})" for n, w in d['outs']])
        out.append(f"  {d['name']} u_{d['name']} ({conns});")
    out.append("  initial begin")
    for d in duts:
        out.append(f"    $display(\"DUT {d['name']}\");")
        for k, st in enumerate(d['stim']):
            sets = " ".join([f"{d['name']}_{n} = {w}'b{st[n]};" for n, w in d['ins']])
            shows_in = " ".join([f"{n}=%b" for n, w in d['ins']])
            shows_out = " ".join([f"{n}=%b" for n, w in d['outs']])
            args = ", ".join([f"{d['name']}_{n}" for n, w in d['ins']] + [f"{d['name']}_{n}" for n, w in d['outs']])
            out.append(f"    {sets} #1; $display(\"CYCLE {k} {shows_in} {shows_out}\", {args});")
    out.append("    $finish;")
    out.append("  end")
    out.append("endmodule")
    return "\n".join(out) + "\n"

open('probe.sv', 'w').write(tb_text())
json.dump(duts, open('probe.json', 'w'), indent=1)
print(len(duts), "duts;", sum(len(d['stim']) for d in duts), "cycles")

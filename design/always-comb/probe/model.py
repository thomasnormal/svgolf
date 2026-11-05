#!/usr/bin/env python3
"""Reference of the ls-sv M0 four-state rules, as READ from LeanModels/Sv/Basic.lean (not run in Lean):
  condTrue c   = some bit is a definite 1
  isKnownZero  = every bit is a definite 0
  ternary c a b= a if condTrue c, b if isKnownZero c, else per-bit merge (equal known bits survive, else x)
  lnot c       = 0 if condTrue, 1 if knownZero, else x
  bnot         = per bit: 0<->1, x/z -> x
  The procedural `if (c)`: then-branch iff condTrue c, else the else branch (or nothing).
Strings are MSB-first like the testbench's %b."""
import json, re, sys

def norm(b):  # z behaves as x in every operator
    return 'x' if b in 'xz' else b
def cond_true(s): return '1' in s
def known_zero(s): return all(c == '0' for c in s)
def merge(a, b):
    assert len(a) == len(b)
    return ''.join(x if (x == y and x in '01') else 'x' for x, y in zip(a, b))
def ternary(c, a, b):
    if cond_true(c): return a
    if known_zero(c): return b
    return merge(a, b)
def lnot(c): return '0' if cond_true(c) else ('1' if known_zero(c) else 'x')
def bnot(s): return ''.join({'0': '1', '1': '0'}.get(ch, 'x') for ch in s)
def red_or(s):
    if '1' in s: return '1'
    if all(ch == '0' for ch in s): return '0'
    return 'x'
def red_and(s):
    if '0' in s: return '0'
    if all(ch == '1' for ch in s): return '1'
    return 'x'
def red_xor(s):
    if any(ch not in '01' for ch in s): return 'x'
    return str(s.count('1') % 2)
def land(a, b):
    if known_zero(a) or known_zero(b): return '0'
    if cond_true(a) and cond_true(b): return '1'
    return 'x'
def lor(a, b):
    if cond_true(a) or cond_true(b): return '1'
    if known_zero(a) and known_zero(b): return '0'
    return 'x'
def band(a, b):
    if a == '0' or b == '0': return '0'
    if a == '1' and b == '1': return '1'
    return 'x'
def bxor(a, b):
    if a in '01' and b in '01': return str(int(a) ^ int(b))
    return 'x'
def zext(s, w): return s.rjust(w, '0')
def trunc(s, w): return s[-w:]

def run(name, st):
    g = lambda k: st[k]
    if name == 'p_if1': return dict(y=g('a') if cond_true(g('c')) else g('b'))
    if name == 'p_if2': return dict(y=g('a') if cond_true(g('v')) else g('b'))
    if name == 'p_ifnot': return dict(y=g('a') if cond_true(lnot(g('c'))) else g('b'))
    if name == 'p_ifnot2': return dict(y=g('b') if cond_true(g('c')) else g('a'))
    if name == 'p_ifbnot': return dict(y=g('a') if cond_true(bnot(g('c'))) else g('b'))
    if name == 'p_ifchain': return dict(y=g('a') if cond_true(g('c1')) else (g('b') if cond_true(g('c2')) else g('d')))
    if name == 'p_ifnest': return dict(y=(g('a') if cond_true(g('e')) else g('b')) if cond_true(g('c')) else g('d'))
    if name == 'p_deflt': return dict(y=g('a') if cond_true(g('c')) else '0')
    if name == 'p_untaken': return dict(y=g('a') if cond_true(g('c')) else g('b'))
    if name == 'p_order':
        t = bxor(g('a'), g('b')); return dict(y=g('b'), z=band(t, g('c')))
    if name == 'p_two':
        return dict(y=g('a') if cond_true(g('c')) else g('b'), w=g('b') if cond_true(g('c')) else g('a'))
    if name == 'p_cond_vec_unary': return dict(y=g('a') if cond_true(red_or(g('v'))) else g('b'))
    if name == 'p_cond_lnot_vec': return dict(y=g('a') if cond_true(lnot(g('v'))) else g('b'))
    if name == 'e_tern1': return dict(y=ternary(g('c'), g('a'), g('b')))
    if name == 'e_tern4': return dict(y=ternary(g('c'), g('a'), g('b')))
    if name == 'e_ternv': return dict(y=ternary(g('v'), g('a'), g('b')))
    if name == 'e_tern_proc': return dict(y=ternary(g('c'), g('a'), g('b')))
    if name == 'e_ternnest': return dict(y=ternary(g('c'), g('a'), ternary(g('d'), g('b'), g('e'))))
    if name == 'e_tern_not': return dict(y=ternary(lnot(g('c')), g('a'), g('b')))
    if name == 'u_not1':
        a = g('a'); n = lnot(a)
        return dict(n1=n, b1=bnot(a), n4=zext(n, 4), b4=bnot(zext(a, 4)))
    if name == 'u_notv':
        v = g('v'); n = lnot(v)
        return dict(nl=n, nb=bnot(v), nl4=zext(n, 4), nb4=bnot(zext(v, 4)))
    if name == 'u_notnot':
        v = g('v'); return dict(y=lnot(lnot(v)), z=lnot(bnot(v)))
    if name == 'p_local':
        t = bxor(g('a'), g('b')); return dict(y=band(t, g('c')))
    if name == 'p_rowwrite': return dict(y=g('a') if cond_true(g('c')) else g('b'))
    if name == 'p_widthext': return dict(y=zext(g('a'), 4) if cond_true(g('c')) else '1111')
    if name == 'p_tern_ctx': return dict(y=ternary(g('c'), bnot(zext(g('a'), 4)), '0000'))
    if name == 'p_carry':
        return dict(co=g('c') if cond_true(g('p')) else g('a'), s=bxor(g('p'), g('c')))
    raise KeyError(name)

def run_partial(rows):
    # per-bit latch: each bit keeps its value on the path that does not write it (x at time 0)
    y = ['x', 'x']   # y[1], y[0] MSB first
    outs = []
    for st in rows:
        if cond_true(st['c']): y[1] = st['a']      # bit 0 (LSB, last in the MSB-first list)
        else: y[0] = st['b']                       # bit 1
        outs.append(dict(y=''.join(y)))
    return outs

def parse(out):
    cur = None; res = {}
    for line in out.splitlines():
        m = re.match(r'DUT (\S+)', line)
        if m: cur = m.group(1); res[cur] = []; continue
        m = re.match(r'CYCLE (\d+) (.*)', line)
        if m and cur:
            kv = dict(p.split('=') for p in m.group(2).split())
            res[cur].append(kv)
    return res

if __name__ == '__main__':
    duts = {d['name']: d for f in ('probe.json', 'probe2.json') for d in json.load(open(f))}
    res = parse(open(sys.argv[1]).read())
    bad = 0; tot = 0
    for name, rows in res.items():
        if name == 'p_partial':
            exps = run_partial([{n: kv[n] for n, w in duts[name]['ins']} for kv in rows])
            for k, (kv, e) in enumerate(zip(rows, exps)):
                tot += 1
                if e['y'] != kv['y']:
                    bad += 1; print(f"MISMATCH {name} #{k}: xcelium={kv['y']} model={e['y']}")
            continue
        for k, kv in enumerate(rows):
            st = {n: kv[n] for n, w in duts[name]['ins']}
            outs = [n for n, w in duts[name]['outs']]
            exp = run(name, st)
            tot += 1
            for o in outs:
                if exp[o] != kv[o]:
                    bad += 1
                    print(f"MISMATCH {name} #{k} in={st} out {o}: xcelium={kv[o]} model={exp[o]}")
    print(f"{tot} rows, {bad} output mismatches")

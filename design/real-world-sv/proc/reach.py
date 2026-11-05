#!/usr/bin/env python3
"""WP-PROC G0: upper-bound reach of the planned lowerings on three populations (no Lean, no pyslang needed).

  survey real files : survey_files.json  (216 self-contained files of the real-world survey: per file the Unsupported kinds
                      of its extractor envelope + counts of LocalDecl and `packed: null` declarations) + scan_survey.json
                      (pyslang statement census of every procedural block / subroutine, scan_proc.py)
  probes            : probe_scan.json    (the 241 reduced probes: same two measurements, reach_probes.py)
  RB0               : ../rb0/census.json (79 as-is CPU blocks, blocker sets by register row)

A population member is accepted at tier T iff every Unsupported kind is covered by T, every loader-refused node is covered and
(from the local-declaration tier on) every comb-style block / function passes the admission predicate (section 4.1 of PROC-NOTE.md).
These are UPPER bounds: obstacles hidden inside Unsupported text are not seen.

    python3 reach.py            # prints the three tables of PROC-NOTE.md section 2
"""
import json, os, collections
H = os.path.dirname(os.path.abspath(__file__))
NETS = {'PortSymbol:net-z', 'NetSymbol:net-z'}
EVT = {'TimedStatement:ImplicitEventControl', 'TimedStatement:EventListControl', 'SignalEventControl:None_'}
LOOPF = {'ForLoopStatement', 'SubroutineSymbol:Subroutine', 'CallExpression', 'ExpressionStatement:CallExpression'}
TIERS = [('T0 today', set(), False, False, False), ('T1 nets/typeless dims', NETS, True, False, False),
         ('T2 +always @*/level lists', NETS | EVT, True, False, False), ('T3 +local decls', NETS | EVT, True, True, False),
         ('T4 +loops/functions', NETS | EVT | LOOPF, True, True, True)]
COMB = {'AlwaysComb', 'always@ImplicitEventControl', 'gen:AlwaysComb', 'function'}
BADSTMT = ['stmt:WhileLoopStatement', 'stmt:RepeatLoopStatement', 'stmt:ForeverLoopStatement', 'stmt:ForeachLoopStatement',
           'stmt:BreakStatement', 'stmt:ContinueStatement', 'stmt:TimedStatement', 'stmt:ImmediateAssertionStatement',
           'stmt:InvalidStatement', 'assign:nba', 'lhs:ConcatenationExpression', 'lhs:MemberAccessExpression']

def adm_loop(sh):
    return (sh['start'] in ('literal', 'param') and sh['bound'] in ('literal', 'param')
            and sh['cond'] in ('LessThan', 'LessThanEqual', 'NotEqual', 'GreaterThan', 'GreaterThanEqual')
            and sh['step'] in ('inc', 'dec'))

def block_ok(b, in_function):
    c = b['counts']
    if any(c.get(k) for k in BADSTMT): return False
    if c.get('stmt:ReturnStatement') and not in_function: return False
    return all(n[0] != 'for' or adm_loop(n[1]) for n in b['notes'])

def census_ok(scan):
    if scan is None: return False
    for b in scan['blocks']:
        if b['style'] in COMB and not block_ok(b, False): return False
        if b['counts'].get('stmt:ForLoopStatement') and b['style'] not in COMB: return False
    return all(block_ok(s, True) for s in scan['subs'])

def accept(kinds, loc, packed, scan, tier):
    _, allowed, nets, local, loopf = tier
    if not kinds <= allowed: return False
    if packed and not nets: return False
    if loc and not local: return False
    if (loopf or local or EVT <= allowed) and not census_ok(scan): return False
    return True

def table(name, rows):
    print('\n== %s (%d)' % (name, len(rows)))
    for t in TIERS:
        by = collections.Counter(); n = 0
        for topic, kinds, loc, packed, scan in rows:
            if accept(kinds, loc, packed, scan, t): n += 1; by[topic] += 1
        print('%-28s %3d  %s' % (t[0], n, dict(by)))

def main():
    survey = json.load(open(H + '/survey_files.json'))
    scan = {(x['topic'], x['file']): x for x in json.load(open(H + '/scan_survey.json')) if 'error' not in x}
    table('survey real files', [(r['topic'], set(r['unsupported']), r['localdecl'], r['packednull'], scan.get((r['topic'], r['file'])))
                                for r in survey])
    pr = json.load(open(H + '/probe_scan.json'))
    rows = [('probe', set(d[0]), d[1]['localdecl'], d[1]['packednull'], d[2]) for fn, d, st in pr if d]
    table('survey probes (extractor level; triage of the flips is in the note)', rows)
    rb0 = json.load(open(H + '/../rb0/census.json'))
    asis = [b for b in rb0['blocks'] if b['variant'] == 'as-is' and b['status'] != 'CORPUS-BLOCKED']
    keys = lambda b: {x['key'] for x in b['blockers']}
    clean = sum(1 for b in asis if not keys(b))
    N = {'ld-init-expr', 'dc-net-z'}
    steps = [('T1 nets/typeless dims', N), ('+ x:top-instantiated (topModules)', N | {'x:top-instantiated'}),
             ('T2 +pr-implicit-event', N | {'x:top-instantiated', 'pr-implicit-event'}),
             ('T3 +ld-localdecl/le-generate-decl', N | {'x:top-instantiated', 'pr-implicit-event', 'ld-localdecl', 'le-generate-decl'}),
             ('T4 +st-for/st-compound/ex-user-call/dc-member-kinds',
              N | {'x:top-instantiated', 'pr-implicit-event', 'ld-localdecl', 'le-generate-decl', 'st-for', 'st-compound',
                   'ex-user-call', 'dc-member-kinds', 'sy-user-task-call'})]
    print('\n== RB0 CPU blocks (%d as-is rows not corpus-blocked; %d already blocker-free)' % (len(asis), clean))
    for name, S in steps:
        f = sum(1 for b in asis if keys(b) and keys(b) <= S)
        print('%-52s freed %2d  blocker-free in all %2d' % (name, f, f + clean))

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""mk_results.py WORKDIR: collect what `check.py --unproved --tactics` and the tactic probes answered on proc/lowered/*.sv
into results.md. WORKDIR holds res/<name>.json (check.py --json output) and dumps/<name>.out (lake env lean on Probe_*.lean)."""
import json, os, sys, glob
W = sys.argv[1] if len(sys.argv) > 1 else '.'
H = os.path.dirname(os.path.abspath(__file__))
rows = []
for f in sorted(glob.glob(W + '/res/v*.json') + glob.glob(W + '/res/s[0-9]*.json') + glob.glob(W + '/res/t[0-9]*.json')):
    b = os.path.basename(f)[:-5]
    try:
        j = json.load(open(f))
    except Exception:
        rows.append((b, 'no result', '', '')); continue
    stage = j.get('stage'); tac = j.get('tactics') or {}
    err = ' '.join(str(e) for e in (j.get('errors') or j.get('notes') or []))[:240].replace('\n', ' ')   # a clean --unproved run: its note
    rows.append((b, stage, str(tac.get('in_fragment')), (tac.get('message') or err)[:400].replace('\n', ' ').replace('|', '/')))
out = ['# Hand-lowered shapes through the pipeline (`check.py --unproved --tactics`)', '',
       '| design | stage reached | in tactic fragment | first message |', '|---|---|---|---|']
out += ['| %s | %s | %s | %s |' % r for r in rows]
for f in sorted(glob.glob(W + '/dumps/*.out')):
    out += ['', '## ' + os.path.basename(f), '', '```', open(f).read()[:6000].rstrip(), '```']
open(H + '/results.md', 'w').write('\n'.join(out) + '\n')
print('wrote', H + '/results.md', len(rows), 'designs')

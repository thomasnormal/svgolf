#!/usr/bin/env python3.12
"""Build the Verilator model of a design `fdiv #(W, P)` (default: the reference) at (W, P), run it exhaustively (K <= 14) or sampled; print one JSON line.
usage: run_v.py W P [--sv FILE] [--samples N] [--jobs J] [--work DIR]"""
import argparse, json, os, subprocess, sys, shutil
ap = argparse.ArgumentParser()
ap.add_argument('W', type=int); ap.add_argument('P', type=int)
ap.add_argument('--sv', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tasks', 'fdivp', 'reference', 'fdivp.sv')); ap.add_argument('--samples', type=int, default=0)
ap.add_argument('--jobs', type=int, default=1); ap.add_argument('--work', default=os.path.join(__import__('tempfile').gettempdir(), 'svgolf-fdivp-validate')); ap.add_argument('--seed', type=int, default=1)
a = ap.parse_args()
HERE = os.path.dirname(os.path.abspath(__file__))
W, P = a.W, a.P
d = os.path.join(os.path.abspath(a.work), f'{W}_{P}')
shutil.rmtree(d, ignore_errors=True); os.makedirs(d)
sv = os.path.abspath(a.sv)
cmd = ['verilator', '--cc', '--exe', '--build', '-O3', '-Wno-fatal', '-Wno-lint', '--top-module', 'fdiv', f'-GW={W}', f'-GP={P}',
       '-CFLAGS', f'-O2 -std=c++17 -DWW={W} -DPP={P} -I{HERE}', '-Mdir', os.path.join(d, 'obj'), '-o', 'vfdiv', '-j', '2', sv,
       os.path.join(HERE, 'tb_fdivp.cpp')]
r = subprocess.run(cmd, cwd=d, capture_output=True, text=True)
if r.returncode:
    print(json.dumps({'W': W, 'P': P, 'build_error': (r.stdout + r.stderr)[-1500:]})); sys.exit(2)
exe = os.path.join(d, 'obj', 'vfdiv')
K = W + P
res = []
if a.samples:
    p = subprocess.run([exe, '0', '0', str(a.samples), str(a.seed)], capture_output=True, text=True)
    res.append(json.loads(p.stdout.strip().splitlines()[-1])); 
    if p.returncode: print(p.stderr[:600], file=sys.stderr)
else:
    n = 1 << K; j = a.jobs
    procs = [subprocess.Popen([exe, str(i * n // j), str((i + 1) * n // j)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) for i in range(j)]
    for pr in procs:
        o, e = pr.communicate()
        res.append(json.loads(o.strip().splitlines()[-1]))
        if pr.returncode: print(e[:600], file=sys.stderr)
print(json.dumps({'W': W, 'P': P, 'K': K, 'pairs': sum(x['pairs'] for x in res), 'mismatches': sum(x['mismatches'] for x in res), 'mode': 'sampled' if a.samples else 'exhaustive'}))
shutil.rmtree(os.path.join(d, 'obj'), ignore_errors=True)

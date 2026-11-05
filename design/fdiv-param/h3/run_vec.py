#!/usr/bin/env python3.12
"""usage: run_vec.py W P N SEED [--sv FILE] : generate vectors, build the Verilator model, run."""
import subprocess, sys, os, json, shutil, argparse
ap = argparse.ArgumentParser(); ap.add_argument('W', type=int); ap.add_argument('P', type=int); ap.add_argument('N', type=int); ap.add_argument('SEED', type=int)
ap.add_argument('--sv', default='fdivp.sv'); ap.add_argument('--model', action='store_true'); ap.add_argument('--model3', action='store_true')
a = ap.parse_args()
H = os.path.dirname(os.path.abspath(__file__))
d = os.path.abspath(f'build/vec_{a.W}_{a.P}'); shutil.rmtree(d, ignore_errors=True); os.makedirs(d)
vec = os.path.join(d, 'vec.bin')
r = subprocess.run([sys.executable, os.path.join(H, 'gen_vec.py'), str(a.W), str(a.P), str(a.N), str(a.SEED), vec] + (['--model'] if a.model else []) + (['--model3'] if a.model3 else []), capture_output=True, text=True, cwd=H)
print(r.stdout.strip(), r.stderr[-300:])
cmd = ['verilator', '--cc', '--exe', '--build', '-O3', '-Wno-fatal', '-Wno-lint', '--top-module', 'fdiv', f'-GW={a.W}', f'-GP={a.P}', '-CFLAGS', f'-O2 -std=c++17', '-Mdir', os.path.join(d, 'obj'), '-o', 'vfdiv', '-j', '2', os.path.abspath(a.sv), os.path.join(H, 'tb_vec.cpp')]
b = subprocess.run(cmd, cwd=d, capture_output=True, text=True)
if b.returncode: print('BUILD ERROR', (b.stdout + b.stderr)[-800:]); sys.exit(2)
p = subprocess.run([os.path.join(d, 'obj', 'vfdiv'), vec], capture_output=True, text=True)
print(f'({a.W},{a.P}) verilator:', p.stdout.strip(), p.stderr[:400].strip())
shutil.rmtree(d, ignore_errors=True)

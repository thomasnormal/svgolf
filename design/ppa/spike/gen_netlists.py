#!/usr/bin/env python3.12
"""Step 1 of the spike: the pinned svGolf flow (score/score.py) on every design,
keeping the SCORED gate netlist and the score JSON.

  python3.12 gen_netlists.py [--n 16] [--only NAME ...]

Writes data/netlists/<name>_N<n>.v and data/netlists/<name>_N<n>.score.json
(area_ge, depth, gates, rtlil_sha256 ...). Designs whose source is a flat
netlist for one width (dadda_*) exist only at the widths of tests/mul/baselines.
"""
import argparse, json, os, subprocess, sys, time
from designs import SVGOLF, HERE, designs

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args()
    out = os.path.join(HERE, "data", "netlists")
    os.makedirs(out, exist_ok=True)
    for d in designs():
        if a.only and d["name"] not in a.only:
            continue
        src = os.path.join(SVGOLF, d["src"].format(N=a.n))
        if not os.path.exists(src):
            print(f"skip {d['name']} N={a.n}: {src} missing")
            continue
        tag = f"{d['name']}_N{a.n}"
        nl = os.path.join(out, tag + ".v")
        js = os.path.join(out, tag + ".score.json")
        cmd = [sys.executable if sys.version_info[:2] == (3, 12) else "python3.12",
               os.path.join(SVGOLF, "score", "score.py"), src, "--top", d["top"],
               "--param", f"N={a.n}", "--netlist", nl, "--json", js]
        t = time.time()
        r = subprocess.run(cmd, capture_output=True, text=True)
        dt = time.time() - t
        if r.returncode != 0:
            print(f"FAIL {tag}: {r.stdout[-400:]} {r.stderr[-400:]}")
            continue
        s = json.load(open(js))
        print(f"{tag:24s} area {s['area_ge']:9.3f} GE  depth {s['depth']:3d}  gates {s['num_gates']:5d}  {dt:5.1f}s")

if __name__ == "__main__":
    main()

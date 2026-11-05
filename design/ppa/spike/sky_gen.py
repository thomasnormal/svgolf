#!/usr/bin/env python3.12
"""Step 1 (WP-X1): the PINNED svGolf flow (score/score.py, unchanged) on every design of the sky130 study:
keeps the canonical RTLIL (input of every mapping flow), the SCORED gate netlist (input of flow A0') and the
score JSON (area_ge, depth ...), and the wall time of the pinned flow.

  python3.12 sky_gen.py [--n 16] [--only NAME ...]      # -> .cache/sky130/{rtlil,netlists}/, data/sky130/pinned_N16.json
"""
import argparse, json, os, subprocess, sys, time
import sky130_designs as SD

def run(d, outdir, py="python3.12"):
    tag = d["tag"]
    nl = os.path.join(outdir, "netlists", tag + ".v")
    il = os.path.join(outdir, "rtlil", tag + ".il")
    js = os.path.join(outdir, "netlists", tag + ".score.json")
    for p in (nl, il):
        os.makedirs(os.path.dirname(p), exist_ok=True)
    cmd = [py, os.path.join(SD.D.SVGOLF, "score", "score.py"), d["src"], "--top", d["top"],
           "--netlist", nl, "--rtlil", il, "--json", js]
    for k, v in d["params"].items():
        cmd += ["--param", f"{k}={v}"]
    t = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    dt = time.time() - t
    if r.returncode != 0:
        raise SystemExit(f"FAIL {tag}: {r.stdout[-600:]} {r.stderr[-600:]}")
    s = json.load(open(js))
    return dict(name=d["name"], tag=tag, area_ge=s["area_ge"], area_mge=s["area_mge"], depth=s["depth"],
                gates=s["gates"], num_gates=s["num_gates"], rtlil_sha256=s["rtlil_sha256"],
                script_sha256=s["script_sha256"], canon_script_sha256=s["canon_script_sha256"],
                ge_table_sha256=s["ge_table_sha256"], yosys_version=s["yosys_version"], seconds=round(dt, 2))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args()
    rows = []
    for d in SD.all_designs(a.n):
        if a.only and d["name"] not in a.only:
            continue
        r = run(d, SD.CACHE)
        rows.append(r)
        print(f"{d['tag']:20s} {r['area_ge']:9.3f} GE depth {r['depth']:3d} gates {r['num_gates']:5d} {r['seconds']:6.1f}s", flush=True)
    os.makedirs(SD.DATA, exist_ok=True)
    with open(os.path.join(SD.DATA, f"pinned_N{a.n}.json"), "w") as fh:
        json.dump({"rows": rows}, fh, indent=1, sort_keys=True)

if __name__ == "__main__":
    main()

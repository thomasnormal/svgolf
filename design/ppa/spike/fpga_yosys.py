#!/usr/bin/env python3.12
"""Flow C (Yosys half): LUT count and LUT levels of the same canonical RTLIL on
FPGA-style mappings, using only the installed Yosys 0.53 (no place and route, so
no fmax and no routing delay).

  python3.12 fpga_yosys.py --n 16     # -> data/fpga_N16.json

Per design:
  lutK   `synth -flatten; abc -lut K; ltp -noff`: K-input LUT count and LUT levels
         (K = 4: iCE40 / ECP5 / Cyclone-class, K = 6: Xilinx 7-series / Ultrascale)
  ice40  `synth_ice40`: SB_LUT4 / SB_CARRY counts (target-specific carry logic and
         techmap, abc with `-dff` off)
  xc7    `synth_xilinx -family xc7 -flatten`: LUT1..6 / MUXF counts
"""
import argparse, json, os, re, subprocess, sys, tempfile

from designs import SVGOLF, HERE, designs
import flow_a


def run(script):
    with tempfile.NamedTemporaryFile("w", suffix=".ys", delete=False) as fh:
        fh.write(script)
        ys = fh.name
    try:
        r = subprocess.run(["yosys", "-q", "-s", ys, "-l", ys + ".log"], capture_output=True, text=True, timeout=1800)
        log = open(ys + ".log").read()
        if r.returncode != 0:
            raise RuntimeError(r.stderr[-1500:])
        return log
    finally:
        for p in (ys, ys + ".log"):
            if os.path.exists(p):
                os.unlink(p)


def stat_cells(log):
    m = list(re.finditer(r"Number of cells:\s+(\d+)\n((?:\s+\S+\s+\d+\n)+)", log))
    cells = {}
    if m:
        for line in m[-1].group(2).splitlines():
            k, v = line.split()
            cells[k] = int(v)
    return cells


def ltp(log):
    m = re.search(r"Longest topological path in \S+ \(length=(\d+)\)", log)
    return int(m.group(1)) if m else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    a = ap.parse_args()
    rows = []
    for d in designs():
        src = os.path.join(SVGOLF, d["src"].format(N=a.n))
        if not os.path.exists(src):
            continue
        tag = f"{d['name']}_N{a.n}"
        rt = os.path.join(HERE, ".cache", "rtlil", tag + ".il")
        flow_a.canon_rtlil(src, d["top"], a.n, rt)
        row = {"name": d["name"]}
        for K in (4, 6):
            log = run(f"read_rtlil {rt}\nsynth -flatten -top {d['top']}\nabc -lut {K}\nopt_clean\nstat\nltp -noff\n")
            c = stat_cells(log)
            row[f"lut{K}"] = sum(v for k, v in c.items() if k.startswith("$lut"))
            row[f"lut{K}_levels"] = ltp(log)
        log = run(f"read_rtlil {rt}\nsynth_ice40 -top {d['top']}\nstat\n")
        c = stat_cells(log)
        row["ice40_lut4"] = c.get("SB_LUT4", 0)
        row["ice40_carry"] = c.get("SB_CARRY", 0)
        log = run(f"read_rtlil {rt}\nsynth_xilinx -family xc7 -top {d['top']} -flatten\nstat\n")
        c = stat_cells(log)
        row["xc7_lut"] = sum(v for k, v in c.items() if re.fullmatch(r"LUT[1-6]", k))
        row["xc7_muxf"] = sum(v for k, v in c.items() if k.startswith("MUXF"))
        row["xc7_carry"] = c.get("CARRY4", 0)
        rows.append(row)
        print(row, flush=True)
    with open(os.path.join(HERE, "data", f"fpga_N{a.n}.json"), "w") as fh:
        json.dump(rows, fh, indent=1, sort_keys=True)


if __name__ == "__main__":
    main()

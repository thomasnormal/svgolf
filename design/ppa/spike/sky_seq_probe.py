#!/usr/bin/env python3.12
"""Which sky130 flip-flops does Yosys 0.53's dfflibmap choose, and what does each register style cost? (WP-X1 item 6)
seq_probe.sv has 4-bit registers of every style (plain, async reset, async set, sync reset, enable) and one 1-bit set+reset
flop. The cell policy's dont_use list is applied, with the sequential classes re-enabled except scan flops / latches.
  python3.12 sky_seq_probe.py        -> prints the dfflibmap decisions and the cell histogram and area"""
import os, re, subprocess, tempfile
import fetch_sky130 as F, sky130 as S, sky130_designs as SD

HERE = os.path.dirname(os.path.abspath(__file__))
lib = F.lib_path()
logic_dont = " ".join(f"-dont_use {p}" for p in S.DONT_USE if not p.endswith(("df*", "sdf*", "edf*", "sedf*")))
ff_dont = f"-dont_use {S.PREFIX}lpflow_* -dont_use {S.PREFIX}sdf* -dont_use {S.PREFIX}sedf* -dont_use {S.PREFIX}dl*"
with tempfile.TemporaryDirectory() as d:
    open(os.path.join(d, "t.ys"), "w").write(f"""read_verilog -sv {HERE}/seq_probe.sv
synth -flatten -top seqt
dfflibmap -liberty {lib} {ff_dont}
abc -liberty {lib} {logic_dont}
opt_clean -purge
tee -o {d}/stat.txt stat -liberty {lib}
""")
    r = subprocess.run(["yosys", "-q", "-l", os.path.join(d, "t.log"), os.path.join(d, "t.ys")], capture_output=True, text=True, cwd=d)
    log = open(os.path.join(d, "t.log")).read()
    for ln in log.splitlines():
        if "is a direct match" in ln:
            print(ln.strip())
    st = open(os.path.join(d, "stat.txt")).read()
    for ln in st.splitlines():
        if "sky130" in ln or "Chip area" in ln:
            print(ln)

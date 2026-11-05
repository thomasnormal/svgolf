import json, sys, re, subprocess, os
sys.path.insert(0, '../probe')
from model import *

cases = json.load(open('cases_wpg.json'))
# widths per signal from the .sv headers
def ports(name):
    src = open(f"{name}/{name}.sv").read()
    ins, outs = [], []
    for m in re.finditer(r'(input|output)\s+logic\s*(\[(\d+):0\])?\s*(\w+)', src):
        w = int(m.group(3)) + 1 if m.group(3) else 1
        (ins if m.group(1) == 'input' else outs).append((m.group(4), w))
    return ins, outs

tb = ["`timescale 1ns/1ns"]
for c in cases:
    tb.append(open(f"{c['name']}/{c['name']}.sv").read())
tb.append("module tb;")
for c in cases:
    n = c['name']; ins, outs = ports(n)
    for p, w in ins + outs:
        tb.append(f"  {'reg' if (p,w) in ins else 'wire'} [{w-1}:0] {n}_{p};")
    tb.append(f"  {n} u_{n} (" + ", ".join(f".{p}({n}_{p})" for p, w in ins + outs) + ");")
tb.append("  initial begin")
for c in cases:
    n = c['name']; ins, outs = ports(n)
    tb.append(f'    $display("DUT {n}");')
    for k, st in enumerate(c['stimulus']):
        tb.append("    " + " ".join(f"{n}_{p} = {w}'b{st[p]};" for p, w in ins) + " #1; $display(\"CYCLE %d " % k +
                  " ".join(f"{p}=%b" for p, w in ins + outs) + '", ' + ", ".join(f"{n}_{p}" for p, w in ins + outs) + ");")
tb.append("    $finish;\n  end\nendmodule")
open('rows_tb.sv', 'w').write("\n".join(tb) + "\n")
print("tb written")

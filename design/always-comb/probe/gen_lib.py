#!/usr/bin/env python3
"""Generate the WP-G four-state contract probe: DUT modules + one testbench (xrun, one run)."""
import itertools, json, sys

# Each DUT: name, inputs [(name,width)], outputs [(name,width)], body (module items), stimulus list of dicts of binary strings.
S1 = ['0','1','x','z']

def prod(names, vals):
    return [dict(zip(names, p)) for p in itertools.product(*vals)]

duts = []
def dut(name, ins, outs, body, stim, note=''):
    duts.append(dict(name=name, ins=ins, outs=outs, body=body, stim=stim, note=note))


def tb_text():
    out = []
    out.append("`timescale 1ns/1ns")
    for d in duts:
        ports = ", ".join([f"input logic [{w-1}:0] {n}" if w > 1 else f"input logic {n}" for n, w in d['ins']] +
                          [f"output logic [{w-1}:0] {n}" if w > 1 else f"output logic {n}" for n, w in d['outs']])
        out.append(f"// {d['note']}")
        out.append(f"module {d['name']} ({ports});")
        out.append("  " + d['body'])
        out.append("endmodule")
    out.append("module tb;")
    for d in duts:
        for n, w in d['ins']:
            out.append(f"  reg [{w-1}:0] {d['name']}_{n};")
        for n, w in d['outs']:
            out.append(f"  wire [{w-1}:0] {d['name']}_{n};")
        conns = ", ".join([f".{n}({d['name']}_{n})" for n, w in d['ins']] + [f".{n}({d['name']}_{n})" for n, w in d['outs']])
        out.append(f"  {d['name']} u_{d['name']} ({conns});")
    out.append("  initial begin")
    for d in duts:
        out.append(f"    $display(\"DUT {d['name']}\");")
        for k, st in enumerate(d['stim']):
            sets = " ".join([f"{d['name']}_{n} = {w}'b{st[n]};" for n, w in d['ins']])
            shows_in = " ".join([f"{n}=%b" for n, w in d['ins']])
            shows_out = " ".join([f"{n}=%b" for n, w in d['outs']])
            args = ", ".join([f"{d['name']}_{n}" for n, w in d['ins']] + [f"{d['name']}_{n}" for n, w in d['outs']])
            out.append(f"    {sets} #1; $display(\"CYCLE {k} {shows_in} {shows_out}\", {args});")
    out.append("    $finish;")
    out.append("  end")
    out.append("endmodule")
    return "\n".join(out) + "\n"





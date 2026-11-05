#!/usr/bin/env python3.12
"""X10, synthesis agreement (ARCH-NOTE §7 X10, §4.5 `Admissible`; EXECUTION-PLAN WS4 Days 4-5).

    python3.12 -I x10_split.py --repo REPO --out OUT_DIR [--only NAME,..]        # tools: slang, Icarus, Verilator, Yosys
    (then, under the Lean slot, the model column:)
    $SLOT bash OUT_DIR/lean_batch.sh > OUT_DIR/lean.out
    python3.12 -I x10_split.py --repo REPO --out OUT_DIR --collect             # -> x10.json

Fixtures: the construct classes ARCH-NOTE names for `Admissible` (unique/unique0/priority on case and if, a self-reading
always_comb, synthesis attributes) plus x-as-don't-care, each written so that some stimulus cycles VIOLATE the construct's
claim (no item matches, two items match, the block reads a value it writes, a read during a write) and others do not.
Every fixture is in this file (no third-party text); the self-read rows are the repository's own
`Examples/system-verilog/sem2/rbw_*`.

Columns (one canonical trace per tool, `CYCLE <k> <signal>=<bits>` from harness/sv/gen_tb2.py's cycle testbench, the one
the Xcelium pins use):
  slang       pyslang 11: errors and warnings (codes)
  icarus      the RTL in Icarus 12 (event-driven, 4-state)
  verilator   the RTL in Verilator 5.042 (2-state: x/z stimulus digits become 0)
  yosys       the PINNED scoring flow (svgolf/score/score.py --no-gate: canon.ys + svgolf.ys, Yosys 0.53 + ABC) -> its
              netlist simulated in Icarus with simcells.v
  model       ls-sv: the extractor's Unsupported kinds, then run2 (harness/sv/runner2.lean) through the Lean slot
Xcelium is not run here: no `harness/sv/xcelium_golden.json` row covers these fixtures; the report lists the rows to pin.

Every Yosys run starts in its own process group under `timeout -s KILL`, and the group is killed and checked empty
afterwards (no `yosys-abc` survives: the 2026-11-01 orphan incident).
"""
import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

FIX = {}


def fx(name, top, sv, ports, signals, stim, note, clock=None, violating=None):
    FIX[name] = {"top": top, "sv": sv, "ports": ports, "signals": signals, "stimulus": stim, "note": note,
                 "clock": clock, "violating": violating or []}


S4 = [{"s": "00", "d": "0101"}, {"s": "01", "d": "0101"}, {"s": "10", "d": "0100"}, {"s": "11", "d": "1011"},
      {"s": "11", "d": "0100"}, {"s": "10", "d": "1011"}, {"s": "x1", "d": "1111"}, {"s": "01", "d": "1010"},
      {"s": "11", "d": "0110"}, {"s": "11", "d": "1001"}, {"s": "00", "d": "1111"}]


def viol(pred):
    """Violating cycles of S4: the selector has an x/z digit, or pred(s) holds."""
    return [k for k, e in enumerate(S4) if any(c in "xz" for c in e["s"]) or pred(e["s"])]
P_SD = [("s", "in", 2), ("d", "in", 4), ("y", "out", 1)]

fx("uq_case_nomatch", "uq_case_nomatch", r'''
module uq_case_nomatch (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    y = 1'b0;
    unique case (s)
      2'd0: y = d[0];
      2'd1: y = d[1];
      2'd2: y = d[2];
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "unique case, no default, s = 3 matches no item (a preceding default assignment: no latch)",
   violating=viol(lambda s: s == "11"))

fx("uq_case_nomatch_hold", "uq_case_nomatch_hold", r'''
module uq_case_nomatch_hold (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    unique case (s)
      2'd0: y = d[0];
      2'd1: y = d[1];
      2'd2: y = d[2];
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "unique case, no default and no preceding assignment: s = 3 holds y in simulation",
   violating=viol(lambda s: s == "11"))

fx("pr_case_nomatch", "pr_case_nomatch", r'''
module pr_case_nomatch (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    y = 1'b0;
    priority case (s)
      2'd0: y = d[0];
      2'd1: y = d[1];
      2'd2: y = d[2];
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "priority case, s = 3 matches no item", violating=viol(lambda s: s == "11"))

fx("uq_case_overlap", "uq_case_overlap", r'''
module uq_case_overlap (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    y = 1'b0;
    unique case (1'b1)
      s[0]: y = d[0];
      s[1]: y = d[1];
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "unique case (1'b1): s = 11 matches two items, s = 00 none", violating=viol(lambda s: s in ("11", "00")))

fx("uq0_case_overlap", "uq0_case_overlap", r'''
module uq0_case_overlap (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    y = 1'b0;
    unique0 case (1'b1)
      s[0]: y = d[0];
      s[1]: y = d[1];
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "unique0 case (1'b1): s = 11 matches two items (no match is allowed for unique0)",
   violating=viol(lambda s: s == "11"))

fx("pr_case_overlap", "pr_case_overlap", r'''
module pr_case_overlap (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    y = 1'b0;
    priority case (1'b1)
      s[0]: y = d[0];
      s[1]: y = d[1];
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "priority case (1'b1): overlap is allowed (first wins), no match (s = 00) is a violation",
   violating=viol(lambda s: s == "00"))

fx("uq_case_full", "uq_case_full", r'''
module uq_case_full (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    unique case (s)
      2'd0: y = d[0];
      2'd1: y = d[1];
      2'd2: y = d[2];
      2'd3: y = d[3];
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "control: unique case covering every 2-state value (only the x selector violates)",
   violating=viol(lambda s: False))

fx("uq_if_nomatch", "uq_if_nomatch", r'''
module uq_if_nomatch (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    y = 1'b0;
    unique if (s == 2'd0) y = d[0];
    else if (s == 2'd1) y = d[1];
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "unique if without else: s = 2, 3 take no branch", violating=viol(lambda s: s in ("10", "11")))

fx("uq_if_overlap", "uq_if_overlap", r'''
module uq_if_overlap (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    unique if (s[0]) y = d[0];
    else if (s[1]) y = d[1];
    else y = 1'b0;
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "unique if: s = 11 makes two conditions true", violating=viol(lambda s: s == "11"))

fx("pr_if_nomatch", "pr_if_nomatch", r'''
module pr_if_nomatch (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    y = 1'b0;
    priority if (s[0]) y = d[0];
    else if (s[1]) y = d[1];
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "priority if without else: s = 00 takes no branch", violating=viol(lambda s: s == "00"))

fx("attr_full_case", "attr_full_case", r'''
module attr_full_case (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    y = 1'b0;
    (* full_case *)
    case (s)
      2'd0: y = d[0];
      2'd1: y = d[1];
      2'd2: y = d[2];
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "(* full_case *) on a case with no item for s = 3", violating=viol(lambda s: s == "11"))

fx("attr_parallel_case", "attr_parallel_case", r'''
module attr_parallel_case (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    y = 1'b0;
    (* parallel_case *)
    case (1'b1)
      s[0]: y = d[0];
      s[1]: y = d[1];
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "(* parallel_case *) on overlapping items: s = 11 matches two", violating=viol(lambda s: s == "11"))

fx("attr_keep", "attr_keep", r'''
module attr_keep (input logic [1:0] s, input logic [3:0] d, output logic y);
  (* keep *) logic t;
  assign t = d[0] & d[1];
  assign y = t | (s[0] & ~s[0]);
endmodule
''', P_SD, ["s", "d", "y"], S4, "(* keep *) on a wire: no functional meaning, an area meaning", violating=viol(lambda s: False))

fx("x_dontcare", "x_dontcare", r'''
module x_dontcare (input logic [1:0] s, input logic [3:0] d, output logic y);
  always_comb begin
    case (s)
      2'd0: y = d[0];
      2'd1: y = d[1];
      2'd2: y = d[2];
      default: y = 1'bx;
    endcase
  end
endmodule
''', P_SD, ["s", "d", "y"], S4, "an x literal as a don't-care for s = 3", violating=viol(lambda s: s == "11"))

MEM_P = [("we", "in", 1), ("wa", "in", 2), ("ra", "in", 2), ("wd", "in", 4), ("rd", "out", 4)]
MEM_S = [{"we": "1", "wa": "00", "ra": "01", "wd": "0001"}, {"we": "1", "wa": "01", "ra": "00", "wd": "0010"},
         {"we": "1", "wa": "01", "ra": "01", "wd": "0100"}, {"we": "0", "wa": "00", "ra": "01", "wd": "1111"},
         {"we": "1", "wa": "00", "ra": "00", "wd": "1000"}, {"we": "0", "wa": "00", "ra": "00", "wd": "0000"}]
for nm, attr in (("mem_rw_plain", ""), ("attr_no_rw_check", "(* no_rw_check *) ")):
    fx(nm, nm, r'''
module %s (input logic clk, input logic we, input logic [1:0] wa, input logic [1:0] ra, input logic [3:0] wd,
           output logic [3:0] rd);
  %slogic [3:0] mem [0:3];
  always_ff @(posedge clk) begin
    if (we) mem[wa] <= wd;
    rd <= mem[ra];
  end
endmodule
''' % (nm, attr), [("clk", "in", 1)] + MEM_P, ["we", "wa", "ra", "wd", "rd"], MEM_S,
       ("a read during a write of the same address (cycles 2, 4)" + (", with (* no_rw_check *)" if attr else "")),
       clock="clk", violating=[2, 4])

SELF_READ = ["rbw_comb", "rbw_held", "rbw_cond", "rbw_part"]


def add_self_read(repo):
    cases = {c["name"]: c for c in json.load(open(os.path.join(repo, "harness", "sv", "cases2.json")))["cases"]}
    for nm in SELF_READ:
        p = os.path.join(repo, "Examples", "system-verilog", "sem2", nm, nm + ".sv")
        c = cases.get(nm)
        if not os.path.exists(p) or c is None:
            continue
        sv = open(p).read()
        ports = sv_ports(p, c["top"])
        fx(nm, c["top"], sv, ports, c["signals"], c["stimulus"],
           "always_comb that reads a variable before writing it (Examples/system-verilog/sem2/%s)" % nm,
           clock=c.get("clock"), violating=list(range(len(c["stimulus"]))))
        FIX[nm]["from_repo"] = os.path.relpath(p, repo)


def sv_ports(path, top):
    import slang_env
    slang_env.pyslang()
    from pyslang.ast import SymbolKind, ArgumentDirection
    comp, root, errs, sm = slang_env.compile_files([path], top=top)
    inst = [i for i in root.topInstances if i.name == top][0]
    out = []
    for m in inst.body:
        if m.kind == SymbolKind.Port:
            out.append((m.name, "in" if m.direction == ArgumentDirection.In else "out", int(m.type.bitWidth)))
    return out


# ---------------------------------------------------------------------------------------------------------- tools

def run(cmd, cwd, timeout=300, env=None):
    """Run a command in its own process group, KILL the group on timeout and afterwards; report leftovers."""
    t0 = time.time()
    p = subprocess.Popen(["timeout", "-s", "KILL", str(timeout)] + cmd, cwd=cwd, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True, start_new_session=True, env=env)
    try:
        out, err = p.communicate(timeout=timeout + 30)
    except subprocess.TimeoutExpired:
        out, err = "", "communicate timeout"
    pgid = p.pid
    try:
        os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    left = subprocess.run(["ps", "-A", "-o", "pid=,pgid=,command="], capture_output=True, text=True).stdout
    survivors = [ln.strip() for ln in left.splitlines() if ln.split() and len(ln.split()) > 1
                 and ln.split()[1] == str(pgid)]
    return {"rc": p.returncode, "out": out, "err": err, "seconds": round(time.time() - t0, 2),
            "survivors": survivors}


def cycles(text):
    return [ln.strip() for ln in text.splitlines() if ln.startswith("CYCLE ")]


def gen_tb(f, mod_name):
    sys.path.insert(0, os.path.join(REPO, "harness", "sv"))
    import gen_tb2
    case = {"name": f["top"], "signals": f["signals"], "stimulus": f["stimulus"]}
    if f.get("clock"):
        case["clock"] = f["clock"]
    return gen_tb2.generate_tb2(mod_name, f["ports"], case)


def tool_slang(d, f):
    """pyslang 11 compilation diagnostics (errors E:, warnings W:) of the fixture alone. The analysis-pass errors
    (`multiple-always-assigns`, ...) are not included; none of these fixtures has two writers."""
    import slang_env
    ps = slang_env.pyslang()
    from pyslang.ast import Compilation, CompilationOptions
    from pyslang.syntax import SyntaxTree
    tree = SyntaxTree.fromFile(os.path.join(d, "dut.sv"))
    opts = CompilationOptions()
    opts.topModules = {f["top"]}
    comp = Compilation(ps.Bag([opts]))
    comp.addSyntaxTree(tree)
    diags = []
    for dg in comp.getAllDiagnostics():
        diags.append(("E" if dg.isError() else "W") + ":" + str(dg.code).replace("DiagCode(", "").rstrip(")"))
    return {"diags": sorted(set(diags))}


def tool_icarus(d, f, netlist=None):
    files = [os.path.join(d, "tb.sv")]
    if netlist:
        import subprocess as sp
        dat = sp.run(["yosys-config", "--datdir"], capture_output=True, text=True).stdout.strip()
        files += [netlist, os.path.join(dat, "simcells.v")]
    else:
        files.append(os.path.join(d, "dut.sv"))
    exe = os.path.join(d, "ivl_net" if netlist else "ivl_rtl")
    r = run(["iverilog", "-g2012", "-o", exe] + files, d, 120)
    if r["rc"] != 0:
        return {"error": (r["err"] or r["out"])[-400:]}
    r = run(["vvp", "-n", exe], d, 120)
    return {"cycles": cycles(r["out"]), "warnings": [ln.split("dut.sv")[-1][:160] for ln in r["out"].splitlines()
                                                     if not ln.startswith("CYCLE ") and ln.strip()][:5]}


def tool_verilator(d, f):
    vd = os.path.join(d, "vl")
    os.makedirs(vd, exist_ok=True)
    tb = open(os.path.join(d, "tb.sv")).read()
    tb2 = tb
    for c in ("1'bx", "1'bz"):
        tb2 = tb2.replace(c, "1'b0")
    import re
    tb2 = re.sub(r"(\d+'b)([01xz]+)", lambda m: m.group(1) + m.group(2).replace("x", "0").replace("z", "0"), tb2)
    open(os.path.join(vd, "tb.sv"), "w").write(tb2)
    r = run(["verilator", "--binary", "--timing", "-Wno-fatal", "-Wno-lint", "-Wno-style", "--top-module", "tb",
             "-Mdir", os.path.join(vd, "obj"), os.path.join(vd, "tb.sv"), os.path.join(d, "dut.sv")], vd, 300)
    if r["rc"] != 0:
        return {"error": (r["err"] or r["out"])[-400:]}
    r = run([os.path.join(vd, "obj", "Vtb")], vd, 60)
    msgs = [ln.strip()[:200] for ln in (r["out"] + "\n" + r["err"]).splitlines()
            if ln.strip() and not ln.startswith("CYCLE ") and "- V e r i l a t i o n" not in ln][:4]
    return {"cycles": cycles(r["out"]), "rc": r["rc"], "messages": msgs}


def tool_yosys(d, f):
    net = os.path.join(d, "netlist.v")
    res_json = os.path.join(d, "score.json")
    r = run([sys.executable, os.path.join(REPO, "svgolf", "score", "score.py"), "--no-gate", "--top", f["top"],
             "--netlist", net, "--json", res_json, os.path.join(d, "dut.sv")], d, 600)
    out = {"rc": r["rc"], "seconds": r["seconds"], "survivors": r["survivors"]}
    if r["rc"] != 0 or not os.path.exists(net):
        out["error"] = (r["out"] + r["err"])[-500:]
        if "does not price" not in out["error"]:
            return out
        # a sequential fixture: score.py refuses to PRICE flip-flops (svGolf scores combinational tasks), but the
        # pinned flow itself runs; run its two stages directly (same templates) to get the netlist
        sys.path.insert(0, os.path.join(REPO, "svgolf", "score"))
        import score as S
        rtl = os.path.join(d, "canon.il")
        open(os.path.join(d, "canon.ys"), "w").write(S.render_canon([os.path.join(d, "dut.sv")], f["top"], {}, rtl))
        open(os.path.join(d, "synth.ys"), "w").write(S.render_script(rtl, f["top"], os.path.join(d, "stat.json"),
                                                                    os.path.join(d, "ltp.txt"), net))
        for st in ("canon.ys", "synth.ys"):
            r2 = run(["yosys", "-q", "-s", os.path.join(d, st)], d, 600)
            out["survivors"] = out["survivors"] + r2["survivors"]
            if r2["rc"] != 0:
                out["error"] += " | direct %s: %s" % (st, (r2["out"] + r2["err"])[-300:])
                return out
        out["note"] = "netlist from the pinned flow run directly (score.py does not price flip-flops)"
    try:
        sc = json.load(open(res_json))
        out["area_ge"] = sc.get("area_ge")
        out["depth"] = sc.get("depth")
        out["gates"] = sc.get("gates")
    except Exception:  # noqa: BLE001
        pass
    sim = tool_icarus(d, f, netlist=net)
    out.update(sim)
    return out


def tool_extract(d, f):
    env_path = os.path.join(d, "dut.sv.json")
    r = run([sys.executable, "-I", os.path.join(HERE, "run_extract.py"), "--repo", REPO, "--", "--top", f["top"],
             os.path.join(d, "dut.sv"), "-o", env_path], d, 300)
    out = {"rc": r["rc"]}
    if r["rc"] != 0:
        out["error"] = (r["err"] or r["out"])[-300:]
        return out
    env = json.load(open(env_path))
    kinds = []

    def walk(x):
        if isinstance(x, dict):
            if x.get("kind") == "Unsupported" or x.get("kind") == "unsupported":
                kinds.append(x.get("sv_kind") or x.get("svKind"))
            for v in x.values():
                walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)
    walk(env)
    out["unsupported"] = sorted(set(k for k in kinds if k))
    out["envelope"] = env_path
    return out


# ---------------------------------------------------------------------------------------------------------- driver

REPO = None


def main():
    global REPO
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--only")
    ap.add_argument("--collect", action="store_true")
    a = ap.parse_args()
    REPO = os.path.abspath(a.repo)
    add_self_read(REPO)
    names = [n for n in FIX if not a.only or n in a.only.split(",")]
    os.makedirs(a.out, exist_ok=True)
    if a.collect:
        return collect(a.out, names)
    res = {}
    for n in names:
        f = FIX[n]
        d = os.path.join(os.path.abspath(a.out), n)
        os.makedirs(d, exist_ok=True)
        open(os.path.join(d, "dut.sv"), "w").write(f["sv"])
        open(os.path.join(d, "tb.sv"), "w").write(gen_tb(f, f["top"]))
        row = {"note": f["note"], "violating_cycles": f["violating"], "from_repo": f.get("from_repo")}
        for tname, fn in (("slang", tool_slang), ("icarus", tool_icarus), ("verilator", tool_verilator),
                          ("yosys", tool_yosys), ("extract", tool_extract)):
            try:
                row[tname] = fn(d, f)
            except Exception as exc:  # noqa: BLE001
                row[tname] = {"error": "%s: %s" % (type(exc).__name__, str(exc)[:300])}
        res[n] = row
        y = row["yosys"]
        print(n, "survivors=%d" % len(y.get("survivors", [])), "yosys_rc=%s" % y.get("rc"), flush=True)
    json.dump(res, open(os.path.join(a.out, "tools.json"), "w"), indent=1)
    # the Lean batch (model column): one slot acquisition for every fixture with an envelope
    cases = []
    for n in names:
        f = FIX[n]
        e = {"name": n, "example": "x10/" + n, "top": f["top"], "signals": f["signals"], "stimulus": f["stimulus"]}
        if f.get("clock"):
            e["clock"] = f["clock"]
        cases.append(e)
    json.dump({"fuel": 2000, "cases": cases}, open(os.path.join(a.out, "lean_cases.json"), "w"), indent=1)
    lines = ["#!/bin/bash", "cd %s" % REPO]
    for n in names:
        envp = res[n]["extract"].get("envelope")
        lines.append('echo "@@@CASE %s"' % n)
        if envp:
            lines.append("timeout 600 lake env lean --run harness/sv/runner2.lean %s %s %s src 2>&1 | head -60"
                         % (envp, os.path.join(os.path.abspath(a.out), "lean_cases.json"), n))
        else:
            lines.append('echo "@@@NOENVELOPE"')
    open(os.path.join(a.out, "lean_batch.sh"), "w").write("\n".join(lines) + "\n")
    print("wrote", os.path.join(a.out, "lean_batch.sh"))


def collect(out, names):
    tools = json.load(open(os.path.join(out, "tools.json")))
    model = {}
    cur = None
    lp = os.path.join(out, "lean.out")
    if os.path.exists(lp):
        for ln in open(lp, errors="replace"):
            if ln.startswith("@@@CASE "):
                cur = ln.split()[1]
                model[cur] = {"cycles": [], "lines": []}
            elif cur:
                if ln.startswith("CYCLE "):
                    model[cur]["cycles"].append(ln.strip())
                elif ln.strip():
                    model[cur]["lines"].append(ln.strip()[:300])
    rows = {}
    for n in names:
        t = tools[n]
        m = model.get(n, {})
        ref = t["icarus"].get("cycles") or []
        cmp = {}
        for col, tr in (("verilator", t["verilator"].get("cycles")), ("yosys_netlist", t["yosys"].get("cycles")),
                        ("model_run2", m.get("cycles"))):
            if not tr:
                cmp[col] = "no trace"
                continue
            diff = [k for k, (a, b) in enumerate(zip(ref, tr)) if a != b]
            viol = set(FIX[n]["violating"])
            xin = {k for k, e in enumerate(FIX[n]["stimulus"]) if any(c in "xz" for v in e.values() for c in v)}
            cmp[col] = {"differs_at": diff, "only_on_violating": bool(diff) and set(diff) <= viol,
                        "on_non_violating": sorted(set(diff) - viol),
                        "on_clean_cycles": sorted(set(diff) - viol - xin),
                        "trace_length": len(tr), "reference_length": len(ref)}
        rows[n] = dict(t, model=m, compare_to_icarus=cmp)
    json.dump({"schema": "ws4-x10/1", "fixtures": rows}, open(os.path.join(HERE, "x10.json"), "w"), indent=1)
    for n in names:
        print(n, json.dumps(rows[n]["compare_to_icarus"]))


if __name__ == "__main__":
    main()

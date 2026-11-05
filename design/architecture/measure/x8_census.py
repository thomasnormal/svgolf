#!/usr/bin/env python3.12
"""X8, the arc-granularity census (ARCH-NOTE §7 X8, §9 "compositionality"; EXECUTION-PLAN WS4 Day 1).

    python3.12 -I x8_census.py --src SRC_DIR [--corpus x8_corpus.json] [--only ID,..] [--modes lrm4,yosys] [--out x8.json]
    python3.12 -I x8_census.py --self-test

SRC_DIR holds the fetched sources (fetch_src.py --list x8_files.tsv --dest SRC_DIR); they are untrusted data, parsed
by pyslang only. For every design point of the corpus, every distinct module body in the elaborated hierarchy is
analysed by arcs.Module (bit-precise own logic, parameters folded) with its children summarized at four
granularities and the strongly connected components of each module's graph are collected:

    module  one arc set per child: every combinational output depends on every input that reaches some output
    port    per (output port, input port)
    field   per (leaf struct field, leaf struct field); non-struct ports whole
    bit     exact

Bit-level SCCs that share a signal are reported as ONE group. A group is
    hold    every member is a single bit whose only cycle is its self-edge (a variable that keeps its value on some
            path of a combinational process: a latch, or a case/if with no assignment on the no-match path)
    cycle   anything else (a combinational loop of the analysed graph)
and is MODULE-LEVEL when it contains a child-port node (it closes through at least one child's arcs).
A coarse-granularity group "persists" at a finer granularity when one of its nodes lies on a finer cycle group.

Modes (arcs.Module): lrm4 = LRM 4-state (a default-less case has a no-match path even when its items cover every
2-state value: an x/z selector matches nothing); 2state = that path only when the items do not cover; yosys = as
2state, plus `unique`/`priority` case read as full_case. Modes change only hold groups, never the module-level
census, unless a no-match path is itself on a loop (reported if it happens).

Also per module: the SCC count of the module graph QUOTIENTED to whole signals and to struct fields (children's arcs
exact): what a rank over signals or fields, rather than bits, would have to break.
"""
import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import slang_env  # noqa: E402
import arcs  # noqa: E402
from arcs import SymbolKind, ArgumentDirection, GRANULARITIES  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
FINER = {"module": ("port", "field", "bit"), "port": ("field", "bit"), "field": ("bit",), "bit": ()}


def body_key(inst):
    parts = [inst.definition.name]
    for m in inst.body:
        if m.kind == SymbolKind.Parameter:
            parts.append("%s=%s" % (m.name, m.value))
        elif m.kind == SymbolKind.TypeParameter:
            try:
                parts.append("%s=%s" % (m.name, m.targetType.type))
            except Exception:  # noqa: BLE001
                parts.append(m.name)
    return "|".join(parts)


def new_stats():
    return {"fallback_kinds": {}, "unhandled_statements": {}, "fixpoint_loops": 0,
            "processes": {"assign": 0, "comb": 0, "other": 0, "net-init": 0},
            "uninstantiated": [], "interfaces": 0, "inout_ports": 0, "const_folds": 0,
            "case_no_default": 0, "case_complete_2state": 0, "case_full_by_qualifier": 0}


class Census:
    def __init__(self, mode):
        self.mode = mode
        self.memo = {}
        self.order = []
        self.inst_count = {}

    def child(self, inst, g):
        if g == GRANULARITIES[0]:
            k = body_key(inst)
            self.inst_count[k] = self.inst_count.get(k, 0) + 1
        return self.analyse(inst)["summary"][g]

    def analyse(self, inst):
        key = body_key(inst)
        if key in self.memo:
            return self.memo[key]
        t0 = time.time()
        stats = new_stats()
        rec = {"key": key, "module": inst.definition.name}
        self.memo[key] = rec
        M = arcs.Module(inst, self.child, stats, mode=self.mode).run()
        ports_in, ports_out = [], []
        for p in inst.body:
            if p.kind == SymbolKind.Port and p.internalSymbol is not None:
                first, w, _ = M.sym_nodes(p.internalSymbol)
                (ports_in if p.direction == ArgumentDirection.In else
                 ports_out if p.direction == ArgumentDirection.Out else []).append((p.name, first, w, p.type))
        child_nodes = set()
        for k, (first, w, _t) in M.base.items():
            if k.startswith("<port>"):
                child_nodes.update(range(first, first + w))
        rec["summary"], rec["groups"] = {}, {}
        sources = [first + i for (_n, first, w, _t) in ports_in for i in range(w)]
        in_index = [(n, i) for (n, first, w, _t) in ports_in for i in range(w)]
        sinks = [first + i for (_n, first, w, _t) in ports_out for i in range(w)]
        nn = len(M.names)
        nodesets = {}
        for g in GRANULARITIES:
            comps, adj = arcs.sccs(nn, [M.edges, M.child_edges[g]])
            groups = group_by_signal(M, comps)
            reach = arcs.reach_inputs(adj, sources, sinks)
            rec["summary"][g] = coarsen(g, ports_in, ports_out, in_index, reach)
            rec.setdefault("arc_counts", {})[g] = arc_count(g, ports_in, ports_out, rec["summary"][g])
            if g == "port":
                rec["port_arcs"] = port_arcs(rec["summary"][g])
            rec["groups"][g] = [describe(M, grp, child_nodes) for grp in groups]
            nodesets[g] = [set(n for c in grp for n in c) for grp in groups]
            if g == "bit":
                rec["quotient"] = quotients(M, adj)
        for g in GRANULARITIES:
            for fg in FINER[g]:
                fine = set()
                for d, ns in zip(rec["groups"][fg], nodesets[fg]):
                    if d["kind"] == "cycle":
                        fine |= ns
                for d, ns in zip(rec["groups"][g], nodesets[g]):
                    d["persists_" + fg] = bool(ns & fine)
        rec["nodes"] = nn
        rec["own_edges"] = sum(bin(m).count("1") for m in M.edges.values())
        rec["fallbacks"] = M.fallbacks
        rec["stats"] = stats
        rec["seconds"] = round(time.time() - t0, 2)
        if os.environ.get("X8_PROGRESS"):
            print("  analysed %s (%d nodes, %.1fs)" % (rec["module"], nn, rec["seconds"]), file=sys.stderr, flush=True)
        self.order.append(key)
        return rec


def group_by_signal(M, comps):
    """Merge bit-level SCCs that share a signal: one reported group per signal cluster."""
    parent = list(range(len(comps)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    owner = {}
    for i, c in enumerate(comps):
        for n in c:
            lab = M.names[n][0]
            if lab in owner:
                a, b = find(i), find(owner[lab])
                if a != b:
                    parent[a] = b
            else:
                owner[lab] = i
    groups = {}
    for i, c in enumerate(comps):
        groups.setdefault(find(i), []).append(c)
    return list(groups.values())


def describe(M, grp, child_nodes):
    nodes = [n for c in grp for n in c]
    hold = all(len(c) == 1 for c in grp)
    sigs = sorted({M.names[n][0] for n in nodes})
    via = sorted({M.names[n][0] for n in nodes if n in child_nodes})
    return {"kind": "hold" if hold else "cycle", "bits": len(nodes), "signals": sigs[:40], "n_signals": len(sigs),
            "module_level": bool(via), "child_ports": via[:40]}


def atoms(g, typ, w):
    if g == "port":
        return [(0, w)]
    if g == "field":
        return arcs.field_atoms(typ) if typ is not None else [(0, w)]
    return [(i, 1) for i in range(w)]


def coarsen(g, ports_in, ports_out, in_index, reach):
    """Bit summary -> summary at granularity g (both interfaces coarsened)."""
    out = {}
    if g == "module":
        allin = 0
        for (n, first, w, typ) in ports_out:
            for i in range(w):
                allin |= reach.get(first + i, 0)
        for (n, first, w, typ) in ports_out:
            out[n] = [allin if reach.get(first + i, 0) else 0 for i in range(w)]
        return {"in_index": in_index, "out": out}
    in_atoms = []
    pos = 0
    for (_n, _first, w, typ) in ports_in:
        for lo, aw in atoms(g, typ, w):
            in_atoms.append(((1 << aw) - 1) << (pos + lo))
        pos += w
    for (n, first, w, typ) in ports_out:
        bits = [reach.get(first + i, 0) for i in range(w)]
        if g != "bit":
            res = [0] * w
            for lo, aw in atoms(g, typ, w):
                u = 0
                for i in range(lo, min(lo + aw, w)):
                    u |= bits[i]
                exp = 0
                if u:
                    for am in in_atoms:
                        if am & u:
                            exp |= am
                for i in range(lo, min(lo + aw, w)):
                    res[i] = exp
            bits = res
        out[n] = bits
    return {"in_index": in_index, "out": out}


def port_arcs(summ):
    out = {}
    for o, bits in summ["out"].items():
        ins = set()
        for m in bits:
            for b in arcs.iter_bits(m):
                ins.add(summ["in_index"][b][0])
        if ins:
            out[o] = sorted(ins)
    return out


def arc_count(g, ports_in, ports_out, summ):
    """Size of the summary at granularity g: distinct (output atom, input atom) pairs."""
    if g == "bit":
        return sum(bin(m).count("1") for bits in summ["out"].values() for m in bits)
    pos, in_atoms = 0, []
    for (_n, _f, w, typ) in ports_in:
        for lo, aw in (atoms(g, typ, w) if g != "module" else [(0, w)]):
            in_atoms.append(((1 << aw) - 1) << (pos + lo))
        pos += w
    if g == "module":
        in_atoms = [sum(in_atoms)] if in_atoms else []
    n = 0
    outs = [(n_, w, typ) for (n_, _f, w, typ) in ports_out]
    if g == "module":
        anyo = any(m for bits in summ["out"].values() for m in bits)
        return 1 if anyo else 0
    for (name, w, typ) in outs:
        bits = summ["out"][name]
        for lo, aw in atoms(g, typ, w):
            m = bits[lo] if lo < len(bits) else 0
            n += sum(1 for am in in_atoms if am & m)
    return n


def quotients(M, adj):
    """Cycle counts of the module graph quotiented to process, signal and field atoms (child arcs exact). `process`:
    every bit a combinational process writes is that process (the granularity of today's `Acyclic` rank on process
    indices); `signal`: one atom per declared signal; `field`: one per leaf struct field."""
    out = {}
    for mode in ("process", "signal", "field"):
        atom_of = {}
        nxt = 0
        if mode == "process":
            # a node written by a combinational process is that process; every other node is itself
            pid_atom = {}
            for n in range(len(M.names)):
                p = M.writer.get(n)
                if p is None:
                    atom_of[n] = nxt
                    nxt += 1
                else:
                    if p not in pid_atom:
                        pid_atom[p] = nxt
                        nxt += 1
                    atom_of[n] = pid_atom[p]
        for k, (first, w, typ) in (M.base.items() if mode != "process" else []):
            if mode == "signal" or typ is None:
                for i in range(w):
                    atom_of[first + i] = nxt
                nxt += 1
            else:
                covered = [None] * w
                for lo, aw in arcs.field_atoms(typ):
                    for i in range(lo, min(lo + aw, w)):
                        covered[i] = nxt
                    nxt += 1
                for i in range(w):
                    if covered[i] is None:
                        covered[i] = nxt
                        nxt += 1
                    atom_of[first + i] = covered[i]
        qadj = {}
        for u, m in adj.items():
            au = atom_of.get(u)
            if au is None:
                continue
            acc = qadj.get(au, 0)
            for v in arcs.iter_bits(m):
                av = atom_of.get(v)
                if av is not None:
                    acc |= 1 << av
            qadj[au] = acc
        comps, _ = arcs.sccs(nxt, [qadj])
        out[mode + "_cycles"] = sum(1 for c in comps if len(c) > 1)
        out[mode + "_selfloops"] = sum(1 for c in comps if len(c) == 1)
        if mode == "process":
            members = {}
            for n, a in atom_of.items():
                members.setdefault(a, set()).add(M.names[n][0])
            desc = []
            for c in comps:
                if len(c) > 1:
                    desc.append([sorted(members.get(a, ()))[:8] for a in c][:12])
            out["process_cycle_members"] = desc
    return out


def run_point(point, src, mode):
    files = [os.path.join(src, f) for f in point["files"]] + [os.path.join(HERE, f) for f in point.get("extra_files", [])]
    inc = [os.path.join(src, d) for d in point.get("incdirs", [])]
    t0 = time.time()
    comp, root, errors, sm = slang_env.compile_files(files, top=point["top"], incdirs=inc,
                                                     defines=point.get("defines", []),
                                                     params=point.get("params", []))
    res = {"id": point["id"], "mode": mode, "top": point["top"], "params": point.get("params", []),
           "slang_errors": errors[:20], "n_slang_errors": len(errors)}
    tops = [i for i in root.topInstances if i.name == point["top"]]
    if not tops:
        res["error"] = "top not found"
        return res
    c = Census(mode)
    c.analyse(tops[0])
    mods = [c.memo[k] for k in c.order]
    for m in mods:
        m.pop("summary", None)
        m["instances"] = c.inst_count.get(m["key"], 1)
    res["modules"] = mods
    res["totals"] = totals(mods)
    res["seconds"] = round(time.time() - t0, 1)
    return res


def totals(mods):
    t = {}
    for g in GRANULARITIES:
        gs = [d for m in mods for d in m["groups"][g]]
        t[g] = {"module_level_cycles": sum(1 for d in gs if d["module_level"] and d["kind"] == "cycle"),
                "intra_cycles": sum(1 for d in gs if not d["module_level"] and d["kind"] == "cycle"),
                "holds": sum(1 for d in gs if d["kind"] == "hold"),
                "modules_with_module_level_cycle": sum(1 for m in mods if any(
                    d["module_level"] and d["kind"] == "cycle" for d in m["groups"][g]))}
        for fg in FINER[g]:
            t[g]["module_level_cycles_vanishing_at_" + fg] = sum(
                1 for d in gs if d["module_level"] and d["kind"] == "cycle" and not d["persists_" + fg])
    t["quotient"] = {k: sum(m["quotient"][k] for m in mods) for k in mods[0]["quotient"]
                     if not k.endswith("_members")} if mods else {}
    t["arc_counts"] = {g: sum(m["arc_counts"][g] for m in mods) for g in GRANULARITIES}
    t["distinct_bodies"] = len(mods)
    t["fallbacks"] = sum(m["fallbacks"] for m in mods)
    t["fallback_kinds"] = {}
    for m in mods:
        for k, v in m["stats"]["fallback_kinds"].items():
            t["fallback_kinds"][k] = t["fallback_kinds"].get(k, 0) + v
    t["unhandled_statements"] = {}
    for m in mods:
        for k, v in m["stats"]["unhandled_statements"].items():
            t["unhandled_statements"][k] = t["unhandled_statements"].get(k, 0) + v
    for k in ("fixpoint_loops", "const_folds", "case_no_default", "case_complete_2state", "case_full_by_qualifier"):
        t[k] = sum(m["stats"][k] for m in mods)
    return t


SELF_TEST = r'''
package st_pkg; typedef struct packed { logic [3:0] a; logic [3:0] b; } pair_t; endpackage
module bitc (input logic [1:0] i, input logic x, output logic [1:0] o);
  assign o[0] = x;
  assign o[1] = i[0];
endmodule
module fldc import st_pkg::*; (input pair_t pin, input logic [3:0] x, output pair_t pout);
  always_comb begin pout.a = pin.a; pout.b = x; end
endmodule
module realc (input logic i, output logic o); assign o = i; endmodule
module twoc (input logic a, input logic b, output logic p, output logic q); assign p = a; assign q = b; endmodule
module fallc #(parameter bit FT = 1'b0) (input logic push, input logic s, output logic e);
  assign e = s & ~(FT & push);
endmodule
module topt import st_pkg::*; (input logic x, input logic [3:0] y, input logic [1:0] sel,
                               output logic [1:0] o, output pair_t q, output logic z, output logic [3:0] lat,
                               output logic [3:0] cs, output logic v);
  logic [1:0] ci;
  assign ci = {1'b0, o[0]};
  bitc u_bit (.i(ci), .x(x), .o(o));
  pair_t fi;
  always_comb begin fi = '0; fi.a = q.b; end
  fldc u_fld (.pin(fi), .x(y), .pout(q));
  logic w1, w2;
  realc u_r1 (.i(w2), .o(w1));
  realc u_r2 (.i(w1), .o(w2));
  assign z = w1;
  always_comb begin if (x) lat = y; end
  always_comb begin
    unique case (sel)
      2'd0: cs = y; 2'd1: cs = ~y; 2'd2: cs = '0; 2'd3: cs = '1;
    endcase
  end
  logic pp, qq;
  twoc u_two (.a(qq), .b(x), .p(pp), .q(qq));
  logic e, pu;
  fallc u_fall (.push(pu), .s(x), .e(e));
  assign pu = e;
  assign v = pp ^ e;
endmodule
'''


def self_test():
    import tempfile
    d = tempfile.mkdtemp()
    p = os.path.join(d, "t.sv")
    open(p, "w").write(SELF_TEST)
    ok = True
    # expected (cycle groups, hold groups) per granularity, all cycles module-level:
    #   u_bit  bit-port false cycle: module, port, field;  u_fld  struct false cycle: module, port;
    #   u_r1/u_r2  real loop: all;  u_two  q <- b only, p <- a: false only at module granularity;
    #   u_fall  FT = 0 folds the push path away: no cycle anywhere;  lat: hold everywhere;
    #   cs: hold in lrm4 only (its items cover every 2-state value).
    exp = {"lrm4": {"module": (4, 2), "port": (3, 2), "field": (2, 2), "bit": (1, 2)},
           "2state": {"module": (4, 1), "port": (3, 1), "field": (2, 1), "bit": (1, 1)}}
    for mode in ("lrm4", "2state"):
        res = run_point({"id": "self", "top": "topt", "files": [p]}, "/", mode)
        top = [m for m in res["modules"] if m["module"] == "topt"][0]
        got = {g: (sum(1 for d in top["groups"][g] if d["kind"] == "cycle"),
                   sum(1 for d in top["groups"][g] if d["kind"] == "hold")) for g in GRANULARITIES}
        good = got == exp[mode]
        ok &= good
        print(mode, "PASS" if good else "FAIL", got, "expected", exp[mode], res["slang_errors"])
    print("SELF-TEST", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src")
    ap.add_argument("--corpus", default=os.path.join(HERE, "x8_corpus.json"))
    ap.add_argument("--only")
    ap.add_argument("--modes", default="lrm4,yosys")
    ap.add_argument("--out")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        sys.exit(self_test())
    corpus = json.load(open(a.corpus))
    pts = corpus["points"]
    if a.only:
        keep = set(a.only.split(","))
        pts = [p for p in pts if p["id"] in keep]
    results = []
    for p in pts:
        for mode in a.modes.split(","):
            r = run_point(p, a.src, mode)
            results.append(r)
            t = r.get("totals", {})
            print(p["id"], mode, "slang_errors=%s" % r.get("n_slang_errors"), "%ss" % r.get("seconds"),
                  json.dumps({g: t.get(g) for g in GRANULARITIES}), "quotient", json.dumps(t.get("quotient")),
                  flush=True)
    if a.out:
        write_compact(results, a.out)


def write_compact(results, path):
    """The data file: long body keys (cva6's configuration struct is in every key) become name + hash; the per-port
    arc lists are kept for the first mode of each point only (modes do not change arcs); no indentation."""
    import hashlib
    seen = set()
    for r in results:
        for m in r.get("modules", []):
            k = m["key"]
            if len(k) > 120:
                m["key"] = "%s|sha1:%s" % (m["module"], hashlib.sha1(k.encode()).hexdigest()[:16])
        if r["id"] in seen and "modules" in r:
            # a second mode of the same point changes only hold groups: keep those
            r["modules"] = [{"module": m["module"], "key": m["key"],
                             "holds": [d["signals"] for d in m["groups"]["bit"] if d["kind"] == "hold"]}
                            for m in r["modules"] if "groups" in m]
        seen.add(r["id"])
    with open(path, "w") as f:
        json.dump({"schema": "ws4-x8/2", "pyslang": "11.0.0", "results": results}, f, separators=(",", ":"))
        f.write("\n")


if __name__ == "__main__":
    main()

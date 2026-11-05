#!/usr/bin/env python3.12
"""X9, second half: how often real blocks make a PROCEDURAL decision on a value that could be x (ARCH-NOTE §4.3 R-X,
§9 "2-state and 4-state mismatch"; EXECUTION-PLAN WS4 Day 3).

    python3.12 -I x9_census.py --rb0 RB0_SRC --repo REPO [--x8src X8_SRC] [--out x9.json]
    python3.12 -I x9_census.py --self-test

A decision site is an `if` condition or a `case` subject/item of a procedural block (combinational or edge), counted
once per source location and module definition. Its condition "could be x" when the condition's dependency cone,
followed through combinational edges (arcs.Module, bit-precise, parameters folded), register next-state edges
(edge blocks, executed abstractly the same way) and child instances (bit-exact arcs, plus each child's x-capable
outputs), reaches an x SOURCE:

    unreset-reg   a register with no constant assignment in its block's leading `if` branch (no reset / clear):
                  x from the LRM's x start until first written
    x-literal     an x/z literal (`'x`, `4'b1x0z`, ...)
    out-of-range  a dynamic select whose index type can exceed the selected range (an out-of-range read is x)
    div           `/` or `%` (a zero divisor gives x)
    undriven      a signal read but driven by nothing
    child-x       a child output that is x-capable by the same analysis inside the child

Input ports are assumed known (the environment rely of a task), and a register assigned a constant in the leading
branch is assumed reset. The census is an over-approximation of "could be x" (every rule adds dependencies); a site
counted "never x" is never x under those two assumptions. `?:` is not a decision (LRM 11.4.11 merges; X9Mono.lean
proves `LVec.ternary` monotone) and is not counted.
"""
import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import slang_env  # noqa: E402
import arcs  # noqa: E402
from arcs import (SymbolKind, StatementKind, ExpressionKind, ArgumentDirection, BO, State, TK,  # noqa: E402
                  EdgeKind, GRANULARITIES, tw, iter_bits, elem_info)

KINDS = ("unreset-reg", "x-literal", "out-of-range", "div", "undriven", "child-x")


class XModule(arcs.Module):
    def __init__(self, inst, summaries, stats, xchild):
        super().__init__(inst, summaries, stats, mode="lrm4")
        self.xchild = xchild                        # child inst -> {out port: [bool per bit]}
        self.pseudo = {}
        for k in ("x-literal", "out-of-range", "div", "child-x"):
            first, _, _ = self.nodes_of("<x>" + k, 1, "<x>" + k)
            self.pseudo[k] = first
        self.seq_edges = {}
        self.registers = set()                      # node ids
        self.reset_regs = set()
        self.decisions = {}                         # (offset) -> {"kind", "seq", "mask"}
        self.in_seq = False
        self.items = False                          # evaluating case-item patterns: their x/z digits are wildcards

    def pm(self, k):
        return 1 << self.pseudo[k]

    # x sources inside expressions
    def ev(self, e, st):
        k = e.kind
        if k == ExpressionKind.IntegerLiteral:
            v = e.value
            hu = getattr(v, "hasUnknown", False)
            if callable(hu):
                hu = hu()
            if hu and not self.items:
                return [self.pm("x-literal")] * tw(e.type)
        if k == ExpressionKind.UnbasedUnsizedIntegerLiteral and not self.items:
            if str(e.literalValue).lower() in ("x", "z", "1'bx", "1'bz"):
                return [self.pm("x-literal")] * tw(e.type)
        res = super().ev(e, st)
        if k in (ExpressionKind.ElementSelect, ExpressionKind.RangeSelect):
            if self.may_be_out_of_range(e, st):
                res = [m | self.pm("out-of-range") for m in res]
        elif k == ExpressionKind.BinaryOp and e.op in (BO.Divide, BO.Mod):
            res = [m | self.pm("div") for m in res]
        return res

    def may_be_out_of_range(self, e, st):
        rng, _ew = elem_info(e.value.type)
        if rng is None:
            return False
        lo, hi = min(rng.left, rng.right), max(rng.left, rng.right)
        if e.kind == ExpressionKind.ElementSelect:
            if self.cint(e.selector, st) is not None:
                return False
            iw = tw(e.selector.type)
            signed = bool(getattr(e.selector.type, "isSigned", False))
            imin, imax = (-(1 << (iw - 1)), (1 << (iw - 1)) - 1) if signed else (0, (1 << iw) - 1)
            return imin < lo or imax > hi
        if self.cint(e.left, st) is not None:
            return False
        return True

    # decisions
    def exec(self, s, st):
        k = s.kind
        if k == StatementKind.Conditional:
            conds = list(s.conditions)
            if not (len(conds) == 1 and conds[0].pattern is None and self.const_truth(conds[0].expr, st) is not None):
                m = 0
                for c in conds:
                    m |= self.orall(self.ev(c.expr, st))
                self.record(s, "if", m)
        elif k == StatementKind.Case:
            m = self.orall(self.ev(s.expr, st))
            self.items = True
            try:
                for it in s.items:
                    for x in it.expressions:
                        m |= self.orall(self.ev(x, st))
            finally:
                self.items = False
            if self.cint(s.expr, st) is None:
                self.record(s, {"Normal": "case", "WildcardJustZ": "casez", "WildcardXOrZ": "casex",
                                "Inside": "case inside"}[str(s.condition).split(".")[-1]], m)
        return super().exec(s, st)

    def record(self, s, kind, mask):
        off = s.sourceRange.start.offset
        d = self.decisions.setdefault(off, {"kind": kind, "seq": self.in_seq, "mask": 0,
                                            "check": str(getattr(s, "check", "")).split(".")[-1]})
        d["mask"] |= mask

    # registers
    def seq_block(self, pb):
        b = pb.body
        if pb.procedureKind != arcs.PK.Always and pb.procedureKind != arcs.PK.AlwaysFF:
            return
        if b.kind != StatementKind.Timed:
            return
        tc = b.timing
        evs = [tc] if tc.kind == TK.SignalEvent else (list(tc.events) if tc.kind == TK.EventList else [])
        if not any(getattr(ev, "edge", EdgeKind.None_) != EdgeKind.None_ for ev in evs):
            return
        self.in_seq = True
        st = State()
        self.exec(b.stmt, st)
        lead = b.stmt
        while lead.kind == StatementKind.Block or (lead.kind == StatementKind.List and len(list(lead.list)) >= 1):
            lead = lead.body if lead.kind == StatementKind.Block else list(lead.list)[0]
        reset_keys = set()
        if lead.kind == StatementKind.Conditional:
            st2 = State()
            self.exec(lead.ifTrue, st2)
            for k, v in st2.env.items():
                if all(x is not None and x == 0 for x in v):
                    reset_keys.add(k)
        self.in_seq = False
        for k, v in st.env.items():
            b0 = self.base.get(k)
            if b0 is None or k in self.loop_keys:
                continue
            first, w, _ = b0
            for i, x in enumerate(v):
                if x is not None and i < w:
                    self.registers.add(first + i)
                    self.seq_edges[first + i] = self.seq_edges.get(first + i, 0) | x
                    if k in reset_keys:
                        self.reset_regs.add(first + i)

    def instance(self, inst):
        super().instance(inst)
        label = inst.hierarchicalPath
        top = self.body.hierarchicalPath
        if label.startswith(top + "."):
            label = label[len(top) + 1:]
        xs = self.xchild(inst)
        for pname, bits in xs.items():
            b0 = self.base.get("<port>%s.%s" % (label, pname))
            if b0 is None:
                continue
            for i, flag in enumerate(bits[:b0[1]]):
                if flag:
                    self.edges[b0[0] + i] = self.edges.get(b0[0] + i, 0) | self.pm("child-x")


def body_key(inst):
    parts = [inst.definition.name]
    for m in inst.body:
        if m.kind == SymbolKind.Parameter:
            parts.append("%s=%s" % (m.name, m.value))
    return "|".join(parts)


class Census:
    def __init__(self):
        self.memo = {}
        self.order = []

    def analyse(self, inst):
        key = body_key(inst)
        if key in self.memo:
            return self.memo[key]
        rec = {"module": inst.definition.name, "key": key}
        self.memo[key] = rec
        stats = {"fallback_kinds": {}, "unhandled_statements": {}, "fixpoint_loops": 0,
                 "processes": {"assign": 0, "comb": 0, "other": 0, "net-init": 0}, "uninstantiated": [],
                 "interfaces": 0, "inout_ports": 0, "const_folds": 0, "case_no_default": 0,
                 "case_complete_2state": 0, "case_full_by_qualifier": 0}
        M = XModule(inst, lambda ch, g: self.analyse(ch)["summary"], stats,
                    lambda ch: self.analyse(ch)["x_out"]).run()
        ins, outs = [], []
        for p in inst.body:
            if p.kind == SymbolKind.Port and p.internalSymbol is not None:
                first, w, _ = M.sym_nodes(p.internalSymbol)
                (ins if p.direction == ArgumentDirection.In else outs if p.direction == ArgumentDirection.Out
                 else []).append((p.name, first, w))
        adj = {}
        for E in (M.edges, M.child_edges["bit"], M.seq_edges):
            for u, m in E.items():
                adj[u] = adj.get(u, 0) | m
        input_nodes = {f + i for (_n, f, w) in ins for i in range(w)}
        child_port_nodes = set()
        for k, (f, w, _t) in M.base.items():
            if k.startswith("<port>"):
                child_port_nodes.update(range(f, f + w))
        sources = {k: set() for k in KINDS}
        for k in ("x-literal", "out-of-range", "div", "child-x"):
            sources[k].add(M.pseudo[k])
        for n in M.registers - M.reset_regs:
            sources["unreset-reg"].add(n)
        pseudo = set(M.pseudo.values())
        for n in range(len(M.names)):
            lab = M.names[n][0]
            if (n not in adj and n not in input_nodes and n not in M.registers and n not in child_port_nodes
                    and n not in pseudo and not lab.startswith("<") and n not in M.writer):
                sources["undriven"].add(n)
        # reverse adjacency, then reachability per source kind
        radj = {}
        for u, m in adj.items():
            for v in iter_bits(m):
                radj.setdefault(v, []).append(u)
        reach = {}
        for k, srcs in sources.items():
            seen = set(srcs)
            stack = list(srcs)
            while stack:
                v = stack.pop()
                for u in radj.get(v, ()):
                    if u not in seen:
                        seen.add(u)
                        stack.append(u)
            reach[k] = seen
        allx = set().union(*reach.values())
        sites = []
        for off, d in sorted(M.decisions.items()):
            ks = [k for k in KINDS if any(n in reach[k] for n in iter_bits(d["mask"]))]
            sites.append({"kind": d["kind"], "seq": d["seq"], "check": d["check"], "x_sources": ks,
                          "reads_input_only": all(n in input_nodes for n in iter_bits(d["mask"]))})
        x_out = {}
        for (name, f, w) in outs:
            x_out[name] = [(f + i) in allx for i in range(w)]
        rec["x_out"] = x_out
        rec["sites"] = sites
        rec["registers"] = len(M.registers)
        rec["unreset_registers"] = len(M.registers - M.reset_regs)
        # the arc summary (bit) for the parent, as in x8_census
        sources_in = [f + i for (_n, f, w) in ins for i in range(w)]
        in_index = [(n, i) for (n, f, w) in ins for i in range(w)]
        sinks = [f + i for (_n, f, w) in outs for i in range(w)]
        comb_adj = {}
        for E in (M.edges, M.child_edges["bit"]):
            for u, m in E.items():
                comb_adj[u] = comb_adj.get(u, 0) | m
        r = arcs.reach_inputs(comb_adj, sources_in, sinks)
        rec["summary"] = {"in_index": in_index,
                          "out": {n: [r.get(f + i, 0) for i in range(w)] for (n, f, w) in outs}}
        self.order.append(key)
        return rec


def run(files, top, incdirs=(), defines=(), params=()):
    comp, root, errors, sm = slang_env.compile_files(files, top=top, incdirs=incdirs, defines=defines, params=params)
    tops = [i for i in root.topInstances if i.name == top]
    if not tops:
        return {"error": "top not found", "slang_errors": errors[:5]}
    c = Census()
    c.analyse(tops[0])
    mods = []
    for k in c.order:
        m = dict(c.memo[k])
        m.pop("summary", None)
        m.pop("x_out", None)
        if len(m["key"]) > 120:
            m["key"] = m["module"] + "|..."
        mods.append(m)
    return {"slang_errors": errors[:5], "n_slang_errors": len(errors), "modules": mods}


def tally(mods):
    t = {"sites": 0, "sites_may_be_x": 0, "comb_sites": 0, "comb_may_be_x": 0, "seq_sites": 0, "seq_may_be_x": 0,
         "by_source": {k: 0 for k in KINDS}, "only_unreset": 0}
    for m in mods:
        for s in m["sites"]:
            t["sites"] += 1
            x = bool(s["x_sources"])
            t["sites_may_be_x"] += x
            t["seq_sites" if s["seq"] else "comb_sites"] += 1
            t["seq_may_be_x" if s["seq"] else "comb_may_be_x"] += x
            for k in s["x_sources"]:
                t["by_source"][k] += 1
            if s["x_sources"] == ["unreset-reg"]:
                t["only_unreset"] += 1
    return t


SELF_TEST = r'''
module child (input logic clk, input logic [1:0] a, output logic [1:0] q, output logic r);
  logic [1:0] noreset;
  always_ff @(posedge clk) noreset <= a;          // no reset: x until written
  assign q = noreset;
  assign r = a[0];
endmodule
module t (input logic clk, input logic rst_n, input logic [1:0] a, input logic [2:0] i, input logic [3:0] v,
          output logic [3:0] y, output logic z);
  logic [1:0] q; logic r;
  child u (.clk(clk), .a(a), .q(q), .r(r));
  logic [1:0] cnt;
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) cnt <= '0;
    else if (a[0]) cnt <= cnt + 1;                // decision on an input: never x
  always_comb begin
    y = '0;
    if (cnt[1]) y = v;                            // reset register: never x
    if (q[0]) y = ~v;                             // child's unreset register: child-x
    case (v[i])                                   // i can reach 4..7: out-of-range
      1'b1: z = 1'b1;
      default: z = 1'b0;
    endcase
    if (r) y[0] = 1'b1;                           // child output that is a wire of an input: never x
  end
endmodule
'''


def self_test():
    import tempfile
    d = tempfile.mkdtemp()
    p = os.path.join(d, "t.sv")
    open(p, "w").write(SELF_TEST)
    res = run([p], "t")
    top = [m for m in res["modules"] if m["module"] == "t"][0]
    got = [(s["kind"], s["seq"], s["x_sources"]) for s in top["sites"]]
    exp = [("if", True, []), ("if", True, []), ("if", False, []), ("if", False, ["child-x"]),
           ("case", False, ["out-of-range"]), ("if", False, [])]
    ok = got == exp
    print("got     ", got)
    print("expected", exp)
    print("SELF-TEST", "PASS" if ok else "FAIL", res["slang_errors"])
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rb0", help="RB0 fetch root (files/<project>/...)")
    ap.add_argument("--repo")
    ap.add_argument("--x8src", help="X8 fetch root, to add the X8 core points")
    ap.add_argument("--out")
    ap.add_argument("--only")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        sys.exit(self_test())
    results = []
    corpus = json.load(open(os.path.join(a.repo, "svgolf", "design", "real-world-sv", "rb0", "corpus.json")))
    for b in corpus:
        if a.only and b["id"] not in a.only.split(","):
            continue
        cwd = os.path.join(a.rb0, "files", b["project"])
        files = [os.path.join(cwd, f) for f in b["files"]]
        if not all(os.path.exists(f) for f in files):
            results.append({"id": b["id"], "error": "missing files"})
            continue
        t0 = time.time()
        try:
            r = run(files, b["top"], [os.path.join(cwd, d) for d in b["incdirs"]], b.get("defines") or [])
        except Exception as exc:  # noqa: BLE001
            r = {"error": "%s: %s" % (type(exc).__name__, str(exc)[:200])}
        r.update(id=b["id"], project=b["project"], kind=b.get("kind"), seconds=round(time.time() - t0, 1))
        if "modules" in r:
            r["totals"] = tally(r["modules"])
        results.append(r)
        print(b["id"], r.get("n_slang_errors"), r.get("error", ""), json.dumps(r.get("totals", {}).get("sites")),
              json.dumps(r.get("totals", {}).get("sites_may_be_x")), flush=True)
    if a.x8src:
        pts = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "x8_corpus.json")))["points"]
        for p in pts:
            if a.only and p["id"] not in a.only.split(","):
                continue
            here = os.path.dirname(os.path.abspath(__file__))
            files = [os.path.join(a.x8src, f) for f in p["files"]] + [os.path.join(here, f) for f in p.get("extra_files", [])]
            t0 = time.time()
            r = run(files, p["top"], [os.path.join(a.x8src, d) for d in p.get("incdirs", [])],
                    p.get("defines", []), p.get("params", []))
            r.update(id=p["id"], project=p["id"].split("@")[0], kind="core", seconds=round(time.time() - t0, 1))
            if "modules" in r:
                r["totals"] = tally(r["modules"])
            results.append(r)
            print(p["id"], r.get("n_slang_errors"), json.dumps(r.get("totals", {})), flush=True)
    if a.out:
        with open(a.out, "w") as f:
            json.dump({"schema": "ws4-x9/1", "results": results}, f, separators=(",", ":"))
            f.write("\n")


if __name__ == "__main__":
    main()

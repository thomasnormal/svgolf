#!/usr/bin/env python3.12
"""X3, the record-transfer audit (ARCH-NOTE §7, EXECUTION-PLAN WS4 Day 1). No Lean is run.

    python3.12 -I x3_audit.py --repo REPO_ROOT [--out x3.json]

For every accepted svGolf record (svgolf/leaderboard/data/<task>/<hash>.{json,sv,lean}) and every registered reference
proof (svgolf/tasks/<task>/task.json "references"), it answers two questions:

  A. Does the proof establish an acyclicity certificate, and of WHICH design?  Read from the .lean text: the named
     theorem whose statement contains `Acyclic`, whether its target is the loaded `design.sem …` or the lowered design
     `d'` with `(design.sem …).lowerComb = some d'`, whether it is built by `sv_structure` or by an explicit rank, and
     which bridge the final `solution` uses (`satisfiedAt_of_comb` / `satisfiedAt_of_lowered`).
  B. Does the design make a procedural decision on a value that could be x?  Read from the .sv by pyslang at the task's
     default parameter point: every `if`/`case` statement (procedural decisions) and every `?:` (the conditional
     OPERATOR, which on an ambiguous condition merges both arms by LRM 11.4.11 and is therefore not a decision), with
     the signals its condition reads, each classified as an input port, a signal written by the SAME process, or a
     signal written by ANOTHER process. Sites are deduplicated by source offset (one site per generate body).

Whether a condition "could be x" is then answered twice:
  * settled: at the closed slot under the statement's hypotheses (known inputs). The proof's own knownness facts decide
    it (`sv_equations` states `known_<sig>` for every driven signal; the by-hand proofs carry their own); a condition
    reading only input ports and proved-known driven signals cannot be x there.
  * transient: in SOME activation under SOME legal process-atomic schedule from the LRM x start. An `always_comb`
    runs once at time zero (LRM 9.2.2.2.1) and the Active-region order is arbitrary (4.7), so a condition reading a
    signal written by another process, or an input port the environment has not yet driven, can be x in that
    activation. The count is measured; the "can be x" reading is the LRM's (JUDGED application).
"""
import argparse
import hashlib
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import slang_env  # noqa: E402


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


# ---------------------------------------------------------------- proof side (text) ----------------------------------

THM = re.compile(r"^(?:private\s+)?theorem\s+(\S+)(.*?):=\s*by", re.S | re.M)


def proof_facts(text):
    """Named theorems that state `Acyclic`, their target, and how they are proved."""
    out = []
    starts = [m.start() for m in re.finditer(r"^(?:private\s+)?(?:theorem|lemma|def)\s", text, re.M)] + [len(text)]
    for a, b in zip(starts, starts[1:]):
        chunk = text[a:b]
        m = re.match(r"(?:private\s+)?(theorem|lemma)\s+(\S+)(.*?):=", chunk, re.S)
        if not m:
            continue
        name, stmt = m.group(2), m.group(3)
        if "Acyclic" not in stmt or "satisfiedAt" in name:
            continue
        body = chunk[m.end():]
        if re.search(r"lowerComb\s*=\s*some\s+d'", stmt):
            target = "lowered"          # Acyclic d' of the lowered design
        elif re.search(r"Acyclic\s*\(?\s*design\.sem", stmt):
            target = "design.sem"       # Acyclic of the loaded design itself
        else:
            target = "other"
        how = "sv_structure" if "sv_structure" in body else ("explicit rank" if re.search(r"refine\s*⟨", body) else "other")
        out.append({"theorem": name, "target": target, "proved_by": how,
                    "also_CombDesign": "CombDesign" in stmt})
    bridge = sorted(set(re.findall(r"\b(satisfiedAt_of_comb|satisfiedAt_of_lowered)\b", text)))
    knownness = "sv_equations known_*" if "sv_equations" in text else "by hand (own lemmas)"
    return {"acyclic_theorems": out, "bridge": bridge, "knownness": knownness,
            "lines": text.count("\n")}


# ---------------------------------------------------------------- design side (pyslang) ------------------------------

def design_facts(sv_path, top):
    ps = slang_env.pyslang()
    from pyslang.ast import (SymbolKind, StatementKind, ExpressionKind, VisitAction, ArgumentDirection)
    comp, root, errors, sm = slang_env.compile_files([sv_path], top=top)
    inst = [i for i in root.topInstances if i.name == top][0]
    body = inst.body

    inputs = set()
    for m in body:
        if m.kind == SymbolKind.Port and m.direction == ArgumentDirection.In:
            inputs.add(m.name)

    def root_name(e):
        while True:
            k = e.kind
            if k == ExpressionKind.NamedValue:
                return [e.symbol.name]
            if k in (ExpressionKind.ElementSelect, ExpressionKind.RangeSelect, ExpressionKind.MemberAccess):
                e = e.value
                continue
            if k == ExpressionKind.Concatenation:
                out = []
                for op in e.operands:
                    out += root_name(op)
                return out
            if k == ExpressionKind.Conversion:
                e = e.operand
                continue
            return []

    def reads(expr):
        names = set()

        def v(n):
            if getattr(n, "kind", None) == ExpressionKind.NamedValue:
                s = n.symbol
                if s.kind in (SymbolKind.Variable, SymbolKind.Net, SymbolKind.Port):
                    names.add(s.name)
            return VisitAction.Advance
        expr.visit(v)
        return names

    procs = []          # one entry per elaborated process: kind, source offset, written names
    decisions = []      # one entry per elaborated decision: process index, kind, source offset, condition reads
    seen_proc_off = {}

    def off(node):
        return node.sourceRange.start.offset

    def collect_process(kind, node, walk_root):
        idx = len(procs)
        writes = set()
        local_dec = []

        def v(n):
            k = getattr(n, "kind", None)
            if k == ExpressionKind.Assignment:
                writes.update(root_name(n.left))
            elif k == StatementKind.Conditional:
                r = set()
                for c in n.conditions:
                    r |= reads(c.expr)
                local_dec.append({"kind": "if", "check": str(n.check).split(".")[-1], "offset": off(n),
                                  "reads": sorted(r)})
            elif k == StatementKind.Case:
                local_dec.append({"kind": {"Normal": "case", "WildcardJustZ": "casez", "WildcardXOrZ": "casex",
                                           "Inside": "case inside"}[str(n.condition).split(".")[-1]],
                                  "check": str(n.check).split(".")[-1], "offset": off(n),
                                  "reads": sorted(reads(n.expr)), "default": n.defaultCase is not None})
            elif k == ExpressionKind.ConditionalOp:
                r = set()
                for c in n.conditions:
                    r |= reads(c.expr)
                local_dec.append({"kind": "?:", "check": "", "offset": off(n), "reads": sorted(r)})
            return VisitAction.Advance
        walk_root.visit(v)
        procs.append({"kind": kind, "offset": off(node) if hasattr(node, "sourceRange") else node.location.offset,
                      "writes": sorted(writes)})
        for d in local_dec:
            d["proc"] = idx
            decisions.append(d)

    def top_visit(n):
        k = getattr(n, "kind", None)
        if k == SymbolKind.ContinuousAssign:
            collect_process("assign", n.assignment, n.assignment)
            return VisitAction.Skip
        if k == SymbolKind.ProceduralBlock:
            pk = str(n.procedureKind).split(".")[-1]
            collect_process(pk, n.body, n.body)
            return VisitAction.Skip
        return VisitAction.Advance
    body.visit(top_visit)

    writers = {}
    for i, p in enumerate(procs):
        for w in p["writes"]:
            writers.setdefault(w, set()).add(i)

    # classify, then deduplicate by source offset
    sites = {}
    for d in decisions:
        cls = {}
        for r in d["reads"]:
            if r in inputs:
                cls[r] = "input"
            elif writers.get(r, set()) - {d["proc"]}:
                cls[r] = "other process"
            elif d["proc"] in writers.get(r, set()):
                cls[r] = "same process"
            else:
                cls[r] = "undriven"
        key = d["offset"]
        if key not in sites:
            sites[key] = {"kind": d["kind"], "check": d["check"], "reads": cls,
                          "in_process": procs[d["proc"]]["kind"], "default": d.get("default"),
                          "elaborated_copies": 0}
        sites[key]["elaborated_copies"] += 1
    proc_sites = {}
    for p in procs:
        proc_sites.setdefault((p["kind"], p["offset"]), 0)
        proc_sites[(p["kind"], p["offset"])] += 1
    kinds = {}
    for (k, _o) in proc_sites:
        kinds[k] = kinds.get(k, 0) + 1
    return {"errors": errors, "process_sites_by_kind": kinds, "elaborated_processes": len(procs),
            "decision_sites": [dict(v, offset=k) for k, v in sorted(sites.items())]}


# ---------------------------------------------------------------- driver ----------------------------------------------

def classify(entry):
    """The two answers per proof, and the transfer route they imply."""
    pf, df = entry["proof"], entry["design"]
    acy = pf["acyclic_theorems"]
    has_acy = bool(acy)
    targets = sorted({a["target"] for a in acy})
    procedural = [s for s in df["decision_sites"] if s["kind"] != "?:"]
    condops = [s for s in df["decision_sites"] if s["kind"] == "?:"]
    # settled: every condition reads only inputs or driven signals, and the proof states knownness of driven signals
    settled_x = [s for s in procedural if any(c == "undriven" for c in s["reads"].values())]
    transient = [s for s in procedural if any(c in ("other process", "input") for c in s["reads"].values())]
    transient_internal = [s for s in procedural if any(c == "other process" for c in s["reads"].values())]
    only_assign = set(df["process_sites_by_kind"]) <= {"assign"}
    route = ("R-COMB assign-only (E-core-0, gate G-A) + R-DESIGN2, with the proof's own certificate"
             if only_assign and targets == ["design.sem"] else
             "R-COMB with always_comb (gate G-B) + a lemma lifting the LOWERED design's certificate to the source design"
             if targets == ["lowered"] else "re-certify")
    return {"acyclic_certificate": has_acy, "certificate_targets": targets,
            "procedural_decision_sites": len(procedural), "conditional_operator_sites": len(condops),
            "settled_x_decision_sites": len(settled_x),
            "transient_x_decision_sites": len(transient),
            "transient_x_decision_sites_on_internal_signals": len(transient_internal),
            "assign_only": only_assign, "transfer_route": route}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    sv = os.path.join(a.repo, "svgolf")
    rows = []
    ref_by_hash = {}
    for task in sorted(os.listdir(os.path.join(sv, "tasks"))):
        tj = os.path.join(sv, "tasks", task, "task.json")
        if not os.path.exists(tj):
            continue
        t = json.load(open(tj))
        for r in t.get("references", []):
            svp = os.path.join(sv, "tasks", task, r["sv"])
            lnp = os.path.join(sv, "tasks", task, r["lean"])
            e = {"kind": "reference", "task": task, "sv": os.path.relpath(svp, a.repo),
                 "lean": os.path.relpath(lnp, a.repo), "top": t["top"]}
            e["proof"] = proof_facts(open(lnp).read())
            e["design"] = design_facts(svp, t["top"])
            e["verdict"] = classify(e)
            rows.append(e)
            ref_by_hash[(sha(svp), sha(lnp))] = e
    records = []
    lb = os.path.join(sv, "leaderboard", "data")
    for task in sorted(os.listdir(lb)):
        for f in sorted(os.listdir(os.path.join(lb, task))):
            if not f.endswith(".json"):
                continue
            h = f[:-5]
            rec = json.load(open(os.path.join(lb, task, f)))
            key = (sha(os.path.join(lb, task, h + ".sv")), sha(os.path.join(lb, task, h + ".lean")))
            ref = ref_by_hash.get(key)
            records.append({"task": task, "record_hash": h, "player": rec["player"],
                            "lean_name": rec["files"]["lean"]["name"],
                            "identical_to_reference": ref["lean"] if ref else None,
                            "verdict": ref["verdict"] if ref else "NOT A REFERENCE: audit by hand"})
    summary = {
        "references": len(rows),
        "references_with_acyclic_certificate": sum(r["verdict"]["acyclic_certificate"] for r in rows),
        "references_certificate_on_loaded_design": sum(r["verdict"]["certificate_targets"] == ["design.sem"]
                                                       for r in rows),
        "references_certificate_on_lowered_design": sum(r["verdict"]["certificate_targets"] == ["lowered"]
                                                        for r in rows),
        "references_assign_only": sum(r["verdict"]["assign_only"] for r in rows),
        "references_with_procedural_decisions": sum(r["verdict"]["procedural_decision_sites"] > 0 for r in rows),
        "references_with_conditional_operator": sum(r["verdict"]["conditional_operator_sites"] > 0 for r in rows),
        "references_with_settled_x_decision": sum(r["verdict"]["settled_x_decision_sites"] > 0 for r in rows),
        "references_with_transient_x_decision": sum(r["verdict"]["transient_x_decision_sites"] > 0 for r in rows),
        "records": len(records),
        "records_identical_to_a_reference": sum(r["identical_to_reference"] is not None for r in records),
        "records_assign_only_with_certificate_on_loaded_design": sum(
            isinstance(r["verdict"], dict) and r["verdict"]["assign_only"]
            and r["verdict"]["certificate_targets"] == ["design.sem"] for r in records),
        "records_with_procedural_decisions": sum(isinstance(r["verdict"], dict)
                                                 and r["verdict"]["procedural_decision_sites"] > 0 for r in records),
    }
    out = {"schema": "ws4-x3/1", "summary": summary, "records": records, "references": rows}
    js = json.dumps(out, indent=1, sort_keys=False)
    if a.out:
        open(a.out, "w").write(js + "\n")
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()

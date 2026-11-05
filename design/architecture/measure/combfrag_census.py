#!/usr/bin/env python3.12
"""The E-fragment coverage census: how much real RTL L's `CombFragE` (`Stmt2.combOk`) covers.

    python3.12 -I combfrag_census.py verify --rb0-src SRC --rb0-tsv FILES_TSV --x8-src SRC --x8-tsv X8_FILES_TSV
    python3.12 -I combfrag_census.py extract-x8 --repo REPO --x8-src SRC --out OUT [-j 3]
    python3.12 -I combfrag_census.py batch --rb-out RB_OUT --out OUT --json BATCH.json
    (lean --run CombFragCensus.lean BATCH.json > CFE.txt, against arch-loop's build, through the slot)
    python3.12 -I combfrag_census.py report --txt CFE.txt --batch BATCH.json [--wa-txt CFE_WA.txt --wa-batch BATCH_WA.json]
               --x8-extract X8_EXTRACT.json --json combfrag.json

* RB0: the census blocks as is (no `@wa` variant), from the Day 6 re-run's envelopes (`integ1102`'s extractor; the
  extractor of arch-loop `d7af3dac` is the same file, `git diff` empty).
* X8: every distinct module of the three cores at their default X8 point (`x8.json`, mode lrm4: ibex_core@default,
  cv32e40p_core@default, cva6@cv32a6_imac_sv32+WT), each extracted as its own top from the core's file list, so it
  is measured at its OWN default parameters, like an RB0 block.
The sources are untrusted data under scratch, checked by sha256 first (`verify`); they are parsed by pyslang only.
"""
import argparse
import collections
import concurrent.futures
import hashlib
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def cmd_verify(a):
    bad = n = 0
    for tsv, src, rel in ((a.rb0_tsv, a.rb0_src, lambda f: os.path.join(f[0], f[3])),
                          (a.x8_tsv, a.x8_src, lambda f: os.path.join(f[0], f[3]))):
        for ln in open(tsv):
            if ln.startswith("#") or not ln.strip():
                continue
            f = ln.rstrip("\n").split("\t")
            if len(f) < 5 or f[4] in ("-", ""):
                continue
            p = os.path.join(src, rel(f))
            n += 1
            if not os.path.exists(p) or sha(p) != f[4]:
                bad += 1
                print("MISMATCH", p)
    print("verified", n, "files,", bad, "mismatches")
    sys.exit(1 if bad else 0)


def x8_jobs(a):
    corpus = {p["id"]: p for p in json.load(open(os.path.join(HERE, "x8_corpus.json")))["points"]}
    res = json.load(open(os.path.join(HERE, "x8.json")))["results"]
    jobs = []
    for r in res:
        if r["mode"] != "lrm4" or not r["id"].endswith(("@default", "+WT")):
            continue
        p = corpus[r["id"]]
        for mod in sorted(set(m["module"] for m in r["modules"])):
            jobs.append((p, mod))
    return jobs


def extract_one(a, p, mod):
    core = p["project"]
    d = os.path.join(a.out, "x8", core)
    os.makedirs(d, exist_ok=True)
    env = os.path.join(d, mod + ".env.json")
    files = [os.path.join(a.x8_src, f) for f in p["files"]] + [os.path.join(HERE, f) for f in p.get("extra_files", [])]
    cmd = [sys.executable, "-I", os.path.join(HERE, "run_extract.py"), "--repo", a.repo, "--", "--top", mod]
    for i in p.get("incdirs", []):
        cmd += ["-I", os.path.join(a.x8_src, i)]
    if p.get("defines"):
        # the extractor has no -D: a first source file of `define lines (one compilation, one preprocessor)
        dfile = os.path.join(a.out, "x8", core + "_defines.sv")
        open(dfile, "w").write("".join("`define %s\n" % df for df in p["defines"]))
        files = [dfile] + files
    cmd += files + ["-o", env]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=a.timeout)
        rc, err = r.returncode, r.stderr[-400:]
    except subprocess.TimeoutExpired:
        rc, err = None, "timeout"
    return {"id": "%s:%s" % (core, mod), "group": core, "module": mod, "rc": rc,
            "envelope": env if rc == 0 and os.path.exists(env) else None, "stderr": err}


def cmd_extract_x8(a):
    jobs = x8_jobs(a)
    out = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.j) as ex:
        for r in ex.map(lambda pm: extract_one(a, *pm), jobs):
            out.append(r)
            print(r["id"], r["rc"], (r["stderr"] or "").strip().split("\n")[-1][:120] if r["rc"] else "")
    json.dump(out, open(os.path.join(a.out, "x8_extract.json"), "w"), indent=1)


def cmd_batch(a):
    rows = []
    for f in sorted(os.listdir(a.rb_out)):
        if not f.endswith(".env.json") or "@" in f:
            continue
        rows.append({"id": "rb0:" + f[:-9], "group": "rb0", "envelope": os.path.join(a.rb_out, f)})
    ext = json.load(open(os.path.join(a.out, "x8_extract.json")))
    rows += [{"id": r["id"], "group": "x8-" + r["group"], "envelope": r["envelope"]} for r in ext if r["envelope"]]
    json.dump(rows, open(a.json, "w"))
    print(len(rows), "designs;", collections.Counter(r["group"] for r in rows))


REFUSAL_CATS = [
    ("package-scoped parameter", "a package-scoped parameter (a CVA6Cfg struct default, a package width)"),
    ("Initial", "an initial process (also inside a generate)"),
    ("LocalDecl", "a block-local declaration in a procedural block"),
    ("unknown enum", "a package enum type or member in a parameter default"),
    ("in a constant context", "a constant construct the loader does not fold (replication, concatenation, call, ...)"),
    ("untyped-width", "an untyped parameter or localparam (expression-width rule)"),
    ("AlwaysLatch", "always_latch"),
    ("SysCall", "a system task call"),
    ("unrecoverable packed", "an enum with unrecoverable packed dimensions"),
]


def refusal_cat(msg):
    for key, label in REFUSAL_CATS:
        if key in msg:
            return label
    return msg[:80]


def count_kind(x, kind):
    if isinstance(x, dict):
        return (x.get("kind") == kind) + sum(count_kind(v, kind) for v in x.values())
    if isinstance(x, list):
        return sum(count_kind(v, kind) for v in x)
    return 0


def count_star(x):
    if isinstance(x, dict):
        return (x.get("kind") == "AlwaysComb" and bool(x.get("always_star_lowered"))) + sum(count_star(v) for v in x.values())
    if isinstance(x, list):
        return sum(count_star(v) for v in x)
    return 0


def template_combs(env_path):
    """always_comb processes in the TOP module's text (processes and generate bodies, each written once), loaded or not;
    and how many of them the extractor lowered from `always @*` / a complete sensitivity list (`always_star_lowered`)."""
    e = json.load(open(env_path))
    tops = [m for m in e["design"]["modules"] if m.get("name") == e["top"]] or e["design"]["modules"][:1]
    m = tops[0]
    body = [m.get("processes", []), m.get("generates", [])]
    return count_kind(body, "AlwaysComb"), count_star(body), e["top"]


def _by_cat(rs):
    c = collections.Counter()
    for r in rs:
        if r["load"] != "ok":
            c[refusal_cat(r["load"])] += r["tmpl_combs"]
    return c


def summarize(rs):
    loaded = [r for r in rs if r["load"] == "ok"]
    combs = [c for r in loaded for c in r["combs"]]
    out = [c for c in combs if not c["ok"]]
    return {
        "designs": len(rs), "designs_load": len(loaded),
        "load_refusals": collections.Counter(refusal_cat(r["load"]) for r in rs if r["load"] != "ok").most_common(),
        "always_comb_in_text_all_designs": sum(r["tmpl_combs"] for r in rs),
        "always_comb_in_text_refused_designs": sum(r["tmpl_combs"] for r in rs if r["load"] != "ok"),
        "always_comb_in_text_by_refusal": sorted(
            collections.Counter({k: v for k, v in _by_cat(rs).items()}).items(), key=lambda kv: -kv[1]),
        "always_comb_in_text_lowered_from_always_star_loaded_designs": sum(r["tmpl_star"] for r in loaded),
        "always_comb_processes_loaded": len(combs),
        # every loaded design here is all-or-nothing (its always_comb processes are all lowered from `always @*` or none
        # are), checked below, so the split is per design
        "split_is_per_design": all(r["tmpl_star"] in (0, len(r["combs"])) for r in loaded),
        "loaded_written_always_comb": sum(len(r["combs"]) for r in loaded if not r["tmpl_star"]),
        "loaded_written_always_comb_in_fragment": sum(c["ok"] for r in loaded if not r["tmpl_star"] for c in r["combs"]),
        "loaded_lowered_always_star": sum(len(r["combs"]) for r in loaded if r["tmpl_star"]),
        "loaded_lowered_always_star_in_fragment": sum(c["ok"] for r in loaded if r["tmpl_star"] for c in r["combs"]),
        "in_fragment": len(combs) - len(out),
        "in_fragment_qualified": sum(1 for c in combs if c["ok"] and c["qual"]),
        "in_fragment_case_inside": sum(1 for c in combs if c["ok"] and c["inside"]),
        "out_of_fragment": len(out),
        "out_by_reason": collections.Counter(c["why"].split("|")[0] for c in out).most_common(),
        "out_detail": sorted("%s: %s" % (r["id"], c["why"]) for r in loaded for c in r["combs"] if not c["ok"]),
        "why_agrees_with_combOk": all(c["agree"] for c in combs),
        "designs_with_always_comb": sum(1 for r in loaded if r["combs"]),
        "designs_all_always_comb_in_fragment": sum(1 for r in loaded if r["combs"] and all(c["ok"] for c in r["combs"])),
        "designs_has_unsupported": sum(1 for r in loaded if r["design_has_unsupported"]),
        "designs_all_in_fragment_and_unsupported_free": sum(
            1 for r in loaded if r["combs"] and all(c["ok"] for c in r["combs"]) and not r["design_has_unsupported"]),
        # the E route's design-level hypotheses besides the body: AllFour (sem_run / activate_single), the design stage
        # (hasUnsupported false), and the process shape (one always_comb; or assigns and always_comb only, the shape
        # `Elab.toDesign2_ofDesign2` round-trips)
        "designs_all_in_fragment_unsupported_free_all_four": sum(
            1 for r in loaded if r["combs"] and all(c["ok"] for c in r["combs"]) and not r["design_has_unsupported"]
            and r["all_four"]),
        "designs_all_four": sum(1 for r in loaded if r["all_four"]),
        "designs_comb_only": sum(1 for r in loaded if r["combs"] and all(k in ("alwaysComb", "assign") for k in r["kinds"])),
        "designs_comb_only_all_hypotheses": [
            r["id"] for r in loaded if r["combs"] and all(k in ("alwaysComb", "assign") for k in r["kinds"])
            and all(c["ok"] for c in r["combs"]) and not r["design_has_unsupported"] and r["all_four"]],
        "designs_all_in_fragment_and_unsupported_free_ids": [
            r["id"] for r in loaded if r["combs"] and all(c["ok"] for c in r["combs"]) and not r["design_has_unsupported"]],
        "single_process_designs": sum(1 for r in loaded if r["single"]),
        "single_process_all_hypotheses": sum(
            1 for r in loaded if r["single"] and r["combs"][0]["ok"] and not r["design_has_unsupported"] and r["all_four"]),
        "single_process_in_fragment": sum(1 for r in loaded if r["single"] and r["combs"][0]["ok"]),
        "single_process_ids": [r["id"] for r in loaded if r["single"]],
        "written_before_read": "pending (L's writtenBeforeRead check has not landed on arch-loop; head d7af3dac)",
    }


def cmd_report(a):
    rows = [json.loads(ln[4:]) for ln in open(a.txt, errors="replace") if ln.startswith("CFE ")]
    batch = {b["id"]: b for b in json.load(open(a.batch))}
    for r in rows:
        r["tmpl_combs"], r["tmpl_star"], r["top"] = template_combs(batch[r["id"]]["envelope"])
    wa = []
    if a.wa_txt:
        wbatch = {b["id"]: b for b in json.load(open(a.wa_batch))}
        wa = [json.loads(ln[4:]) for ln in open(a.wa_txt, errors="replace") if ln.startswith("CFE ")]
        for r in wa:
            r["tmpl_combs"], r["tmpl_star"], r["top"] = template_combs(wbatch[r["id"]]["envelope"])
    ext = {r["id"]: r for r in json.load(open(a.x8_extract))} if a.x8_extract else {}
    rb0 = [r for r in rows if r["group"] == "rb0"]
    x8 = [r for r in rows if r["group"] != "rb0"]
    rb_tops = {r["top"] for r in rb0}
    x8_only = [r for r in x8 if r["top"] not in rb_tops]
    groups = collections.OrderedDict()
    groups["rb0 (as is)"] = rb0
    for g in ["x8-ibex", "x8-cv32e40p", "x8-cva6"]:
        groups[g] = [r for r in rows if r["group"] == g]
    groups["x8 (three cores)"] = x8
    groups["overall (rb0 + x8, deduplicated by top module)"] = rb0 + x8_only
    if wa:
        # per RB0 block: the most-modernized variant that loads (@wa3 > @wa2 > @wa > as is), else the as-is row
        best = []
        for r in rb0:
            vs = {w["id"]: w for w in wa}
            pick = r
            for suf in ("@wa3", "@wa2", "@wa"):
                w = vs.get(r["id"] + suf)
                if w and w["load"] == "ok":
                    pick = w
                    break
            best.append(pick)
        groups["rb0 (best Day 6 variant)"] = best
    summ = collections.OrderedDict((g, summarize(rs)) for g, rs in groups.items())
    summ["overlap_rb0_x8_tops"] = sorted(r["top"] for r in x8 if r["top"] in rb_tops)
    if ext:
        summ["x8_extraction"] = {"modules": len(ext), "extracted": sum(1 for r in ext.values() if r["envelope"]),
                                 "failed": {r["id"]: (r["stderr"] or "").strip().split("\n")[-1][:160]
                                            for r in ext.values() if not r["envelope"]}}
    json.dump({"schema": "combfrag/1", "arch_loop": "d7af3dac", "summary": summ, "rows": rows, "rows_rb0_variants": wa},
              open(a.json, "w"), indent=1)
    for g, s in summ.items():
        if not isinstance(s, dict) or "designs" not in s:
            print("==", g, json.dumps(s)[:600])
            continue
        print("==", g, json.dumps({k: v for k, v in s.items()
                                   if k not in ("out_by_reason", "load_refusals", "out_detail", "single_process_ids",
                                                "always_comb_in_text_by_refusal",
                                                "designs_all_in_fragment_and_unsupported_free_ids")}))
        print("   out by reason:", s["out_by_reason"])
        print("   load refusals:", s["load_refusals"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["verify", "extract-x8", "batch", "report"])
    ap.add_argument("--rb0-src")
    ap.add_argument("--rb0-tsv")
    ap.add_argument("--x8-src")
    ap.add_argument("--x8-tsv")
    ap.add_argument("--repo")
    ap.add_argument("--out")
    ap.add_argument("--rb-out")
    ap.add_argument("--json")
    ap.add_argument("--txt")
    ap.add_argument("--x8-extract")
    ap.add_argument("--batch")
    ap.add_argument("--wa-txt")
    ap.add_argument("--wa-batch")
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=900)
    a = ap.parse_args()
    {"verify": cmd_verify, "extract-x8": cmd_extract_x8, "batch": cmd_batch, "report": cmd_report}[a.cmd](a)


if __name__ == "__main__":
    main()

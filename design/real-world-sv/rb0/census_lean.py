#!/usr/bin/env python3.12
"""WP-RB0 census, step 4: the Lean loader and the structure tactics.

    python3.12 census_lean.py gen  --out OUTDIR --lean-dir LEANDIR   # writes LEANDIR/{A,B,C}.lean + batch.sh + index.json
    (run LEANDIR/batch.sh from the repository root, through the machine's Lean slot)
    python3.12 census_lean.py parse --out OUTDIR --lean-dir LEANDIR  # reads LEANDIR/*.json -> OUTDIR/lean.json

`gen` reads OUTDIR/<id>.json (census_extract.py) and, for every block whose extraction succeeded,
emits a Lean command block

    namespace RB.«ID»
    load_design_sv2 d from "<envelope>"
    #eval ... (d.sem <defaults>).hasUnsupported / firstLoud

so the loader's verdict (`load_design_sv2`: parse, the Lean-vs-slang cross-check, the loader guards)
and the lowered design's `Design2.hasUnsupported` (the checker's `design`-stage test) are measured at
the design's DEFAULT parameter point. For blocks with no Unsupported node whose processes are
continuous assigns / always_comb only, it also runs the structure tactic:

    example (P1 ... : Nat) : CombDesign (d.sem P1 ...) := by sv_structure?

(the family quantified over its parameters, as a task statement would) and, for an always_comb design,
the lowering `(d.sem ..).lowerComb`. File A holds the small envelopes, file B the tactic runs
(each of which re-loads its design), file C the envelopes above 1.5 MB, each in its own `lean --json`
process with its own timeout, all inside ONE slot acquisition (`batch.sh`).
"""
import argparse
import glob
import json
import os
import re
import sys

BIG = 1_500_000


def lean_str(s):
    return json.dumps(s)


def default_args(env, top):
    """The default parameter point of the top: one Nat per ParameterDecl, from slang's `resolved`;
    None when some parameter has no non-negative integer default."""
    mods = env["design"]["modules"]
    m = next((x for x in mods if x["name"] == top), mods[0])
    args = []
    for p in m.get("params", []):
        if p.get("kind") != "ParameterDecl":
            continue
        v = p.get("resolved")
        if not isinstance(v, int) or v < 0:
            return None, [q["name"] for q in m.get("params", []) if q.get("kind") == "ParameterDecl"]
        args.append(v)
    names = [q["name"] for q in m.get("params", []) if q.get("kind") == "ParameterDecl"]
    return args, names


def process_kinds(env, top):
    mods = env["design"]["modules"]
    m = next((x for x in mods if x["name"] == top), mods[0])
    ks = {}
    for p in m.get("processes", []):
        ks[p.get("kind")] = ks.get(p.get("kind"), 0) + 1
    return ks, len(m.get("generates", [])), len(mods) > 1


def header(extra_imports):
    imps = "\n".join("import " + i for i in ["LeanModels.Sv.Ingest2"] + extra_imports)
    return imps + "\nopen LeanModels.Sv\nopen LeanModels.Sv.CombView\n\n"


def block_load(bid, env_path, args):
    ns = "«%s»" % bid
    ap = (" " + " ".join(str(a) for a in args)) if args else ""
    return (f"namespace RB.{ns}\n"
            f"#eval IO.println \"RBBEGIN {bid}\"\n"
            f"load_design_sv2 d from {lean_str(env_path)}\n"
            f"#eval show IO Unit from do\n"
            f"  let dd := d.sem{ap}\n"
            f"  let what := match dd.firstLoud with | some (k, t) => s!\"{{k}}: {{t}}\" | none => \"\"\n"
            f"  IO.println s!\"RBLOAD {bid} unsupported={{dd.hasUnsupported}} first={{(what.take 200).replace \"\\n\" \" \"}}\"\n")


def block_tactics(bid, args, names, kinds):
    """Structure and equations tactics on the design family quantified over its parameters (the form a task
    statement has): `sv_structure?` on `CombDesign`, `sv_equations?` in the settled-state context."""
    binders = (" ".join("(p%d : Nat)" % i for i in range(len(names))) + " ") if names else ""
    app = (" " + " ".join("p%d" % i for i in range(len(names)))) if names else ""
    out = ""
    if set(kinds) <= {"Assign"}:
        out += (f"#eval IO.println \"RBTAC {bid} structure\"\n"
                f"example {binders}: CombDesign (d.sem{app}) := by\n  sv_structure?\n"
                f"#eval IO.println \"RBTAC {bid} equations\"\n"
                f"example {binders}(hc : CombDesign (d.sem{app})) (ha : Acyclic (d.sem{app})) (st : SvState)\n"
                f"    (heqs : CombEqs (d.sem{app}) st) (hsh : StateShape (d.sem{app}) st) : True := by\n  sv_equations?\n")
    elif set(kinds) <= {"Assign", "AlwaysComb"}:
        out += (f"#eval IO.println \"RBTAC {bid} structure-lowered\"\n"
                f"example {binders}: \u2203 d', (d.sem{app}).lowerComb = some d' \u2227 CombDesign d' := by\n"
                f"  sv_structure?\n"
                f"#eval IO.println \"RBTAC {bid} equations-lowered\"\n"
                f"example {binders}{{d' : Design2}} (hl : (d.sem{app}).lowerComb = some d') (hc : CombDesign d')\n"
                f"    (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st) (hsh : StateShape d' st) : True := by\n"
                f"  sv_equations?\n")
    return out


def gen(a):
    os.makedirs(a.lean_dir, exist_ok=True)
    recs = [json.load(open(f)) for f in sorted(glob.glob(os.path.join(a.out, "*.json")))
            if not f.endswith((".env.json", "lean.json", "srcgate.json")) and not os.path.basename(f).startswith("lean")]
    if a.only_suffix or a.ids:
        want = set(a.ids.split(",")) if a.ids else set()
        sufs = tuple(a.only_suffix.split(",")) if a.only_suffix else ()
        recs = [r for r in recs if (sufs and r["id"].endswith(sufs)) or r["id"] in want]
    files = {"A": [], "B": [], "C": []}
    index = {}
    for r in recs:
        if r.get("extract", {}).get("rc") != 0 or not r.get("env_bytes"):
            continue
        bid = r["id"]
        env_path = os.path.join(a.out, bid + ".env.json")
        env = json.load(open(env_path))
        args, names = default_args(env, r["top"])
        kinds, ngen, hier = process_kinds(env, r["top"])
        if args is None:
            index[bid] = {"file": None, "reason": "a parameter has no non-negative integer default: %s" % names}
            continue
        which = "C" if r["env_bytes"] > BIG else "A"
        files[which].append(block_load(bid, env_path, args) + "end RB.«%s»\n\n" % bid)
        index[bid] = {"file": which, "args": args, "params": names}
        clean = not r.get("n_unsupported") and not r["slang"]["n_errors"]
        tac = block_tactics(bid, args, names, kinds) if (clean and not hier and r["env_bytes"] <= BIG) else ""
        if tac:
            files["B"].append(block_load(bid, env_path, args) + tac + "end RB.«%s»\n\n" % bid)
            index[bid]["tactic"] = "lowered" if "AlwaysComb" in kinds else "plain"
    chunk = {"A": 8, "B": 5, "C": 1}
    names = []
    for k, blocks in files.items():
        extra = ["LeanModels.Sv.CombViewTactic", "LeanModels.Sv.CombProcTactic", "LeanModels.Sv.CombEqTactic"] if k == "B" else []
        for i in range(0, len(blocks), chunk[k]):
            nm = "%s%s%02d" % (a.tag, k, i // chunk[k])
            open(os.path.join(a.lean_dir, nm + ".lean"), "w").write(header(extra) + "".join(blocks[i:i + chunk[k]]))
            names.append(nm)
    json.dump(index, open(os.path.join(a.lean_dir, "index.json"), "w"), indent=1)
    for nm_sh, pick in (("batchAB.sh", [n for n in names if "C" not in n[len(a.tag):len(a.tag) + 1]]),
                        ("batchC.sh", [n for n in names if "C" in n[len(a.tag):len(a.tag) + 1]])):
        sh = os.path.join(a.lean_dir, nm_sh)
        if nm_sh == "batchC.sh":      # smallest envelopes first: a budget stop loses the largest, not the most
            pick = sorted(pick, key=lambda n: os.path.getsize(os.path.join(a.lean_dir, n + ".lean")))
        open(sh, "w").write(f"""#!/bin/bash
# ONE slot acquisition (budget 14 min: no chunk is STARTED after 840 s; a chunk that is not started is
# reported SKIPPED, and its blocks stay NOT-RUN in lean.json). Every chunk is its own `lean --json` process
# with its own timeout (a stack overflow or a timeout loses one chunk, not the batch).
# A = loader chunks, B = tactic chunks, C = envelopes > 1.5 MB (one block per chunk).
unset SVGOLF_LEAN_WRAP
cd {a.wt}
date
S=$(date +%s)
for f in {" ".join(pick)}; do
  if [ $(( $(date +%s) - S )) -gt 840 ]; then echo "SKIPPED $f (budget)"; continue; fi
  T=300; case $f in *C[0-9][0-9]) T=240;; esac
  echo "== $f $(date +%T)"
  timeout $T lake env lean --json {a.lean_dir}/$f.lean > {a.lean_dir}/$f.json 2> {a.lean_dir}/$f.err
  echo "exit $? ($f) $(date +%T)"
done
date
""")
        os.chmod(sh, 0o755)
    print({k: len(v) for k, v in files.items()}, "->", a.lean_dir)


def parse(a):
    index = json.load(open(os.path.join(a.lean_dir, "index.json")))
    res = {bid: {"loader": None, "messages": [], "unsupported": None, "first_loud": None, "tactics": {}}
           for bid in index}
    for src in sorted(glob.glob(os.path.join(a.lean_dir, "*[ABC][0-9][0-9].lean"))):
        p = src[:-5] + ".json"
        if not os.path.exists(p):
            continue
        lines = open(src).read().split("\n")
        owner, tac_of = {}, {}
        cur, tk = None, None
        for i, l in enumerate(lines, 1):
            m = re.match(r"namespace RB\.«(.*)»", l)
            if m:
                cur, tk = m.group(1), None
            m = re.match(r'#eval IO.println "RBTAC (\S+) (\S+)"', l)
            if m:
                tk = m.group(2)
            owner[i] = cur
            if tk:
                tac_of[i] = tk
        for raw in open(p, errors="replace"):
            raw = raw.strip()
            if not raw.startswith("{"):
                continue
            try:
                m = json.loads(raw)
            except json.JSONDecodeError:
                continue
            line = m["pos"]["line"] if m.get("pos") else 0
            bid = owner.get(line)
            if bid not in res:
                continue
            txt, sev = m.get("data", ""), m.get("severity")
            if "RBLOAD" in txt and sev == "information":
                mm = re.search(r"RBLOAD \S+ unsupported=(\w+) first=(.*)", txt, re.S)
                if mm:
                    res[bid]["unsupported"] = mm.group(1) == "true"
                    res[bid]["first_loud"] = mm.group(2).strip()
                continue
            if "RBBEGIN" in txt:
                res[bid]["began"] = True
                continue
            if "RBTAC" in txt:
                continue
            entry = {"severity": sev, "line": line, "text": txt.strip()[:2500]}
            if line in tac_of:
                res[bid]["tactics"].setdefault(tac_of[line], []).append(entry)
            else:
                res[bid]["messages"].append(entry)
    for bid, r in res.items():
        r["index"] = index[bid]
        errs = [m for m in r["messages"] if m["severity"] == "error"]
        if errs:
            r["loader"] = "REFUSED" if any("load_design_sv2" in e["text"] for e in errs) else "ERROR"
        elif r["unsupported"] is None:
            r["loader"] = "CRASH-OR-TIMEOUT" if r.get("began") else "NOT-RUN"
        else:
            r["loader"] = "LOADED"
        verdicts = {}
        for kind, msgs in r["tactics"].items():
            terr = [m for m in msgs if m["severity"] == "error"]
            tinfo = [m for m in msgs if m["severity"] == "information"]
            refusal = [m for m in terr if not m["text"].startswith("unsolved goals")]
            if refusal:
                verdicts[kind] = "REFUSED: " + refusal[0]["text"][:400].replace("\n", " ")
            elif tinfo:
                verdicts[kind] = "RECOGNIZED: " + tinfo[0]["text"][:600].replace("\n", " | ")
            elif terr:
                verdicts[kind] = "UNSOLVED-ONLY"
            else:
                verdicts[kind] = "NO-OUTPUT"
        r["tactic"] = verdicts or None
    json.dump(res, open(os.path.join(a.out, a.lean_out), "w"), indent=1, sort_keys=True)
    import collections
    print(collections.Counter(r["loader"] for r in res.values()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["gen", "parse"])
    ap.add_argument("--out", required=True)
    ap.add_argument("--lean-dir", required=True)
    ap.add_argument("--wt", default=os.getcwd())
    ap.add_argument("--only-suffix", default=None, help="gen: only ids ending with this (e.g. @wa3)")
    ap.add_argument("--ids", default=None, help="gen: also these exact ids")
    ap.add_argument("--tag", default="", help="gen: prefix of the chunk names (default none: A/B/C)")
    ap.add_argument("--lean-out", default="lean.json", help="parse: output file name inside --out")
    a = ap.parse_args()
    {"gen": gen, "parse": parse}[a.cmd](a)


if __name__ == "__main__":
    main()

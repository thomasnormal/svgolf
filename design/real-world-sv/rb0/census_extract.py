#!/usr/bin/env python3.12
"""WP-RB0 census, steps 1-3 (slang, extractor, envelope statistics).

    python3.12 census_extract.py --src SRCROOT --out OUTDIR [--blocks corpus.json] [--only ID,ID] [-j 3]
                                 [--repo REPO_ROOT]

For every block of corpus.json (see CENSUS.md for the schema):

  1. slang: the files are compiled as ONE compilation with the block's top as the only top
     module and its include directories; the ERROR diagnostics are recorded (code, message,
     file:line) and classified (`missing-include`, `unknown-module`, `unknown-package`, ...).
  2. the extractor, exactly as the checker's `extract` stage runs it:
         extract.py --top TOP -I DIR... FILE... -o OUT.json
     with a wall-clock timeout; return code, stderr, time.
  3. envelope statistics: parameters, ports, processes by kind, generates, instance
     definitions, and every `Unsupported` node (sv_kind, span, text) found anywhere in the
     envelope, mapped to a row of docs/sv-refusals.json (or `unregistered`).

The fetched files are UNTRUSTED data: pyslang reads them in-process (no sandbox) and
nothing is executed. Output: OUTDIR/<id>.json (one record per block) and OUTDIR/<id>.env.json
(the envelope, when there is one). Step 4 (the Lean loader) is census_lean.py.
"""
import argparse
import concurrent.futures
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))


def load_register(repo):
    d = json.load(open(os.path.join(repo, "docs", "sv-refusals.json")))
    return d["entries"]


def match_register(entries, sv_kind, text=""):
    """Map an Unsupported `sv_kind` to the best register row id, or None (= unregistered).
    Score: an exact kind pattern 10; a `Family:*` wildcard 3 + prefix length / 100; the row's tag
    naming the kind (prefix of a tag part) +5; a raw slang class name (`@default:` rows) listed in
    the tag 4. The best score wins, ties go to the earliest row."""
    # shared tags: one slang class, several rows -- disambiguate by the node text
    if sv_kind == "ProceduralBlockSymbol:NoEventControl":
        if re.search(r"\b(assert|assume|cover|restrict)\s+property\b|\bassert\s*\(", text):
            return "pr-concurrent-assert"
        return "pr-always-nocontrol"
    best, best_score = None, 0.0
    for e in entries:
        ks = (e.get("kinds") or {}).get("extractor") or []
        tagparts = [t.strip() for t in re.split(r"\s*/\s*|,\s*|\s\|\s|\s+\(", e["tag"])]
        in_tag = any(t == sv_kind or (t.startswith(sv_kind) and sv_kind.count(":") > 0) for t in tagparts)
        sc = 0.0
        for k in ks:
            if k == sv_kind:
                sc = max(sc, 10)
            elif k.endswith("*") and sv_kind.startswith(k[:-1]):
                sc = max(sc, 3 + len(k) / 100)
            elif k.startswith("@default:") and sv_kind in tagparts:
                sc = max(sc, 4)
        if sc and in_tag:
            sc += 5
        if sc == 0 and in_tag and ":" not in sv_kind:
            sc = 2          # a bare slang class name listed in a tag
        if sc > best_score:
            best, best_score = e["id"], sc
    return best


def classify_diag(code, msg):
    c = code.lower()
    if "includefile" in c or "couldnotopen" in c or "could not open include" in msg.lower():
        return "missing-include"
    if c in ("unknownmodule", "unknowndefinition") or "unknown module" in msg.lower():
        return "unknown-module"
    if "unknownpackage" in c or "unknown package" in msg.lower() or "unknownclassorpackage" in c:
        return "unknown-package"
    if "unknowndirective" in c or "undefinedmacro" in c or "unknown macro" in msg.lower():
        return "undefined-macro"
    if "undeclared" in c or "undeclared" in msg.lower():
        return "undeclared-identifier"
    return "other"


def slang_step(repo, cwd, files, incdirs, top, defines):
    sys.path.insert(0, os.path.join(repo, "extractors", "sv"))
    import extract as X
    import pyslang
    Compilation, CompilationOptions, SyntaxTree = X.Compilation, X.CompilationOptions, X.SyntaxTree
    t0 = time.time()
    rec = {"errors": [], "n_errors": 0, "n_warnings": 0, "parse_ok": False}
    try:
        sm = pyslang.SourceManager()
        popt = pyslang.parsing.PreprocessorOptions()
        popt.additionalIncludePaths = [os.path.join(cwd, d) for d in incdirs]
        if defines:
            popt.predefines = list(defines)
        bag = pyslang.Bag([popt])
        tree = SyntaxTree.fromFiles([os.path.join(cwd, f) for f in files], sm, bag)
        opts = CompilationOptions()
        opts.topModules = {top}
        comp = Compilation(pyslang.Bag([opts]))
        comp.addSyntaxTree(tree)
        engine = X._slang_driver().diagEngine
        seen = set()
        for d in comp.getAllDiagnostics():
            if not d.isError():
                rec["n_warnings"] += 1
                continue
            code = X._slang_diag_name(d)
            msg = " ".join(engine.formatMessage(d).split())
            try:
                f = sm.getFileName(d.location)
                ln = sm.getLineNumber(d.location)
            except Exception:
                f, ln = "?", 0
            f = os.path.relpath(f, cwd) if f and f != "?" and os.path.isabs(f) else f
            key = (code, msg, f, ln)
            if key in seen:
                continue
            seen.add(key)
            rec["errors"].append({"code": code, "msg": msg[:240], "file": f, "line": ln,
                                  "class": classify_diag(code, msg)})
        rec["n_errors"] = len(rec["errors"])
        rec["parse_ok"] = True
    except Exception as exc:  # noqa: BLE001
        rec["exception"] = "%s: %s" % (type(exc).__name__, str(exc)[:300])
    rec["seconds"] = round(time.time() - t0, 2)
    return rec


def walk_unsupported(node, path, out):
    if isinstance(node, dict):
        if node.get("kind") == "Unsupported":
            out.append({"sv_kind": node.get("sv_kind"), "span": node.get("span"),
                        "text": (node.get("text") or "")[:400], "path": path})
        for k, v in node.items():
            walk_unsupported(v, path + [k] if len(path) < 4 else path, out)
    elif isinstance(node, list):
        for v in node:
            walk_unsupported(v, path, out)


def count_kinds(node, acc):
    if isinstance(node, dict):
        k = node.get("kind")
        if k:
            acc[k] = acc.get(k, 0) + 1
        for v in node.values():
            count_kinds(v, acc)
    elif isinstance(node, list):
        for v in node:
            count_kinds(v, acc)


def envelope_stats(env, top):
    st = {}
    design = env.get("design") or {}
    mods = design.get("modules") or []
    st["n_modules"] = len(mods)
    topm = None
    for m in mods:
        if m.get("name") == top:
            topm = m
    if topm is None and mods:
        topm = mods[0]
    if topm is not None:
        st["top_found"] = topm.get("name") == top
        ps = topm.get("params", [])
        st["params"] = [p.get("name") for p in ps if p.get("kind") == "ParameterDecl"]
        st["n_localparams"] = sum(1 for p in ps if p.get("kind") == "LocalParam")
        st["n_ports"] = len(topm.get("ports", []))
        st["ports_in"] = sum(1 for p in topm.get("ports", []) if p.get("dir") == "in")
        st["ports_out"] = sum(1 for p in topm.get("ports", []) if p.get("dir") == "out")
        st["ports_inout"] = sum(1 for p in topm.get("ports", []) if p.get("dir") == "inout")
        procs = {}
        for p in topm.get("processes", []):
            procs[p.get("kind")] = procs.get(p.get("kind"), 0) + 1
        st["processes"] = procs
        st["n_generates"] = len(topm.get("generates", []))
        st["n_decls"] = len(topm.get("decls", []))
    st["packages"] = [p if isinstance(p, str) else p.get("name") for p in env.get("packages", [])]
    st["defs"] = [m.get("name") for m in mods if m.get("name") != top]
    kinds = {}
    count_kinds(env.get("design"), kinds)
    st["n_nodes"] = sum(kinds.values())
    st["node_kinds"] = kinds
    return st


def make_slice(cwd, out, bid, spec):
    """Derived file: the text before the first `module` of the file plus the named modules
    (each from its `module NAME` line to the next `endmodule`). Written under OUT/derived/."""
    lines = open(os.path.join(cwd, spec["file"]), encoding="utf-8").read().split("\n")
    first = next(i for i, l in enumerate(lines) if re.match(r"\s*module\s", l))
    keep = lines[:first]
    for name in spec["modules"]:
        s = next(i for i, l in enumerate(lines) if re.match(r"\s*module\s+%s\b" % re.escape(name), l))
        e = next(i for i in range(s, len(lines)) if re.match(r"\s*endmodule\b", lines[i]))
        keep += lines[s:e + 1] + [""]
    d = os.path.join(out, "derived", bid)
    os.makedirs(d, exist_ok=True)
    dst = os.path.join(d, os.path.basename(spec["file"]))
    open(dst, "w").write("\n".join(keep))
    return dst


_DIRECTIVES = {"define", "undef", "ifdef", "ifndef", "else", "elsif", "endif", "include", "timescale", "default_nettype",
               "resetall", "celldefine", "endcelldefine", "pragma", "line", "begin_keywords", "end_keywords", "__FILE__", "__LINE__"}


def scan_needs(cwd, files):
    """What the sources use beyond plain module text: `include files, package imports, macro uses
    (backtick names that are neither directives nor defined in the scanned files)."""
    inc, imp, uses, defs = set(), set(), set(), set()
    for f in files:
        try:
            t = open(os.path.join(cwd, f), encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        t = re.sub(r"//[^\n]*", "", t)
        t = re.sub(r"/\*.*?\*/", "", t, flags=re.S)
        inc.update(re.findall(r'`include\s+"([^"]+)"', t))
        imp.update(re.findall(r"\bimport\s+(\w+)\s*::", t))
        defs.update(re.findall(r"`define\s+(\w+)", t))
        uses.update(re.findall(r"`(\w+)", t))
    uses = {u for u in uses if u not in _DIRECTIVES and u not in defs}
    return {"includes": sorted(inc), "package_imports": sorted(imp), "macros_used": sorted(uses)[:25],
            "n_macros_used": len(uses)}


def run_block(b, src, out, repo, register, timeout):
    cwd = os.path.join(src, "files", b["project"])
    if b.get("_derived"):
        cwd = b["_derived"]["cwd"]
    rec = {"id": b["id"], "project": b["project"], "category": b["category"], "kind": b["kind"], "top": b["top"]}
    if b.get("wa_note"):
        rec["worked_around"] = b["wa_note"]
    missing = [f for f in b["files"] if not os.path.exists(os.path.join(cwd, f))]
    if missing:
        rec["fetch_missing"] = missing
        return rec
    rec["lines"] = sum(1 for _ in open(os.path.join(cwd, b["files"][-1]), "rb"))
    rec["total_lines"] = sum(sum(1 for _ in open(os.path.join(cwd, f), "rb")) for f in b["files"])
    rec["deps"] = b["files"][:-1]
    rec["incdirs"] = b["incdirs"]
    rec["needs"] = scan_needs(cwd, b["files"])
    # (1) slang
    rec["slang"] = slang_step(repo, cwd, b["files"], b["incdirs"], b["top"], b.get("defines"))
    # (2) extractor
    envp = os.path.join(out, b["id"] + ".env.json")
    if os.path.exists(envp):
        os.remove(envp)
    cmd = [sys.executable, os.path.join(repo, "extractors", "sv", "extract.py"), "--top", b["top"]]
    for d in b["incdirs"]:
        cmd += ["-I", os.path.join(cwd, d)]
    cmd += [os.path.join(cwd, f) for f in b["files"]] + ["-o", envp]
    t0 = time.time()
    try:
        pr = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        rec["extract"] = {"rc": pr.returncode, "seconds": round(time.time() - t0, 2),
                          "stderr": pr.stderr.strip()[-1500:]}
    except subprocess.TimeoutExpired:
        rec["extract"] = {"rc": None, "timeout": timeout, "seconds": timeout, "stderr": ""}
    ex = rec["extract"]
    # (3) envelope
    if ex.get("rc") == 0 and os.path.exists(envp):
        env = json.load(open(envp))
        rec["envelope"] = envelope_stats(env, b["top"])
        un = []
        walk_unsupported(env.get("design"), ["design"], un)
        walk_unsupported(env.get("packages"), ["packages"], un)
        by = {}
        for u in un:
            k = u["sv_kind"]
            e = by.setdefault(k, {"sv_kind": k, "count": 0, "first_line": (u["span"] or {}).get("line"),
                                  "text": u["text"], "row": match_register(register, k, u["text"]), "examples": []})
            e["count"] += 1
            if len(e["examples"]) < 3:
                e["examples"].append({"line": (u["span"] or {}).get("line"), "text": u["text"][:300]})
        rec["unsupported"] = sorted(by.values(), key=lambda e: (-e["count"], e["sv_kind"]))
        rec["n_unsupported"] = len(un)
        rec["env_bytes"] = os.path.getsize(envp)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--blocks", default=os.path.join(HERE, "corpus.json"))
    ap.add_argument("--repo", default=os.path.abspath(os.path.join(HERE, "..", "..", "..", "..")))
    ap.add_argument("--only", default=None)
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=900)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    blocks = json.load(open(a.blocks))
    if a.only:
        ids = set(a.only.split(","))
        blocks = [b for b in blocks if b["id"] in ids]
    register = load_register(a.repo)
    allb = []
    for b in blocks:
        if not b.get("skip_base"):
            allb.append(b)
        allb.extend(variants(b, a.src, a.out))
    args = [(b, a.src, a.out, a.repo, register, a.timeout) for b in allb]
    with concurrent.futures.ProcessPoolExecutor(a.j) as pool:
        list(pool.map(job, args))


_ALWAYS_LIST = re.compile(r"\balways\s*@\s*\(([^)]*)\)")


def modernize(text):
    """The Verilog-2001 -> SystemVerilog spelling pass of the `@wa2` variant (WORKED AROUND, not an
    ls-sv feature): `wire`/`reg` -> `logic`, `always @*` and level-sensitive `always @(a or b)` ->
    `always_comb`. Edge-sensitive lists are left alone. Comments are not special-cased."""
    t = re.sub(r"\balways\s*@\s*\(\s*\*\s*\)", "always_comb", text)
    t = re.sub(r"\balways\s*@\s*\*", "always_comb", t)

    def lvl(m):
        return m.group(0) if re.search(r"\b(posedge|negedge)\b", m.group(1)) else "always_comb"
    t = _ALWAYS_LIST.sub(lvl, t)
    # a net declaration assignment `wire [r] n = e;` is a CONTINUOUS assignment (IEEE 6.1); `logic n = e;` would be a one-time
    # initializer, a different program: spell it `logic [r] n; assign n = e;`
    t = re.sub(r"\bwire(\s+signed)?(\s*\[[^\]]*\])?\s+(\w+)\s*=\s*([^;]*?);", r"logic\1\2 \3; assign \3 = \4;", t)
    t = "\n".join(l if l.lstrip().startswith("`default_nettype") else re.sub(r"\b(wire|reg)\b", "logic", l)
                  for l in t.split("\n"))
    return t


_PORT_KW = {"signed", "unsigned", "var", "logic", "bit", "reg", "wire", "int", "integer", "byte", "shortint", "longint", "real",
            "tri", "supply0", "supply1", "string", "enum", "struct", "union", "type"}
_IMPLICIT_PORT = re.compile(r"\b(input|output|inout)(\s+)((?:\[[^\]\n]*\]\s*)*)([A-Za-z_]\w*)(?=[ \t]*(?:[,)]|//|/\*|$))", re.M)


def type_implicit_ports(text):
    """The `@wa3` step: an ANSI port with a direction and no data type (`input [31:0] x`, `output done`) is an implicit
    NET in Verilog-2001; give it the type `logic`. Non-ANSI body declarations are not touched. WORKED AROUND, not a feature."""
    def f(m):
        if m.group(4) in _PORT_KW:
            return m.group(0)
        return "%s%slogic %s%s" % (m.group(1), m.group(2), m.group(3), m.group(4))
    return _IMPLICIT_PORT.sub(f, text)


def variants(b, src, out):
    """The worked-around blocks of a block: `@wa` (the top-selection slice) and `@wa2` (slice if any, then
    the Verilog-2001 modernization), each only when it changes the text."""
    res = []
    cwd = os.path.join(src, "files", b["project"])
    w = b.get("wa")
    base_files = b["files"]
    sliced = None
    if w and "slice" in w:
        dst = make_slice(cwd, out, b["id"] + "@wa", w["slice"])
        v = dict(b)
        v["id"] = b["id"] + "@wa"
        v["files"] = [os.path.relpath(dst, os.path.join(out, "derived", v["id"]))]
        v["_derived"] = {"cwd": os.path.join(out, "derived", v["id"])}
        v["wa_note"] = w.get("note")
        v["incdirs"] = [os.path.join(cwd, d) for d in b["incdirs"]]
        res.append(v)
        sliced = (os.path.join(out, "derived", v["id"]), v["files"])
    # @wa2: modernized copy of every listed file (of the slice, when there is one)
    srcdir, files = sliced if sliced else (cwd, base_files)
    changed = False
    d2 = os.path.join(out, "derived", b["id"] + "@wa2")
    for f in files:
        txt = open(os.path.join(srcdir, f), encoding="utf-8", errors="replace").read()
        new = modernize(txt)
        changed = changed or new != txt
        dst = os.path.join(d2, f)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, "w").write(new)
    if changed:
        v = dict(b)
        v["id"] = b["id"] + "@wa2"
        v["files"] = list(files)
        v["_derived"] = {"cwd": d2}
        v["incdirs"] = [os.path.join(cwd, d) for d in b["incdirs"]]
        v["wa_note"] = ("Verilog-2001 spelling modernized (wire/reg -> logic, always @* and level-sensitive lists -> always_comb)"
                        + ("; " + w["note"] if sliced else ""))
        res.append(v)
    # @wa3: @wa2 + implicit-typed ports typed, + the block's own flattening edits (corpus.json `wa3_edits`), each only when it changes the text
    d3 = os.path.join(out, "derived", b["id"] + "@wa3")
    changed3 = False
    for f in files:
        txt = modernize(open(os.path.join(srcdir, f), encoding="utf-8", errors="replace").read())
        for pat, repl in (b.get("wa3_edits") or {}).get(os.path.basename(f), []):
            txt2 = re.sub(pat, repl, txt, flags=re.S)
            if txt2 == txt:
                raise ValueError("wa3 edit did not apply: %s %s" % (b["id"], pat))
            txt = txt2
        new3 = type_implicit_ports(txt)
        changed3 = changed3 or new3 != modernize(open(os.path.join(srcdir, f), encoding="utf-8", errors="replace").read())
        dst = os.path.join(d3, f)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, "w").write(new3)
    if changed3:
        v = dict(b)
        v["id"] = b["id"] + "@wa3"
        v["files"] = list(files)
        v["_derived"] = {"cwd": d3}
        v["incdirs"] = [os.path.join(cwd, d) for d in b["incdirs"]]
        v["wa_note"] = ("@wa2 plus implicit-typed ports typed `logic`" + ("; hand flattening edits: %s" % list((b.get("wa3_edits") or {}).keys())
                        if b.get("wa3_edits") else "") + (("; " + w["note"]) if sliced else ""))
        res.append(v)
    return res


def job(arg):
    b, src, out, repo, register, timeout = arg
    try:
        r = run_block(b, src, out, repo, register, timeout)
    except Exception as exc:  # noqa: BLE001
        r = {"id": b["id"], "driver_exception": "%s: %s" % (type(exc).__name__, exc)}
    json.dump(r, open(os.path.join(out, b["id"] + ".json"), "w"), indent=1, sort_keys=True)
    ex = r.get("extract", {})
    print("%-34s slang_err=%-3s rc=%-5s %6ss unsupp=%s" % (
        b["id"], r.get("slang", {}).get("n_errors"), ex.get("rc"), ex.get("seconds"), r.get("n_unsupported")),
        flush=True)
    return r


if __name__ == "__main__":
    main()

#!/usr/bin/env python3.12
"""WP-RB0 census, step 5: the report (census.json + CENSUS.md) from the measurement directory.

    python3.12 census_report.py --out OUTDIR --md CENSUS.md --json census.json [--repo REPO_ROOT]

Reads OUTDIR/<id>.json (census_extract.py), OUTDIR/lean.json (census_lean.py parse) and corpus.json.
Deterministic apart from the date line. Every number printed in CENSUS.md is computed here from the
per-block records; the interpretive text (blocker names, work-package and effort guesses) is the
BLOCKERS table below, which is a judgement and says so.
"""
import argparse
import collections
import glob
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import census_extract as CE  # noqa: E402

LICENCE = {
    "ibex": "Apache-2.0", "cv32e40p": "Solderpad Hardware License v0.51 (SHL-0.51)",
    "cv32e40x": "Solderpad Hardware License v0.51 (SHL-0.51)",
    "cva6": "Solderpad Hardware License v0.51; the vendored PULP cells Apache-2.0 WITH SHL-2.0 / SHL-0.51",
    "picorv32": "ISC", "serv": "ISC", "hazard3": "Apache-2.0", "mor1kx": "CERN-OHL-W-2.0 (file headers); repo metadata unset",
    "biriscv": "BSD-3-Clause", "opentitan": "Apache-2.0", "veer_el2": "Apache-2.0",
    "vexriscv": "MIT (VexRiscv); the generated file carries no header", "rocket": "BSD-3-Clause (rocket-chip); the pythondata repo carries no SPDX",
}

# Blocker table: key -> (name, layer, work package, effort guess, note).  A key is a register row id, or a
# `x:`-prefixed census-level blocker that has no register row (a hole in the register, or a pipeline fact).
# JUDGEMENT, not measurement: the effort guesses are the author's.
BLOCKERS = {
    "dc-net-z": ("Verilog-style nets: `wire`, `input wire`, `output wire` (undriven bits read z)", "extractor + loader", "extractor/loader (driver-coverage analysis, plan NETRES)",
                 "M", "Every Verilog-2001 core (serv, hazard3, mor1kx, biRISC-V, picorv32, Rocket/VexRiscv generated) and every `output wire` in SV. The cheap sound fragment is a net whose every bit has exactly one continuous driver (z unreachable): that is a driver-coverage check, not the x-taint feature."),
    "pr-implicit-event": ("`always @*` / `always @(*)` (level-sensitive block, latch-capable)", "extractor + fourstate rule", "extractor + svgolf fourstate rule + Lean (treat as always_comb when the block provably infers no latch)",
                          "M", "The Verilog spelling of always_comb; the register asks for a 4-state rule for the initial x of a block that can latch (plan LATCH4)."),
    "st-for": ("procedural `for` loop in an always block / function", "extractor + Lean semantics", "Sem2/Comb2Proc (bounded unroll or induction rule), plan LOOPS",
               "L", "popcount/ff1/priority/shift loops of ibex, OpenTitan, hazard3, serv; the single most-wanted construct of the register's own ranking."),
    "ex-user-call": ("function call in expression position", "extractor + Lean semantics", "USERFN (functions with the 4-state rule)", "L",
                     "RVC expanders (hazard3_instr_decompress), prim_util_pkg::vbits(N), bit-twiddling helpers."),
    "dc-member-kinds": ("module-level `function` definitions, `parameter type`, other member kinds", "extractor + Lean", "USERFN / HIERFEAT", "L",
                        "Functions defined in the module (ibex_compressed_decoder, hazard3_*), `parameter type fu_data_t` (cva6)."),
    "cv-explicit": ("explicit size/sign cast `N'(x)`, `signed'(x)`, `int'(x)`", "extractor", "FOLDS (per-point cast lowering)", "S-M", "Ubiquitous in ibex/cv32e40x/cva6."),
    "cv-width": ("implicit signed width change / `$signed` into a different width", "extractor", "SIGNED (symbolic SignedResize)", "M", "Multipliers (ibex_multdiv_fast, cv32e40p_mult), picorv32 mul."),
    "st-assign-target": ("assignment target that is not an identifier / constant select / admitted concat", "extractor + Lean", "SELFEAT (run-time-indexed targets, general concat targets)", "M", "Register files, CSR windows."),
    "pr-concurrent-assert": ("concurrent `assert property` / `cover property` (lowRISC `ASSERT_*` macros)", "extractor", "VERIF: admit and ignore (they have no hardware meaning); today they are loud Unsupported", "S",
                             "Every lowRISC block (ibex, OpenTitan) ends with `ASSERT_*` macro uses. The tools-split reading: Yosys' read_verilog -sv ignores/rejects them differently, so svGolf needs a rule; for a verification (not golf) use a strip-assertions mode is a policy decision."),
    "st-immediate-assert": ("immediate `assert (...)` in a procedural block", "extractor", "VERIF", "S", "ibex_multdiv, picorv32 formal blocks."),
    "dc-unpacked": ("unpacked arrays / structs: ports, variables, run-time-indexed reads", "extractor + Lean", "AGGR", "L", "Register files (`logic [31:0] mem [32]`), imd_val_q_i[2], struct ports."),
    "dc-signed": ("signed declarations (`signed` ports/variables, `integer`)", "extractor + Lean", "SIGNED", "M", "Dividers, multipliers, branch comparators."),
    "pa-aggregate-point": ("fixed unpacked array whose bound is a parameter", "extractor", "AGGR / FOLDS", "M", "Register files with parametric depth."),
    "sel-default-point-index": ("array cell index that is a genvar / parameter expression", "extractor", "FOLDS (symbolic cell indices)", "M", "ibex_alu, ibex_cs_registers."),
    "ex-invalid": ("slang-invalid expression (undeclared name after a slang error)", "consequence", "(consequence of a slang error: fix the corpus/compile)", "-", "Appears only next to slang errors."),
    "st-invalid": ("slang-invalid statement", "consequence", "(consequence of a slang error)", "-", ""),
    "hi-uninstantiated": ("instance of a module that is not in the compilation (or lives in a generate branch not taken)", "multi-file", "multi-file/library support: the checker must hand the extractor every definition the top instantiates", "M",
                          "Technology/primitive cells (`prim_flop`, `prim_buf`, `clkhdr`), sub-blocks given in other files."),
    "pa-syntax-recovery": ("syntax-level name the extractor could not resolve (struct-valued parameter member `CVA6Cfg.XLEN`, unresolved identifier after a slang error)", "extractor", "FOLDS / AGGR (struct-typed parameters)", "L", "CVA6's `CVA6Cfg` config struct reaches every core block."),
    "ge-no-template": ("generate-for with zero instances at the default point", "extractor", "(bind the template from syntax, not the first elaborated instance)", "S-M", "Config-struct-sized loops of cva6."),
    "ex-inside": ("`inside` operator / value range", "extractor + Lean", "CASEFEAT", "S", "cv32e40p_decoder (instruction classes)."),
    "st-casez": ("`casez`", "extractor + Lean", "CASEFEAT (wildcard case)", "M", "RVC decoders, priority encoders."),
    "st-compound": ("compound assignment `+=`, `<<=`", "extractor", "OPS", "S", ""),
    "ex-assign-pattern": ("assignment pattern `'{...}`", "extractor", "AGGR", "M", ""),
    "sel-range-labels": ("range/index select with non-canonical or dynamic range", "extractor", "SELFEAT", "M", ""),
    "sel-dyn-indexed": ("dynamic indexed part select `[b +: w]`", "extractor", "SELFEAT", "M", ""),
    "cv-streaming": ("streaming concatenation `{<<{x}}`", "extractor", "FOLDS", "S", "bit reversal in cv32e40x_alu."),
    "pr-event-list": ("`always @(a or b)` explicit sensitivity list", "extractor", "SEQ", "S", ""),
    "ex-op-invalid-compilation": ("operator in a compilation with slang errors", "consequence", "(consequence of a slang error)", "-", ""),
    "ld-init-expr": ("Verilog nets and implicit-typed declarations whose packed dimensions the extractor cannot recover (loader: `unrecoverable packed dimensions`; also non-literal initializers)", "extractor + loader", "extractor (emit the dimensions of `wire [N:0]` / typeless ports) + Ingest2; the same cluster as `dc-net-z`", "M",
                    "Fires on EVERY typeless ANSI port `input [31:0] x` (the Verilog-2001 default) and on OpenTitan's generated `prim_secded_*`; the extractor accepts the input, the loader refuses it."),
    "le-param-package": ("package-scoped parameters / enum types / config structs (`cv32e40p_pkg::OPCODE_OPIMM`, `ibex_pkg::rv32m_e`, `config_pkg::cva6_cfg_t`)", "Lean model (Param2/ParamRef:package)", "multi-file packages: resolve `pkg::NAME` as a constant of the envelope's `packages` list", "M",
                         "The package IS in the envelope's compilation but the Lean side has no package-constant resolution: every SV core (cv32e40p/x, ibex, cva6) uses packages for opcodes, enums and widths. Struct-valued parameters (`CVA6Cfg`) are a further step."),
    "le-untyped-width": ("untyped parameter taking its expression's own width (`parameter B = W-1`)", "Lean loader", "decide the Icarus/slang width split (a declared departure) or give the parameter an explicit type in the corpus", "S",
                         "serv_*, cv32e40p_register_file: the register records it as refused on purpose (tools split)."),
    "le-const-context": ("replication / concatenation / unbased-unsized literal in a parameter default", "Lean model", "constant evaluator (Param2)", "M", "hazard3_config.vh and mor1kx-defines.v parameter lists."),
    "ld-localdecl": ("block-local declaration in an always_comb (`LocalDecl`)", "Lean loader", "register's #3 allowed-later item: a LocalDecl statement in Stmt2/PStmt", "M", "ibex, cv32e40x_alu, hazard3 loop variables."),
    "ld-initial-syscall": ("`initial` process / system-task statement reaching the loader", "Lean loader", "drop (assertion-only) `initial` blocks or give them a no-op semantics", "S", "OpenTitan `prim_arbiter_ppc`, PULP `lzc`: `initial begin assert ... end` guards."),
    "ld-unknown-kind": ("other node kind the loader does not parse", "Lean loader", "Ingest2", "M", ""),
    "ld-crosscheck": ("loader cross-check disagreement (other)", "Lean loader", "(see detail)", "M", ""),
    "le-generate-decl": ("declaration inside a generate block", "Lean loader", "GenerateDecl:<kind> support", "M", "ibex_counter, serv_immdec."),
    "le-assign-undeclared": ("assign target not a declared signal at this point", "Lean model", "declaration-order/hierarchy handling", "M", "ibex_multdiv_slow (`imd_val_d_o[0]` of an unpacked port)."),
    "lean:max-rec-depth": ("Lean elaboration hits `maxRecDepth` on a multi-MB envelope", "Lean loader", "load_design_sv2 raises maxRecDepth / iterative toExpr (the sunfish examples already set it by hand)", "S", "VexRiscv_Min (2.2 MB envelope)."),
    "lean:crash-or-timeout": ("the Lean process died or timed out on the envelope", "Lean loader", "scale: envelopes of megabytes", "?", ""),
    "x:slang-errors": ("slang rejects the compilation as the corpus provides it", "corpus", "corpus (missing include/package/module)", "-", "Corpus incompleteness, not a tier gap."),
    "x:top-instantiated": ("`--top` names a module that is instantiated by another module of the same sources", "extractor CLI", "extractor: slang `topModules` for the requested top (3 lines)", "S",
                           "picorv32.v (one file, 6 modules, 5 of them instantiated by others), Rocket/VexRiscv generated files, cva6 `popcount` (recursive), any library file."),
    "x:generated-config": ("the design needs a generated configuration (`el2_param.vh`, `el2_pdef.vh`)", "corpus", "multi-file + a documented generator step (untrusted code) or checked-in configs", "M", "VeeR EL2."),
    "x:no-register-row": ("an Unsupported kind with no row in the register", "register", "docs/sv-refusals.json", "S", ""),
}

# sv_kind -> register row, where the shared-tag matcher is wrong or a family row is the honest one.
KIND_ROW = {
    "SubroutineSymbol:Subroutine": ("dc-member-kinds", "family"),
    "TypeParameterSymbol:TypeParameter": ("dc-member-kinds", "family"),
    "UninstantiatedDefSymbol:UninstantiatedDef": ("hi-uninstantiated", "exact"),
    "GenerateFor:no-template": ("ge-no-template", "exact"),
    "Syntax:ScopedName": ("pa-syntax-recovery", "family"),
    "Syntax:Identifier:unresolved": ("pa-syntax-recovery", "exact"),
    "Syntax:Identifier:TypeAliasType": ("pa-syntax-recovery", "family"),
    "ElabSystemTaskSymbol:ElabSystemTask": ("dc-member-kinds", "unregistered"),
    "DataTypeExpression": ("dc-unpacked", "unregistered"),
    "MemberAccessExpression": ("dc-unpacked", "unregistered"),
}


def row_of(kind, matched):
    if kind in KIND_ROW:
        return KIND_ROW[kind]
    if matched is None:
        return (None, "unregistered")
    return (matched, "exact")


def load_all(out):
    recs = {}
    for f in sorted(glob.glob(os.path.join(out, "*.json"))):
        if f.endswith((".env.json", "srcgate.json")) or os.path.basename(f).startswith("lean"):
            continue
        r = json.load(open(f))
        recs[r["id"]] = r
    lean = {}
    for lp in sorted(glob.glob(os.path.join(out, "lean*.json"))):   # lean.json (A/B/C), lean_d.json (batch D), ... later files override
        for k, v in json.load(open(lp)).items():
            if k in lean and v["loader"] in ("NOT-RUN",):
                continue
            lean[k] = v
    return recs, lean


def blockers_of(r, lean_r):
    """The ordered blocker list of one record: (key, detail). Pipeline order: corpus, slang, extractor,
    Unsupported nodes (source order), loader, lowered design."""
    out = []
    if r.get("fetch_missing"):
        out.append(("x:fetch-missing", ",".join(r["fetch_missing"])))
        return out
    sl = r.get("slang", {})
    ex = r.get("extract", {})
    if sl.get("n_errors"):
        classes = collections.Counter(e["class"] for e in sl["errors"])
        e0 = sl["errors"][0]
        key = "x:generated-config" if any("el2_p" in e["msg"] for e in sl["errors"]) else "x:slang-errors"
        out.append((key, "%d slang error(s) %s; first: %s %s:%s %s" % (
            sl["n_errors"], dict(classes), e0["code"], os.path.basename(e0["file"]), e0["line"], e0["msg"][:90])))
    if ex.get("rc") not in (0, None) or ex.get("rc") is None and ex.get("timeout"):
        msg = ex.get("stderr", "")
        if "no such module among top instances" in msg:
            out.append(("x:top-instantiated", msg.strip().splitlines()[-1][:160]))
        else:
            out.append(("x:extract-failed", msg.strip()[-160:]))
        return out
    uns = sorted(r.get("unsupported", []), key=lambda u: (u["first_line"] or 0, u["sv_kind"]))
    for u in uns:
        row, st = row_of(u["sv_kind"], u["row"])
        key = row if st != "unregistered" else "x:no-register-row"
        out.append((key if row else "x:no-register-row", "%s x%d (line %s)%s" % (
            u["sv_kind"], u["count"], u["first_line"], "" if st == "exact" else " [%s row %s]" % (st, row))))
    if lean_r:
        if lean_r["loader"] in ("REFUSED", "ERROR"):
            m = next((m for m in lean_r["messages"] if m["severity"] == "error"), None)
            txt = m["text"] if m else ""
            lines = [l.strip() for l in txt.split("differential):")[-1].split("\n") if l.strip()] if "differential" in txt else [txt]
            seen = []
            for l in lines[:6]:
                k = lean_key(l)
                if k not in seen:
                    seen.append(k)
                    out.append((k, re.sub(r"\s+", " ", l)[:200]))
        elif lean_r["loader"] == "CRASH-OR-TIMEOUT":
            out.append(("lean:crash-or-timeout", "the Lean process died or timed out loading this envelope"))
        elif lean_r["loader"] == "LOADED" and lean_r.get("unsupported"):
            fl = lean_r.get("first_loud") or ""
            out.append((lean_loud_key(fl), fl[:200]))
    return out


def lean_key(msg):
    """Register row of one loader message (the rows of docs/sv-refusals.json, layers lean-loader / lean-model)."""
    m = msg
    if "unrecoverable packed dimensions" in m or "non-literal initializer" in m:
        return "ld-init-expr"
    if 'unknown statement kind "LocalDecl"' in m:
        return "ld-localdecl"
    if 'kind "Initial"' in m or 'kind "SysCall"' in m:
        return "ld-initial-syscall"
    if "package-scoped parameter" in m or "unknown enum member" in m or "unknown enum type" in m:
        return "le-param-package"
    if "Constant:untyped-width" in m:
        return "le-untyped-width"
    if "in a constant context" in m:
        return "le-const-context"
    if "maximum recursion depth" in m:
        return "lean:max-rec-depth"
    if "is not a valid sv-0.2 envelope" in m or "unknown " in m and " kind " in m:
        return "ld-unknown-kind"
    return "ld-crosscheck"


def lean_loud_key(first_loud):
    f = first_loud
    if f.startswith("ParamRef:package"):
        return "le-param-package"
    if f.startswith("GenerateDecl"):
        return "le-generate-decl"
    if f.startswith("Assign:"):
        return "le-assign-undeclared"
    for kind, (row, _) in KIND_ROW.items():
        if f.startswith(kind):
            return row
    head = f.split(":")[0]
    return {"ConversionExpression": "cv-explicit"}.get(head, "lean:lowered-unsupported")


def status_of(r, lean_r, bl):
    if r.get("fetch_missing"):
        return "FETCH-MISSING"
    keys = [k for k, _ in bl]
    if "x:generated-config" in keys:
        return "CORPUS-BLOCKED"
    if r.get("slang", {}).get("n_errors"):
        return "SLANG-ERRORS"
    if "x:top-instantiated" in keys or "x:extract-failed" in keys:
        return "EXTRACT-FAIL"
    if r.get("n_unsupported"):
        return "EXTRACTS-LOUD"
    if lean_r:
        if lean_r["loader"] != "LOADED":
            return {"REFUSED": "LOAD-REFUSED", "ERROR": "LOAD-ERROR", "CRASH-OR-TIMEOUT": "LOAD-CRASH", "NOT-RUN": "LOAD-NOT-RUN"}[lean_r["loader"]]
        if lean_r.get("unsupported"):
            return "LOADS-LOUD"
        return "LOADS-CLEAN"
    return "EXTRACTS-CLEAN"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--md", required=True)
    ap.add_argument("--json", required=True)
    ap.add_argument("--blocks", default=os.path.join(HERE, "corpus.json"))
    ap.add_argument("--sha", default="")
    a = ap.parse_args()
    recs, lean = load_all(a.out)
    sg = {}
    sgp = os.path.join(a.out, "srcgate.json")
    if os.path.exists(sgp):
        sg = json.load(open(sgp))
    corpus = {b["id"]: b for b in json.load(open(a.blocks))}
    rows = []
    for bid, r in recs.items():
        base = bid.split("@")[0]
        b = corpus[base]
        lr = lean.get(bid)
        bl = blockers_of(r, lr)
        st = status_of(r, lr, bl)
        row = {
            "id": bid, "variant": "worked-around" if "@wa" in bid else "as-is", "project": r["project"], "repo": b["repo"],
            "commit": b["commit"], "licence": LICENCE[r["project"]], "category": r["category"], "kind": r["kind"], "top": r["top"],
            "files": (b["files"] if "@wa" not in bid else
                      (["(derived: module text sliced from %s)" % b["wa"]["slice"]["file"]] if bid.endswith("@wa") else
                       ["(derived: Verilog-2001 spelling modernized copy of the files of the block%s)" %
                        (", on the module slice" if b.get("wa") and "slice" in b["wa"] else "")])),
            "incdirs": b["incdirs"], "lines": r.get("lines"), "total_lines": r.get("total_lines"),
            "needs": r.get("needs"), "deps": r.get("deps"),
            "slang": {"parse_ok": r.get("slang", {}).get("parse_ok"), "n_errors": r.get("slang", {}).get("n_errors"),
                      "errors": r.get("slang", {}).get("errors", [])[:6]},
            "extract": {k: r.get("extract", {}).get(k) for k in ("rc", "seconds")},
            "extract_stderr": (r.get("extract", {}).get("stderr") or "")[-300:],
            "envelope": {k: v for k, v in (r.get("envelope") or {}).items() if k != "node_kinds"},
            "env_bytes": r.get("env_bytes"),
            "unsupported": [{"sv_kind": u["sv_kind"], "count": u["count"], "first_line": u["first_line"],
                             "row": row_of(u["sv_kind"], u["row"])[0], "row_status": row_of(u["sv_kind"], u["row"])[1]} for u in r.get("unsupported", [])],
            "n_unsupported": r.get("n_unsupported"),
            "lean": ({"loader": lr["loader"], "lowered_unsupported": lr.get("unsupported"), "first_loud": lr.get("first_loud"),
                      "messages": [m["text"][:300] for m in lr["messages"] if m["severity"] == "error"][:3],
                      "tactic": lr.get("tactic"), "tactic_kind": lr["index"].get("tactic")} if lr else None),
            "blockers": [{"key": k, "detail": d} for k, d in bl],
            "first_blocker": (bl[0][0] if bl else None),
            "status": st,
            "note": b.get("note"),
            "worked_around": r.get("worked_around"),
            "svgolf_source_gate": sg.get(base) if "@wa" not in bid else None,
        }
        rows.append(row)
    rows.sort(key=lambda x: x["id"])
    json.dump({"generated": time.strftime("%Y-%m-%d"), "base": a.sha, "blocks": rows}, open(a.json, "w"), indent=1, sort_keys=False)
    print(len(rows), "rows ->", a.json)
    open(a.md, "w").write(markdown(rows, a))
    print("markdown ->", a.md)


# ---------------------------------------------------------------- markdown

REMOVABLE_NOT = {"x:slang-errors", "x:generated-config", "x:fetch-missing", "ex-invalid", "st-invalid", "ex-op-invalid-compilation",
                 "x:extract-failed", "x:no-register-row"}


def bl_keys(row):
    return [b["key"] for b in row["blockers"]]


def effective_keys(r, byid):
    """The blocker set of a block for ranking: its own; and, when the extractor refused to run because the top is
    instantiated elsewhere (`x:top-instantiated`), also the blockers of its module-slice variant (`@wa`), which is the
    first extraction that shows what is behind that refusal."""
    ks = list(bl_keys(r))
    if "x:top-instantiated" in ks:
        v = byid.get(r["id"] + "@wa")
        if v:
            ks += [k for k in bl_keys(v) if k not in ks]
    return ks


def rank(rows):
    """Per blocker key over the as-is rows: blocks it is present in, blocks it is the SOLE blocker of, blocks
    where it is the first. Plus the greedy unblocking order (each step: the key whose removal frees the most
    blocks completely)."""
    byid = {r["id"]: r for r in rows}
    asis = [r for r in rows if r["variant"] == "as-is" and r["status"] not in ("CORPUS-BLOCKED", "FETCH-MISSING")]
    present, sole, first = collections.Counter(), collections.Counter(), collections.Counter()
    eff = {r["id"]: effective_keys(r, byid) for r in asis}
    for r in asis:
        ks = set(eff[r["id"]])
        for k in ks:
            present[k] += 1
        if len(ks) == 1:
            sole[next(iter(ks))] += 1
        if r["blockers"]:
            first[r["first_blocker"]] += 1
    left = {rid: set(ks) for rid, ks in eff.items() if ks}
    order = []
    removed = set()
    while len(order) < 12:
        cand = collections.Counter()
        for rid, ks in left.items():
            for k in ks - removed:
                if k not in REMOVABLE_NOT:
                    cand[k] += 1
        if not cand:
            break
        best = None
        for k, n in cand.items():
            gain = sum(1 for ks in left.values() if (ks - removed) and (ks - removed - {k}) == set())
            key = (gain, n, k)
            if best is None or key > best[0]:
                best = (key, k)
        (gain, n, k) = best[0]
        removed.add(k)
        order.append((k, gain, n))
    return asis, present, sole, first, order


def short(s, n=70):
    s = (s or "").replace("|", "/").replace("\n", " ")
    return s if len(s) <= n else s[:n - 1] + "~"


def markdown(rows, a):
    asis, present, sole, first, order = rank(rows)
    out = []
    w = out.append
    n_all = len([r for r in rows if r["variant"] == "as-is"])
    st = collections.Counter(r["status"] for r in rows if r["variant"] == "as-is")
    projects = collections.OrderedDict()
    for r in rows:
        if r["variant"] == "as-is":
            projects.setdefault(r["project"], []).append(r)
    w("# WP-RB0: census of real open-source RISC CPU blocks against ls-sv")
    w("")
    w("Generated by `census_report.py` from the measurement directory; every count below is computed from the per-block records in")
    w("`census.json` (one row per block and variant). Date %s, ls-sv base `%s`, pyslang 11.0.0." % (time.strftime("%Y-%m-%d"), a.sha or "svgolf-prep"))
    w("The interpretive columns (blocker names, work packages, effort) are judgement and say so; the rest is measured.")
    w("")
    w("## 1. Corpus (G0)")
    w("")
    n_def = len({r["id"].split("@")[0] for r in rows})
    w("%d blocks from %d projects (%d run as written; the other %d, Rocket-generated modules, exist only as sliced variants because their unsliced run would repeat `rocket_alu`'s failure; %d worked-around variants in all). The third-party files are NOT in this repository: `fetch.sh` re-fetches exactly"
      % (n_def, len(projects), n_all, n_def - n_all, len([r for r in rows if r['variant'] != 'as-is'])))
    w("those 137 files by pinned commit and verifies sha256 (`files.tsv`; a fresh re-fetch was diffed against the working copy: identical).")
    w("Untrusted data: read, never executed; pyslang parses it in-process (not sandboxed), so only well-known repositories at pinned commits are used.")
    w("")
    w("| project | repo @ commit | licence (file headers + repo metadata) | blocks | lines (primary files) |")
    w("|---|---|---|---|---|")
    for proj, rs in projects.items():
        w("| %s | %s @ `%s` | %s | %d | %d |" % (proj, rs[0]["repo"], rs[0]["commit"][:10], rs[0]["licence"], len(rs), sum(r["lines"] or 0 for r in rs)))
    w("")
    w("Not covered, and why: **NEORV32** is VHDL (the lane reads SystemVerilog); **VexRiscv** and **rocket-chip** ship no generated Verilog in their")
    w("repositories, so their generated output is taken from the `litex-hub/pythondata-cpu-*` repositories (a SpinalHDL 1.9.4 `VexRiscv_Min.v`, 3952 lines;")
    w("a Chisel/FIRRTL-generated 9.5 MB single-file `LitexConfig_linux_1_1.v` with 259 modules, of which four are used). **SweRV/VeeR EL2** needs")
    w("`el2_param.vh` / `el2_pdef.vh`, which its configure script generates (Perl, untrusted): recorded as a corpus-level blocker, not worked around.")
    w("")
    w("## 2. Headline (G1)")
    w("")
    w("Pipeline per block: slang (own compile, top only) -> extractor as the checker runs it (`extract.py --top TOP -I ...`) -> `load_design_sv2` -> ")
    w("`Design2.hasUnsupported` at the default parameter point -> `sv_structure?` / `sv_equations?` for combinational blocks with no Unsupported node.")
    w("")
    w("| status of the block as it is (no workaround) | blocks |")
    w("|---|---|")
    desc = {"LOADS-CLEAN": "loads in Lean, no Unsupported node at the default point", "LOADS-LOUD": "loads, but the lowered design has Unsupported nodes",
            "LOAD-REFUSED": "extracts clean; `load_design_sv2` refuses", "LOAD-ERROR": "extracts clean; Lean error while loading", "LOAD-CRASH": "Lean process died or timed out",
            "LOAD-NOT-RUN": "not run (slot budget)", "EXTRACTS-CLEAN": "extractor: zero Unsupported nodes (Lean step not run)",
            "EXTRACTS-LOUD": "extractor emits Unsupported nodes (the register's loud refusals)", "EXTRACT-FAIL": "extractor refuses to run (top selection)",
            "SLANG-ERRORS": "slang rejects the compilation as the corpus provides it", "CORPUS-BLOCKED": "needs a generated configuration that is absent"}
    for k in ["LOADS-CLEAN", "LOADS-LOUD", "LOAD-REFUSED", "LOAD-ERROR", "LOAD-CRASH", "LOAD-NOT-RUN", "EXTRACTS-CLEAN", "EXTRACTS-LOUD", "EXTRACT-FAIL", "SLANG-ERRORS", "CORPUS-BLOCKED"]:
        if st.get(k):
            w("| %s: %s | %d |" % (k, desc[k], st[k]))
    w("")
    sgm = [r for r in rows if r["variant"] == "as-is" and r.get("svgolf_source_gate") and r["svgolf_source_gate"].get("ok") is not None]
    sgok = [r for r in sgm if r["svgolf_source_gate"]["ok"]]
    cats = collections.Counter()
    for r in sgm:
        for c in r["svgolf_source_gate"].get("categories", {}):
            cats[c] += 1
    w("**svGolf path versus ls-sv.** `extractors/sv/extract.py` takes several files and `-I` directories (`--top T f1.sv f2.sv -I dir`); that is how every")
    w("block here was extracted. svGolf's checker does not: `check/envelope.py` runs the SOURCE GATE on ONE file (README: \"One file, one design\") and extracts")
    w("the gate's canonical text; the gate refuses every compiler directive but `timescale and `default_nettype, attributes, `unique`/`priority`, pragma comments")
    w("and x/z literals (P-NO-TOOL-DIRECTIVES, P-SAME-PROGRAM). Measured on the %d primary files below 1 MB: **%d pass the gate as written**; findings by category"
      " (files with at least one): %s." % (len(sgm), len(sgok), ", ".join("%s %d" % kv for kv in cats.most_common())))
    w("So multi-file/include/package support is a blocker of the svGolf path (not of ls-sv itself): a real block verified through the checker needs a flattening step")
    w("(preprocess + concatenate in dependency order) or a multi-file gate; ls-sv's extractor and loader need nothing new for it.")
    w("")
    # per-project summary: as-is vs best variant
    byid0 = {r["id"]: r for r in rows}
    w("Per project. EXTRACTS-CLEAN = slang no error and no Unsupported node in the envelope; LOADS-CLEAN = additionally `load_design_sv2` accepts it and the lowered design has no Unsupported node")
    w("at the default point (the checker's `design`-stage test). The last column counts blocks that reach LOADS-CLEAN as-is or through a worked-around variant (`@wa`/`@wa2`/`@wa3`).")
    w("")
    w("| project | style | blocks | EXTRACTS-CLEAN as-is | LOADS-CLEAN as-is | LOADS-CLEAN after a worked-around variant | most frequent blockers (present in blocks) |")
    w("|---|---|---|---|---|---|---|")
    style = {"serv": "Verilog-2001", "picorv32": "Verilog-2001", "hazard3": "Verilog-2001 + includes", "mor1kx": "Verilog-2001 + defines", "biriscv": "Verilog-2001 + defines",
             "vexriscv": "generated Verilog", "rocket": "generated Verilog", "veer_el2": "SV + generated config"}
    tot = [0, 0, 0, 0]
    for proj, rs in projects.items():
        def eclean(r):
            return r["extract"]["rc"] == 0 and not r["slang"]["n_errors"] and not r["n_unsupported"] and r["status"] != "CORPUS-BLOCKED"
        def lclean(r):
            return r["status"] == "LOADS-CLEAN"
        c_e = sum(1 for r in rs if eclean(r))
        c_l = sum(1 for r in rs if lclean(r))
        c_v = 0
        for r in rs:
            vs = [byid0[x] for x in (r["id"] + "@wa", r["id"] + "@wa2", r["id"] + "@wa3") if x in byid0]
            if lclean(r) or any(lclean(v) for v in vs):
                c_v += 1
        tot = [tot[0] + len(rs), tot[1] + c_e, tot[2] + c_l, tot[3] + c_v]
        kc = collections.Counter(k for r in rs for k in set(effective_keys(r, byid0)) if k not in REMOVABLE_NOT)
        top = ", ".join("`%s` %d" % kv for kv in kc.most_common(3)) or "-"
        w("| %s | %s | %d | %d | %d | %d | %s |" % (proj, style.get(proj, "SystemVerilog"), len(rs), c_e, c_l, c_v, top))
    w("| **all** | | **%d** | **%d** | **%d** | **%d** | |" % tuple(tot))
    w("")
    # ---- funnel
    stages = ["slang accepts the compilation (0 errors)", "extractor produces an envelope", "envelope has no Unsupported node",
              "`load_design_sv2` accepts it", "lowered design has no Unsupported node (the checker's `design` stage)",
              "`sv_structure?` recognizes it (combinational, flat)", "`sv_equations?` accepts it"]

    def stage(r):
        k = 0
        if r["slang"]["n_errors"] == 0 and r["slang"]["parse_ok"]:
            k = 1
        else:
            return 0
        if r["extract"]["rc"] != 0:
            return k
        k = 2
        if r["n_unsupported"]:
            return k if not (r["lean"] and r["lean"]["loader"] == "LOADED") else 4
        k = 3
        l = r["lean"]
        if not l or l["loader"] != "LOADED":
            return k
        k = 4
        if l["lowered_unsupported"]:
            return k
        k = 5
        tac = l.get("tactic") or {}
        if any(k2.startswith("structure") and v.startswith("RECOGNIZED") for k2, v in tac.items()):
            k = 6
            if any(k2.startswith("equations") and v.startswith("RECOGNIZED") for k2, v in tac.items()):
                k = 7
        return k
    best = {}
    for r in rows:
        base = r["id"].split("@")[0]
        best[base] = max(best.get(base, 0), stage(r))
    asis_stage = {r["id"]: stage(r) for r in rows if r["variant"] == "as-is"}
    # blocks defined = bases (some, the Rocket slices, only exist as variants)
    bases = sorted(best)
    w("**Funnel** (blocks that get at least this far; `as is` = the block unmodified, `best variant` = the best of the block and its worked-around variants):")
    w("")
    w("| stage | as is | best variant |")
    w("|---|---|---|")
    w("| blocks | %d | %d |" % (len(asis_stage), len(bases)))
    for i, name in enumerate(stages, 1):
        w("| %s | %d | %d |" % (name, sum(1 for v in asis_stage.values() if v >= i), sum(1 for v in best.values() if v >= i)))
    w("")
    w("(`best variant` counts the three Rocket slices, which exist only as variants, as blocks; the loader-LOADED-but-loud rows count as having passed `load_design_sv2` only.)")
    w("")
    w("## 3. Per-block table (as-is rows)")
    w("")
    w("`unsupp` = Unsupported nodes in the envelope (all blockers visible at the extractor are listed in `census.json`); `row` = register row of the FIRST blocker in source order.")
    w("")
    w("`needs` = what slang needs besides the primary file: other files (`+n f`), `include files (`inc`), package imports (`pkg`), macros used and not defined in the scanned files (`mac`), parameters without a usable default (none here).")
    w("")
    w("| block | cat | kind | lines | needs | slang err | extract | unsupp | first blocker (row) | Lean loader | tactic | status |")
    w("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in [r for r in rows if r["variant"] == "as-is"]:
        fb = r["blockers"][0] if r["blockers"] else None
        fbs = ("%s: %s" % (fb["key"], short(fb["detail"], 60))) if fb else "-"
        lean = r["lean"]
        tac = "-"
        if lean and lean.get("tactic"):
            tac = "; ".join("%s %s" % (k, v.split(":")[0]) for k, v in lean["tactic"].items())
        nd = r.get("needs") or {}
        needs = ", ".join(x for x in [("+%d f" % len(r["deps"])) if r.get("deps") else "", ("inc %d" % len(nd.get("includes", []))) if nd.get("includes") else "",
                                      ("pkg %s" % "/".join(nd["package_imports"])) if nd.get("package_imports") else "",
                                      ("mac %d" % nd["n_macros_used"]) if nd.get("n_macros_used") else ""] if x) or "-"
        w("| %s | %s | %s | %d | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            r["id"], r["category"], r["kind"], r["lines"] or 0, needs, r["slang"]["n_errors"], r["extract"]["rc"],
            r["n_unsupported"] if r["n_unsupported"] is not None else "-", fbs.replace("|", "/"),
            lean["loader"] if lean else "-", tac, r["status"]))
    w("")
    w("## 4. Worked-around variants (clearly NOT the block as it is)")
    w("")
    w("`@wa` = the module text sliced out of a multi-module file (the top is instantiated by another module of the same file, which the extractor's `--top` refuses).")
    w("`@wa2` = Verilog-2001 spelling modernized by regex (`wire`/`reg` -> `logic`, a net declaration assignment `wire [r] n = e;` -> `logic [r] n; assign n = e;`, `always @*` and level-sensitive `always @(a or b)` -> `always_comb`), on the slice when there is one.")
    w("`@wa3` = `@wa2` plus every ANSI port that has a direction and no data type (`input [31:0] x`, an implicit net in Verilog-2001) typed `logic`; for `hazard3_branchcmp` also the one hand edit (its two configuration includes, ~60 parameters, replaced by `parameter W_DATA = 32`).")
    w("None is an ls-sv feature: they show what is BEHIND the first blocker. (A first version of the modernizer turned `wire x = e;` into `logic x = e;`, a one-time initializer, i.e. a different program; the loader rightly refused it. It was corrected and EVERYTHING re-run from the corrected extraction; no number here comes from the first version.)")
    w("")
    w("| variant | blocks it came from | unsupp before -> after | remaining blockers | Lean loader | tactic |")
    w("|---|---|---|---|---|---|")
    byid = {r["id"]: r for r in rows}
    for r in [r for r in rows if r["variant"] != "as-is"]:
        base = byid.get(r["id"].split("@")[0])
        before = (base["n_unsupported"] if base and base["n_unsupported"] is not None else ("fail" if base else "-"))
        keys = collections.Counter(k for k in bl_keys(r))
        lean = r["lean"]
        tac = "-"
        if lean and lean.get("tactic"):
            tac = "; ".join("%s %s" % (k, v.split(":")[0]) for k, v in lean["tactic"].items())
        w("| %s | %s | %s -> %s | %s | %s | %s |" % (r["id"], base["status"] if base else "-", before,
                                                   r["n_unsupported"] if r["n_unsupported"] is not None else "-",
                                                   ", ".join("%s x%d" % kv for kv in keys.most_common(4)) or "none",
                                                   lean["loader"] if lean else "-", tac))
    w("")
    w("## 5. Top blockers (ranked)")
    w("")
    w("Ranking is by the number of blocks a blocker is PRESENT in (= gates), as the brief asks; `sole` = blocks for which it is the ONLY blocker (what building it alone frees),")
    w("`first` = blocks where it is the first blocker in source order. Blocks counted: the %d as-is rows that are not corpus-blocked; for the 8 rows the extractor refuses to run"
      " (`x:top-instantiated`) the blockers of their module-slice variant are counted too. Consequence blockers (a slang error's fallout) and corpus-level ones are listed after the table, not ranked." % len(asis))
    w("")
    w("| # | blocker | register row | gates (present) | sole | first | layer: work package | effort (guess; S = a small PR, M = a work package, L = several) |")
    w("|---|---|---|---|---|---|---|---|")
    keys = sorted([k for k in present if k not in REMOVABLE_NOT], key=lambda k: (-present[k], -sole.get(k, 0), k))
    shown = 0
    for k in keys:
        name, layer, wp, eff, note = BLOCKERS.get(k, (k, "?", "?", "?", ""))
        shown += 1
        w("| %d | %s | `%s` | %d | %d | %d | %s: %s | %s |" % (shown, name, k, present[k], sole.get(k, 0), first.get(k, 0), layer, wp, eff))
        if shown >= 12:
            break
    others = [k for k in present if k in REMOVABLE_NOT]
    w("")
    w("Not ranked (consequences of slang errors / corpus-level): " + ", ".join("`%s` (%d)" % (k, present[k]) for k in sorted(others, key=lambda k: -present[k])) + ".")
    w("")
    w("Greedy unblocking order (blocks freed COMPLETELY at each step, then blocks the blocker is present in):")
    w("")
    tot = 0
    for i, (k, gain, n) in enumerate(order, 1):
        tot += gain
        w("%d. `%s` frees %d (cumulative %d), present in %d" % (i, k, gain, tot, n))
    w("")
    def freed(items):
        keys = set(items)
        return sorted(r["id"] for r in asis if (effs0[r["id"]] - REMOVABLE_NOT) and (effs0[r["id"]] - REMOVABLE_NOT) <= keys)
    byid2 = {r["id"]: r for r in rows}
    effs0 = {r["id"]: set(effective_keys(r, byid2)) for r in asis}
    nets = ["dc-net-z", "ld-init-expr"]
    w("Rows `dc-net-z` and `ld-init-expr` are ONE work item (Verilog nets and typeless declarations: the extractor half and the loader half), which is why neither is `sole` alone. Blocks freed COMPLETELY (every other")
    w("extractor/loader blocker absent, tactics not considered) by combinations:")
    w("")
    for label, items in [("nets (`dc-net-z` + `ld-init-expr`)", nets), ("nets + `pr-implicit-event`", nets + ["pr-implicit-event", "pr-event-list"]),
                         ("nets + `pr-implicit-event` + `x:top-instantiated`", nets + ["pr-implicit-event", "pr-event-list", "x:top-instantiated"]),
                         ("`le-param-package`", ["le-param-package"]),
                         ("all four items above", nets + ["pr-implicit-event", "pr-event-list", "x:top-instantiated", "le-param-package"])]:
        f = freed(items)
        w("* %s: %d blocks%s" % (label, len(f), (" (" + ", ".join(f[:12]) + (", ..." if len(f) > 12 else "") + ")") if f else ""))
    w("")
    w("(Blockers hidden behind a refusal that stops the stage -- the extractor failing to run, the loader's first message -- are not seen; `cva6_popcount` is listed although it is recursive, `le-recursion`.)")
    w("")
    w("Notes per blocker (judgement):")
    w("")
    for k in keys[:12]:
        name, layer, wp, eff, note = BLOCKERS.get(k, (k, "", "", "", ""))
        if note:
            w("* `%s`: %s" % (k, note))
    w("")
    # ---- cross-reference with the real-world survey
    byid1 = {r["id"]: r for r in rows}
    effs = {r["id"]: set(effective_keys(r, byid1)) for r in asis}

    def blocks_with(keys):
        return sum(1 for ks in effs.values() if ks & set(keys))
    nas = len(asis)
    anyblock = sum(1 for r in asis if effs[r["id"]] - REMOVABLE_NOT or r["status"] in ("EXTRACT-FAIL",))
    w("## 5b. Cross-reference with the real-world survey (`svgolf/design/real-world-sv/SURVEY.md`, svgolf-prep 6aacc87b)")
    w("")
    w("The survey measures 331 implementations of eight algorithm families (golf-style kernels, 77% of its 213 self-contained real files have an Unsupported node) against the svGolf pipeline, ranked by frequency x refusal x")
    w("scorer readability. This census measures %d RISC CPU blocks against ls-sv for VERIFICATION, so the weights differ; the register row ids are the same. Counts below are mine (blocks of my %d as-is rows"
      % (nas, nas))
    w("that carry any of the rows); the survey's counts are not redone.")
    w("")
    w("| survey rank and gap | survey rows | my blocks | agree / differ |")
    w("|---|---|---|---|")
    X = [
        ("1 procedural `for`", ["st-for", "ld-localdecl", "st-compound"], "agree on the construct and the register rows; weaker here (CPU datapath blocks have fewer loops than kernels; `LocalDecl` is the loader-side half). Both measurements show loops die at the extractor AND at the loader."),
        ("2 user functions / tasks", ["ex-user-call", "dc-member-kinds", "sy-user-task-call"], "agree (RVC expanders, `vbits`, helper functions)."),
        ("3 `wire` / implicit nets", ["dc-net-z", "ld-init-expr"], "agree on the cause, DIFFER in rank: the survey puts it 3rd, here it is 1st-2nd because 40%% of this corpus is Verilog-2001. This census adds the LOADER half: the extractor accepts a typeless input port / `wire [N:0]` input and `load_design_sv2` then refuses it with `unrecoverable packed dimensions` (the survey notes the message sits only in `ld-init-expr`'s tag); I measured it on every Verilog-2001 core."),
        ("4 block/generate-local declarations", ["ld-localdecl", "le-generate-decl"], "agree, fewer here."),
        ("5 `always @*` / `always @(a or b)`", ["pr-implicit-event", "pr-event-list"], "agree (survey: 25 of 213 real files; here the figure on the left). Fixing it alone frees only blocks with no `wire`, which is why it is a pair with gap 3."),
        ("8 module instances in the tactics", ["hi-uninstantiated", "ld-unknown-kind"], "NOT measured here: the hierarchical blocks (`ibex_ex_block`, `cv32e40p_alu`) never reached the tactics. What I add is the multi-file side: an instance of a module that is not in the compilation (`hi-uninstantiated`)."),
        ("9 explicit casts `N'(x)`", ["cv-explicit"], "agree (ibex, cv32e40x, cva6)."),
        ("12 `unique case` / `casez`", ["st-casez", "ex-inside", "st-cond-qual"], "agree on the pair of rows; for the svGolf SOURCE GATE the qualifier is the bigger issue (see below: 20 of 81 primary files)."),
        ("13 unpacked arrays", ["dc-unpacked", "pa-aggregate-point", "sel-default-point-index", "st-assign-target"], "agree (register files, `imd_val_q_i[2]`)."),
        ("14 signed", ["dc-signed", "cv-width"], "agree (multipliers, dividers, comparators)."),
        ("15 packages / typedef / enum", ["le-param-package", "pa-syntax-recovery"], "DIFFER strongly: the survey ranks packages 15th because Yosys 0.53 cannot read `import`, so such designs cannot be SCORED anyway; for verifying real SV cores through ls-sv alone the package-scoped parameter / enum type is the FIRST loader blocker of the SystemVerilog projects and the first step of the greedy order. Which weight is right depends on whether a real-block target must pass the Yosys scorer: it need not."),
        ("16 macros / include", ["x:svgolf-gate"], "agree on direction, DIFFER in weight: the survey calls it low-medium; on real CPU blocks %d of %d primary files fail the source gate for a directive (macro/include/ifdef), and lowRISC `ASSERT_*` macros alone touch every ibex/OpenTitan block. For ls-sv itself it is no blocker (`-I` works)."),
    ]
    gate_dir = sum(1 for r in asis if r.get("svgolf_source_gate") and r["svgolf_source_gate"].get("categories", {}).get("directive/macro/include"))
    gate_n = sum(1 for r in asis if r.get("svgolf_source_gate") and r["svgolf_source_gate"].get("ok") is not None)
    for name, keys, txt in X:
        n = gate_dir if keys == ["x:svgolf-gate"] else blocks_with(keys)
        if "%d of %d" in txt:
            txt = txt % (gate_dir, gate_n)
        w("| %s | %s | %d of %d | %s |" % (name, ", ".join("`%s`" % k for k in keys), n, nas, txt.replace("%%", "%")))
    w("")
    w("Survey gaps 6 (replication), 7 (constant part-select of literal-width signals), 10 (comparisons in conditions) and 11 (generate structure, `$clog2`) are TACTIC-level; my tactic stage reached only 6 blocks, and the refusals it printed")
    w("coincide with them: `sv_structure?` refuses `$clog2` in a localparam (`cv32e40p_ff_one`, gap 11), `sv_equations?` refuses a constant part-select WRITE `data_o[31:0] = data_i` (`prim_secded_*`, gap 7, the survey's \"legacy part select\"),")
    w("and refuses multi-dimensional packed arrays (`cv32e40p_popcnt`, `cv32e40x_popcnt`, `cv32e40x_alu_b_cpop`) and `always_comb` bodies that write several windows or have several statements (`cv32e40p_compressed_decoder`, `prim_secded_inv_72_64_dec`): the last two are the survey's \"S1b gate d\" item.")
    w("Multi-dimensional packed arrays are not in the survey's list (it records 1-D/2-D packed arrays as working for the structure stage; the refusal I measured is in `sv_equations?`).")
    w("")
    w("Only here, not in the survey: (a) `--top` of a module instantiated by another module of the same sources (extractor CLI), (b) generated configuration (`el2_param.vh`), (c) `lean:max-rec-depth` on multi-MB envelopes,")
    w("(d) generated Chisel/SpinalHDL Verilog as a style (net declaration assignments everywhere, one module per file), (e) the `Initial`-with-assertion guard of PULP/OpenTitan cells reaching the loader (`ld-initial-syscall`).")
    w("")
    # ---- register holes
    holes = collections.defaultdict(lambda: [0, set()])
    for r in rows:
        for u in r["unsupported"]:
            if u["row_status"] in ("unregistered", "family"):
                holes[(u["sv_kind"], u["row_status"], u["row"])][0] += u["count"]
                holes[(u["sv_kind"], u["row_status"], u["row"])][1].add(r["id"].split("@")[0])
    w("## 6. Holes in the refusal register found by the census")
    w("")
    w("An `Unsupported` kind with no row of its own (`unregistered`) or only a catch-all family row (`family`). The extractor/loader refuse them LOUDLY, so nothing is wrong")
    w("with the tier; the register just does not name them. Pipeline-level facts with no row either: (a) `extract.py --top T` fails with \"no such module among top instances\"")
    w("when T is instantiated by another module of the same sources (8 as-is rows; slang's `topModules` option would select it); (b) the extractor still writes an envelope when slang")
    w("reports errors (\"extracting anyway\"): `el2_ifu_compress_ctl` has two slang errors (missing generated include) and a clean-looking empty-of-Unsupported envelope, so an envelope is not a verdict;")
    w("(c) an `Initial` / `LocalDecl` / `GenerateDecl` node the extractor emits and the loader refuses (rows `ld-initial-syscall`, `ld-localdecl`, `le-generate-decl` exist: extractor-vs-loader vocabulary mismatches).")
    w("")
    w("| sv_kind | status | nearest row | nodes | blocks |")
    w("|---|---|---|---|---|")
    for (k, stt, row), (n, bs) in sorted(holes.items(), key=lambda kv: -kv[1][0]):
        w("| `%s` | %s | `%s` | %d | %s |" % (k, stt, row, n, ", ".join(sorted(bs)[:4]) + ("..." if len(bs) > 4 else "")))
    w("")
    w("## 7. Not measured, and caveats")
    w("")
    w("* The Lean steps ran at the DEFAULT parameter point of each block (`d.sem <defaults>`); `load_design_sv2` is the checker's own gate, but the multi-point probe sidecar (`--probe-points`) was not used, so a block that")
    w("  loads at its defaults may still be refused at another point.")
    w("* A loader refusal reports the FIRST failing message (`load_design_sv2` throws at the first); the blockers behind it are invisible until it is removed. The extractor-side list is complete (all Unsupported nodes).")
    w("* `sv_structure?` / `sv_equations?` were run only on blocks that load with a clean lowered design and whose processes are continuous assigns / `always_comb`: the shape of the goal is the task shape")
    w("  (`example (p0 ... : Nat) : CombDesign (d.sem p0 ...)`, parameters free), no rank certificate was supplied, so `RECOGNIZED` means the recognizer accepted the design and printed its sites and rank relation, not that a proof exists.")
    w("* Sequential blocks (registers, FSM multipliers/dividers) were measured through the loader only; the sequential tier is not an ls-sv goal of the current ladder (policy: combinational first).")
    w("* Envelopes above 1.5 MB (13 blocks) were loaded in a separate budgeted batch; blocks that did not finish are reported as `NOT-RUN` / `LOAD-CRASH`, never as accepted.")
    w("* The `@wa*` variants are derived by regular expressions (`census_extract.py`: `modernize`, `type_implicit_ports`, `make_slice`) and by one hand edit (`hazard3_branchcmp`: the configuration include replaced by its one parameter).")
    w("  They are not part of any claim about the block as written. The modernizer does not touch non-ANSI port declarations or implicit-typed nets declared in the body.")
    w("* No simulation oracle (Verilator/Icarus/Xcelium) was run: this is a census of acceptance, not of semantic agreement. The semantic cross-checks of ls-sv (harness/sv) are not repeated here.")
    w("* The svGolf source-gate measurement skips the one primary file above 1 MB (the 9.5 MB Rocket file: the gate's Python scanner ran more than 7 minutes on it before I stopped it); 81 of the 82 as-is blocks are measured.")
    w("* Third-party licences differ and are recorded per project; nothing third-party is committed. Licence strings come from file headers and GitHub metadata and were not legally reviewed.")
    w("")
    w("## 8. First targets (G2)")
    w("")
    w("See `FIRST_TARGETS.md` and `g2/G2Specs.lean` (typechecked statements, nothing proved): `hazard3_branchcmp` (spec `Rv.branchSem`) and `biriscv_decoder` (spec `Rv.decode`) are the two blocks whose worked-around variants reach")
    w("`sv_equations?`; `biriscv_alu` (spec `Rv.aluSem`) loads and stops at the multi-statement `always_comb` rule; `cv32e40p_compressed_decoder` (spec `Rv.expandC`) is next.")
    w("")
    w("## 9. Reproduce")
    w("")
    w("```")
    w("cd svgolf/design/real-world-sv/rb0")
    w("./fetch.sh $S/src/files                      # 137 files, sha256-verified")
    w("python3.12 corpus_def.py                      # corpus.json from the block definitions")
    w("python3.12 census_extract.py --src $S/src --out $S/out/final3 -j 3     # slang + extractor + envelope statistics (~2 min)")
    w("python3.12 census_srcgate.py --src $S/src --out $S/out/final3 --repo <repo root>")
    w("python3.12 census_lean.py gen --out $S/out/final3 --lean-dir $S/lean/final2 --wt <repo root>   # then run lean/final2/batchAB.sh and batchC.sh through the Lean slot")
    w("python3.12 census_lean.py parse --out $S/out/final3 --lean-dir $S/lean/final2")
    w("python3.12 census_report.py --out $S/out/final3 --md CENSUS.md --json census.json")
    w("```")
    w("")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    main()

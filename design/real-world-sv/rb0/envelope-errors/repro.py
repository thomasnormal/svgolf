#!/usr/bin/env python3.12
"""WP-RB0 follow-up: what lands in the envelope when slang reports errors, and which consumer notices.

    python3.12 repro.py [--repo REPO_ROOT]

Python only (no Lean, no slot). For each case file next to this script it runs
  * the extractor as the checker runs it (`extract.py --top t`), and with `--probe-points` for the parametric twins;
  * the svGolf stages' own functions: the source gate, `banlist.front_check` (non-empty banlist), `banlist.check` with an EMPTY
    banlist, `fourstate.slang_check`;
and the same extractor with the proposed marker (`proposal.diff` applied to a scratch copy: nothing in the repository is
patched). Prints a markdown table.
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser()
ap.add_argument("--repo", default=os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "..")))
a = ap.parse_args()
a.repo = os.path.abspath(a.repo)
EXTRACT = os.path.join(a.repo, "extractors", "sv", "extract.py")
sys.path.insert(0, os.path.join(a.repo, "svgolf", "score"))
import srcgate  # noqa: E402
import banlist  # noqa: E402
import fourstate  # noqa: E402

tmp = tempfile.mkdtemp(prefix="envelope-errors-")
patched = os.path.join(tmp, "extract_patched.py")
r = subprocess.run(["patch", "-s", "-o", patched, EXTRACT, os.path.join(HERE, "proposal.diff")],
                   capture_output=True, text=True)
have_patch = r.returncode == 0


def extract(script, case, probes=None):
    out = os.path.join(tmp, os.path.basename(script) + "_" + case + ("_p" if probes else "") + ".json")
    cmd = [sys.executable, script, "--top", "t", os.path.join(HERE, case + ".sv"), "-o", out]
    if probes:
        cmd += ["--probe-points", probes]
    p = subprocess.run(cmd, capture_output=True, text=True, cwd=HERE)
    return p, out


def envelope_view(path):
    d = json.load(open(path))
    m = d["design"]["modules"][0]
    return d, [(o["sv_kind"], (o.get("text") or "")[:60]) for o in m["others"]]


def norm(d):
    d = json.loads(json.dumps(d))
    d.pop("source_files", None)

    def strip(n):
        if isinstance(n, dict):
            n.pop("span", None)
            for v in n.values():
                strip(v)
        elif isinstance(n, list):
            for v in n:
                strip(v)
    strip(d)
    return d


ctrl, _ = envelope_view(extract(EXTRACT, "c7_control")[1])
print("| case | slang error | extractor exit / stderr | envelope vs the clean control | with the proposal | source gate | banlist front (non-empty) | banlist EMPTY | fourstate |")
print("|---|---|---|---|---|---|---|---|---|")
for case in ["c1_include", "c2_macro", "c4_import", "c6_other_module", "c7_control"]:
    p, out = extract(EXTRACT, case)
    d, others = envelope_view(out)
    if norm(d) == norm(ctrl):
        diff = "IDENTICAL"
    elif not others:
        pk = [i.get("package") for i in d["design"]["modules"][0].get("imports", [])]
        diff = "no Unsupported node; differs only by the import of " + str(pk)
    else:
        diff = "differs: " + str(others)
    if have_patch:
        _, o2 = envelope_view(extract(patched, case)[1])
        prop = ", ".join(k for k, _ in o2) or "nothing"
    else:
        prop = "(patch did not apply)"
    src = os.path.join(HERE, case + ".sv")
    canon, find = srcgate.gate_file(src, name=case + ".sv")
    fr, dg = banlist.front_check([src], "t", ["+"], [])
    be = banlist.check([src], "t", [], [], gate=False)
    f4 = fourstate.slang_check([src], "t", {})
    print("| %s | %s | %d / %s | %s | %s | %s | %s | %s | %s |" % (
        case, "yes" if case != "c7_control" else "no", p.returncode,
        "one warning line" if p.stderr.strip() else "silent", diff, prop,
        "REJECT" if find else "accepts", "REJECT" if (fr or dg) else "accepts",
        "accepts" if be["passed"] else "REJECT", "REJECT" if (f4[0] or f4[1]) else "accepts"))
print()
for case in ["c4p_import", "c6p_other_module"]:
    for probes in ("N=1;N=4", None):
        p, out = extract(EXTRACT, case, probes)
        d, others = envelope_view(out)
        side = out[:-5] + ".probes.json"
        fe = [pt["frontend_errors"] for pt in json.load(open(side))["points"]] if probes else "no sidecar"
        if have_patch:
            _, o2 = envelope_view(extract(patched, case, probes)[1])
            prop = ", ".join(k for k, _ in o2) or "nothing"
        else:
            prop = "?"
        print("%s %s: envelope others %s; sidecar frontend_errors %s; with the proposal: %s" % (
            case, "--probe-points" if probes else "(no probe points)", others or "[]", fe, prop))

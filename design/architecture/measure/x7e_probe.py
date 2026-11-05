#!/usr/bin/env python3
"""X7 proper: heartbeats of L's E route (arch-loop) per theorem and per tactic call, against L's build, read-only.

    python3 x7e_probe.py prepare --repo REPO --commit c7b56d30 --out S
    (S/run.sh through the Lean slot)
    python3 x7e_probe.py collect --out S --json x7e.json

`prepare` writes under S only (never into the repository or into arch-loop's tree):
* `S/src/`: the svgolf-side modules of L's loop route at COMMIT (`git show`), compiled by `S/run.sh` in
  compile-loop.sh's order, with `lean -R S/src -o S/build/<M>.olean`. The dependencies (SeqTask, TaskV2, ObsComb,
  ObsCombE, LoopTask) verbatim; `LoopTaskE` and the three designs (ClmulNested, PriEnc, PopCount) as PROBES.
* `S/libsrc/LeanModels/Sv/`: probe copies of L's library modules (Loop2, Loop2Rows, Loop2Sem, Loop2Frag, Loop2E,
  Loop2Slot, Loop2Clmul, XorSum), each compiled once to measure it, output never put on LEAN_PATH.
* `S/root/svgolf`: a scratch svGolf root for `load_sv` (its `check/`, `score/`, `tasks/` and the repository's `extractors/`
  are symlinks into the measuring worktree, whose extraction path is identical to COMMIT's; the designs' `.sv`
  files are copied from COMMIT), so the envelope cache is written under S.

A probe is the module with three additions and no other change:
* `import X7Hb` (the `count_hb` command and the `hb_tac` tactic, both reading core's `IO.getNumHeartbeats`)
  and `set_option Elab.async false`;
* `count_hb in` before every top-level declaration (a `mutual` block as one);
* in the designs only, `count_hb in` before `load_sv`, and `hb_tac "<label>" (…)` around each argument of `statement`/`statement_E0` and around the
  `sv_loop_sem` / `sv_loop_rows` calls, which logs that tactic's heartbeats (`X7EHB <label> <n>`).
The modules are compiled against a COPY-ON-WRITE CLONE of arch-loop's built libraries (`S/snap`, `cp -c`), so a
rebuild in arch-loop during the run cannot change what is measured.
"""
import argparse
import json
import os
import re
import subprocess

DEPS = [("svgolf/design/sequential/SeqTask.lean", "SeqTask"), ("svgolf/design/architecture/TaskV2.lean", "TaskV2"),
        ("svgolf/design/architecture/ObsComb.lean", "ObsComb"), ("svgolf/design/architecture/ObsCombE.lean", "ObsCombE"),
        ("svgolf/design/loop/LoopTask.lean", "LoopTask")]
PROBES = [("svgolf/design/loop/LoopTaskE.lean", "LoopTaskE"), ("svgolf/design/loop/g1/ClmulNested.lean", "ClmulNested"),
          ("svgolf/design/loop/g2/PriEnc.lean", "PriEnc"), ("svgolf/design/loop/g2/PopCount.lean", "PopCount")]
LIBS = ["Loop2", "Loop2Rows", "Loop2Sem", "Loop2Frag", "Loop2E", "Loop2Slot", "Loop2Clmul", "XorSum"]
SVS = ["svgolf/design/loop/g2/prienc.sv", "svgolf/design/loop/g2/popcnt.sv", "svgolf/tests/clmul/attacks/proc_nested_for.sv"]

X7HB = '''import Lean

/-! The X7 heartbeat probes (x7e_probe.py): a command and a tactic wrapper around core's `IO.getNumHeartbeats`. -/

open Lean Elab Command in
elab "count_hb " "in " cmd:command : command => do
  let h0 ← IO.getNumHeartbeats
  elabCommand cmd
  let h1 ← IO.getNumHeartbeats
  let pos := (← getFileMap).toPosition (cmd.raw.getPos?.getD 0)
  logInfo m!"X7HB {pos.line} {h1 - h0}"

open Lean Elab Tactic in
elab "hb_tac " lbl:str " (" t:tacticSeq ")" : tactic => do
  let h0 ← IO.getNumHeartbeats
  evalTactic t
  let h1 ← IO.getNumHeartbeats
  logInfo m!"X7EHB {lbl.getString} {h1 - h0}"

open Lean Elab Command in
elab "#hb_mark " lbl:str : command => do
  logInfo m!"X7MARK {lbl.getString} {← IO.getNumHeartbeats}"
'''

DECL = re.compile(r"^(@\[[^\]]*\]\s*)?(private |protected |noncomputable |partial |unsafe |nonrec )*"
                  r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class)\b")


def git_show(repo, commit, path):
    return subprocess.run(["git", "-C", repo, "show", "%s:%s" % (commit, path)], check=True,
                          capture_output=True, text=True).stdout


def probe_text(src, wrap_args=False):
    lines = src.split("\n")
    i = 0
    head = []
    while i < len(lines) and (lines[i].startswith("import ") or not lines[i].strip()):
        head.append(lines[i])
        i += 1
    body = lines[i:]
    out = []
    in_mutual = False
    for ln in body:
        if ln.strip() == "mutual" and not ln.startswith(" "):
            out.append("count_hb in")
            in_mutual = True
            out.append(ln)
            continue
        if in_mutual:
            if ln.startswith("end") and ln.strip() == "end":
                in_mutual = False
            out.append(ln)
            continue
        if DECL.match(ln):
            j = len(out)
            while j > 0 and (out[j - 1].startswith("@[") or re.match(r"^set_option .* in\s*$", out[j - 1])):
                j -= 1
            e = j
            while e > 0 and not out[e - 1].strip():
                e -= 1
            if e > 0 and out[e - 1].rstrip().endswith("-/"):
                t = e - 1
                while t >= 0 and not out[t].lstrip().startswith("/-"):
                    t -= 1
                if t >= 0 and out[t].lstrip().startswith("/--"):
                    j = t
            out.append(ln)
            out.insert(j, "count_hb in")
            continue
        out.append(ln)
    text = "\n".join(head + ["import X7Hb", "", "set_option Elab.async false", ""] + out)
    text = text.replace("\nset_option Elab.async false\n", "\nset_option Elab.async false\n#hb_mark \"start\"\n", 1)
    text = text.rstrip("\n") + "\n\n#hb_mark \"end\"\n"
    if wrap_args:
        text = wrap_design(text)
    return text


def wrap_design(text):
    # the design's elaboration at elaboration time (`load_sv`: extraction cached, then `load_design_sv2`)
    text = re.sub(r"^(load_sv .*)$", r"count_hb in\n\1", text, flags=re.M)
    # the loop tactics
    text = re.sub(r"^(\s+)(sv_loop_sem .*)$", r'\1hb_tac "sv_loop_sem" (\2)', text, flags=re.M)
    text = re.sub(r"^(\s+)(sv_loop_rows .*)$", r'\1hb_tac "sv_loop_rows" (\2)', text, flags=re.M)
    # the arguments of `statement` / `statement_E0`
    for thm in ("statement", "statement_E0"):
        m = re.search(r"^theorem %s\b.*?(?=^(?:#pin_axioms|/--|theorem|end |count_hb))" % thm, text, flags=re.M | re.S)
        if not m:
            continue
        seg = m.group(0)
        new, k, pos = [], 0, 0
        while True:
            a = seg.find("(by ", pos)
            if a < 0:
                new.append(seg[pos:])
                break
            depth, b = 0, a
            while b < len(seg):
                if seg[b] == "(":
                    depth += 1
                elif seg[b] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                b += 1
            inner = seg[a + 4:b]
            hint = ("frag_ok" if "sv_frag_ok" in inner else "iface" if "CombTask.Interface" in inner else
                    "declWidth" if "declWidth" in inner else "notInput" if "inputNames" in inner else
                    "procs" if inner.strip().endswith("rfl") else "inputsNodup" if "rw [h]" not in inner else "decls")
            label = "%s.%d:%s" % (thm, k, hint)
            new.append(seg[pos:a] + '(by hb_tac "%s" (%s))' % (label, inner))
            k += 1
            pos = b + 1
        text = text.replace(seg, "".join(new), 1)
    return text


def cmd_prepare(a):
    S = os.path.abspath(a.out)
    for d in ("src", "build", "libsrc/LeanModels/Sv", "libbuild", "root/svgolf/design/loop/g2",
              "root/svgolf/tests/clmul/attacks", "log"):
        os.makedirs(os.path.join(S, d), exist_ok=True)
    open(os.path.join(S, "src", "X7Hb.lean"), "w").write(X7HB)
    for path, mod in DEPS:
        open(os.path.join(S, "src", mod + ".lean"), "w").write(git_show(a.repo, a.commit, path))
    for path, mod in PROBES:
        open(os.path.join(S, "src", mod + ".lean"), "w").write(
            probe_text(git_show(a.repo, a.commit, path), wrap_args=(mod != "LoopTaskE")))
    for mod in LIBS:
        open(os.path.join(S, "libsrc/LeanModels/Sv", mod + ".lean"), "w").write(
            probe_text(git_show(a.repo, a.commit, "LeanModels/Sv/%s.lean" % mod)))
    for p in SVS:
        dst = os.path.join(S, "root", p)
        open(dst, "w").write(git_show(a.repo, a.commit, p))
    for name, target in (("root/svgolf/check", os.path.join(a.worktree, "svgolf/check")),
                         ("root/svgolf/score", os.path.join(a.worktree, "svgolf/score")),
                         ("root/svgolf/tasks", os.path.join(a.worktree, "svgolf/tasks")),
                         ("root/extractors", os.path.join(a.worktree, "extractors"))):
        dst = os.path.join(S, name)
        if not os.path.islink(dst):
            os.symlink(target, dst)
    print("prepared", S)


def cmd_collect(a):
    S = os.path.abspath(a.out)
    res = {"schema": "x7e/1", "modules": {}}
    for f in sorted(os.listdir(os.path.join(S, "log"))):
        if not f.endswith(".out"):
            continue
        mod = f[:-4]
        txt = open(os.path.join(S, "log", f), errors="replace").read()
        src_path = os.path.join(S, "src", mod + ".lean")
        if not os.path.exists(src_path):
            src_path = os.path.join(S, "libsrc/LeanModels/Sv", mod + ".lean")
        src = open(src_path).read().split("\n") if os.path.exists(src_path) else []
        decls = []
        for m in re.finditer(r"X7HB (\d+) (\d+)", txt):
            line, hb = int(m.group(1)), int(m.group(2))
            if line - 1 < len(src) and src[line - 1].startswith("load_sv"):
                decls.append({"line": line, "decl": "load_sv", "heartbeats": hb})
                continue
            k = line - 1
            while k < len(src) and not (DECL.match(src[k]) or src[k].strip() == "mutual"):
                k += 1
            name = src[k] if k < len(src) else "?"
            nm = re.sub(r"^(@\[[^\]]*\]\s*)?(private |protected |noncomputable |partial |unsafe |nonrec )*"
                        r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class)\s*", "", name)
            decls.append({"line": line, "decl": (nm.split() or ["?"])[0], "heartbeats": hb})
        tacs = [{"label": l, "heartbeats": int(h)} for l, h in re.findall(r"X7EHB (\S+) (\d+)", txt)]
        marks = dict((l, int(h)) for l, h in re.findall(r"X7MARK (\S+) (\d+)", txt))
        errors = [ln for ln in txt.split("\n") if ": error" in ln][:5]
        res["modules"][mod] = {"decls": decls, "tactics": tacs, "errors": errors,
                               "module_total": (marks["end"] - marks["start"]) if "start" in marks and "end" in marks
                               else None, "sum_decls": sum(d["heartbeats"] for d in decls)}
    json.dump(res, open(a.json, "w"), indent=1)
    for mod, r in res["modules"].items():
        print(mod, "total", r["module_total"], "decls", len(r["decls"]), "errors", len(r["errors"]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["prepare", "collect"])
    ap.add_argument("--repo")
    ap.add_argument("--worktree")
    ap.add_argument("--commit", default="c7b56d30")
    ap.add_argument("--out")
    ap.add_argument("--json")
    a = ap.parse_args()
    {"prepare": cmd_prepare, "collect": cmd_collect}[a.cmd](a)


if __name__ == "__main__":
    main()

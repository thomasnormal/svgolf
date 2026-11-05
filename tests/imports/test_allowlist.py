#!/usr/bin/env python3.12
"""The checker's import allowlist (`check.py` IMPORT_ALLOW), tested against
`tests/expected.json` -> "import_allowlist".

    python3.12 tests/imports/test_allowlist.py          # exit 0 iff everything holds
    python3.12 tests/imports/test_allowlist.py --expected OTHER.json

Pure Python (no Lean, no Yosys): it takes about a second. What it checks:

1. every module in `admitted` matches the allowlist: the sv_comb tactic
   library a proof needs (`LeanModels.Sv.CombView*`, `CombKnown*`, `CombEq*`,
   `CombLib`) and the framework modules;
2. every module in `refused` does not: `Examples.*`, `LeanModels.Python.*`,
   `LeanModels.Core.*`, another submission, `Lake`, `Cli`, lookalikes of the
   admitted prefixes (`Mathlib2.Tactic`, `Batteries2`, ...);
3. headers (`parse_header`): a file importing an allowlisted module and a
   refused one is rejected for exactly the refused one; `module`/`prelude`
   headers raise;
4. the CLOSURE of the tactic library: every module that `LeanModels.Sv.CombEqTactic`,
   `CombLib`, ... import, transitively, is itself allowed. A later change of
   lean-surfaces that made a tactic module import Mathlib (or any module off
   the list) would otherwise turn every tactic proof into an `imports`-stage
   rejection of the references;
5. `SvGolf/CoreSimp.lean` (`sv_core_simp`) and `LeanModels/Sv/CombCoreSimp.lean` (`sv_simp`, the
   tactics' own `simp`) list exactly the package roots of `check.py` (WP-B review, gate M);
6. the CLOSURE of Mathlib (WP-B, 2026-10-31): the import closure of the module
   `Mathlib`, recomputed from the SOURCES of the packages in the package
   directory (check/layout.py; a header-only scan, no Lean, about 3 s), contains only module
   roots that are allowed, apart from the toolchain modules listed in
   `mathlib_closure.toolchain_unallowed` (reached, never importable directly).
   A Mathlib bump that made it depend on a package the checker does not admit
   fails here, not in a contestant's `imports` stage. Skipped, loudly, when the
   package sources are absent.
"""
import argparse
import importlib.util
import json
import os
import re
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.environ.get("SVGOLF_ROOT") or os.path.dirname(os.path.dirname(HERE))

spec = importlib.util.spec_from_file_location("svgolf_check", os.path.join(SVGOLF, "check.py"))
chk = importlib.util.module_from_spec(spec)
spec.loader.exec_module(chk)
# lean-surfaces, in either layout (check/layout.py; SVGOLF_LS_ROOT overrides)
LS_ROOT = chk.LS_ROOT


def allowed(mod):
    return any(re.fullmatch(p, mod) for p in chk.IMPORT_ALLOW)


def imports_of_file(path):
    with open(path) as fh:
        return chk.parse_header(fh.read())


MODIFIERS = {"public", "meta", "private"}


def source_imports(path):
    """The imports of a Lean SOURCE file (a package module: `module` header, `public` /
    `meta` / `private` modifiers, `import all`), read from its header only: line by line,
    nested block comments and `--` comments skipped, stopping at the first token that is not
    part of the header. (check.py's `parse_header` reads a SOLUTION, which may not carry a
    `module` header, so it cannot be used here.)"""
    out, depth, pend, first = [], 0, False, True
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            i, n, toks = 0, len(line), []
            while i < n:
                if depth:
                    a, b = line.find("-/", i), line.find("/-", i)
                    if a < 0 and b < 0:
                        i = n
                    elif b >= 0 and (a < 0 or b < a):
                        depth, i = depth + 1, b + 2
                    else:
                        depth, i = depth - 1, a + 2
                elif line.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif line.startswith("--", i):
                    i = n
                elif line[i].isspace():
                    i += 1
                else:
                    j = i
                    while (j < n and not line[j].isspace() and not line.startswith("--", j)
                           and not line.startswith("/-", j)):
                        j += 1
                    toks.append(line[i:j])
                    i = j
            for t in toks:
                if first and t == "module":
                    first = False
                    continue
                first = False
                if not pend and t in MODIFIERS:
                    continue
                if not pend and t == "import":
                    pend = True
                elif pend and t == "all":
                    continue
                elif pend:
                    out.append(t)
                    pend = False
                else:
                    return out
    return out


def package_closure(roots, packages_dir):
    """(modules found in a package, with their source path; modules found in none of them,
    i.e. the toolchain's) of the transitive imports of `roots`."""
    pkgs = [os.path.join(packages_dir, d) for d in sorted(os.listdir(packages_dir))]
    seen, outside, todo = {}, set(), list(roots)
    while todo:
        m = todo.pop()
        if m in seen or m in outside:
            continue
        rel = os.path.join(*m.split(".")) + ".lean"
        path = next((os.path.join(p, rel) for p in pkgs if os.path.isfile(os.path.join(p, rel))),
                    None)
        if path is None:
            outside.add(m)
            continue
        seen[m] = path
        todo += source_imports(path)
    return seen, outside


def closure(mods):
    """Transitive imports of `mods` that live in lean-surfaces' LeanModels/Sv,
    plus the first non-Sv modules they reach."""
    seen, todo, outside = set(), list(mods), set()
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        path = os.path.join(LS_ROOT, *m.split(".")) + ".lean"
        if not m.startswith("LeanModels.Sv"):
            outside.add(m)
            continue
        if not os.path.isfile(path):
            raise SystemExit(f"cannot find {path} for the import {m}")
        todo += imports_of_file(path)
    return seen, outside


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--expected", default=os.path.join(SVGOLF, "tests", "expected.json"))
    args = ap.parse_args(argv)
    with open(args.expected) as fh:
        exp = json.load(fh)["import_allowlist"]
    bad = []
    n = 0
    for m in exp["admitted"]:
        n += 1
        if not allowed(m):
            bad.append(f"{m}: should be admitted")
    for m in exp["refused"]:
        n += 1
        if allowed(m):
            bad.append(f"{m}: should be refused")
    for h in exp["headers"]:
        n += 1
        try:
            imps = chk.parse_header(h["text"])
        except chk.Reject as e:
            if not h.get("raises"):
                bad.append(f"header {h['name']}: unexpected rejection {e}")
            continue
        if h.get("raises"):
            bad.append(f"header {h['name']}: should have raised")
            continue
        rej = [m for m in imps if not allowed(m)]
        if imps != h["imports"] or rej != h["rejected"]:
            bad.append(f"header {h['name']}: got imports {imps}, rejected {rej}; "
                       f"want {h['imports']}, {h['rejected']}")
    # SvGolf/CoreSimp.lean (`sv_core_simp`) erases the simp tags of exactly the admitted package roots
    n += 1
    with open(os.path.join(SVGOLF, "SvGolf", "CoreSimp.lean")) as fh:
        cs = re.search(r"def corePackageRoots : List Name :=\s*\[([^\]]*)\]", fh.read())
    cs_roots = sorted(re.findall(r"`(\w+)", cs.group(1))) if cs else None
    if cs_roots != sorted(chk.PACKAGE_ROOTS):
        bad.append(f"SvGolf/CoreSimp.lean corePackageRoots {cs_roots} != check.py PACKAGE_ROOTS "
                   f"{sorted(chk.PACKAGE_ROOTS)}")
    # LeanModels/Sv/CombCoreSimp.lean (`sv_simp`, the tactics' own simp) erases exactly the same roots
    n += 1
    with open(os.path.join(LS_ROOT, "LeanModels", "Sv", "CombCoreSimp.lean")) as fh:
        cs2 = re.search(r"def coreSimpPackageRoots : List Name :=\s*\[([^\]]*)\]", fh.read())
    cs2_roots = sorted(re.findall(r"`(\w+)", cs2.group(1))) if cs2 else None
    if cs2_roots != sorted(chk.PACKAGE_ROOTS):
        bad.append(f"LeanModels/Sv/CombCoreSimp.lean coreSimpPackageRoots {cs2_roots} != check.py "
                   f"PACKAGE_ROOTS {sorted(chk.PACKAGE_ROOTS)}")
    seen, outside = closure(exp["admitted_tactic_library"])
    n += 1
    off = sorted(m for m in seen | outside if not allowed(m))
    if off:
        bad.append(f"the tactic library's import closure leaves the allowlist: {off}")
    note = ""
    mc = exp.get("mathlib_closure")
    pkgs = chk.packages_dir()      # SVGOLF_PACKAGES, else the layout's package directory
    if mc and os.path.isdir(pkgs) and os.path.isfile(os.path.join(pkgs, "mathlib", "Mathlib.lean")):
        inside, outside_m = package_closure(mc["roots"], pkgs)
        n += 1
        off_in = sorted({m.split(".")[0] for m in inside if not allowed(m)})
        off_out = sorted(m for m in outside_m if not allowed(m))
        if off_in:
            bad.append(f"the import closure of {mc['roots']} reaches package modules the "
                       f"allowlist refuses (roots): {off_in}")
        if off_out != sorted(mc["toolchain_unallowed"]):
            bad.append(f"toolchain modules reached from {mc['roots']} and not allowed: "
                       f"{off_out}; expected exactly {sorted(mc['toolchain_unallowed'])}")
        got = sorted({m.split(".")[0] for m in inside})
        n += 1
        if got != sorted(mc["package_roots"]):
            bad.append(f"module roots found in the packages: {got}; expected {sorted(mc['package_roots'])}")
        note = (f"; Mathlib closure: {len(inside)} package modules in {len(got)} roots, "
                f"{len(outside_m)} toolchain modules")
    elif mc:
        note = f"; Mathlib closure check SKIPPED (no package sources under {pkgs})"
    print(f"import allowlist: {n} checks, {len(bad)} failed; tactic library closure: "
          f"{len(seen)} modules, outside LeanModels.Sv: {sorted(outside)}{note}")
    for b in bad:
        print("  FAIL", b)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

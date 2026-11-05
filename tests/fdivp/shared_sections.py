#!/usr/bin/env python3
"""The proved references of task `fdivp` share their math layer and most of their glue, copied: every reference proof
is one self-contained file (no per-task proof library). This check pins the copies: the sections of

    tasks/fdivp/reference/fdivp_newton.lean      named in SHARED      are, character for character, those of
    tasks/fdivp/reference/fdivp_srt.lean                                tasks/fdivp/reference/fdivp.lean

A section is the text from its heading line `/-! # Section `X`...` through its closing line `end X`. Every section two
of the files have in common must be identical (so a new section of any file cannot reuse a name), and every section of
SHARED must be in all of them. That the copied text then CHECKS is the `references` step of tests/run.py (check.py,
accepted); `--selftest` shows the comparison is not vacuous.

    python3 tests/fdivp/shared_sections.py [--selftest]
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
REF = ROOT / "tasks" / "fdivp" / "reference"
# the references that copy D3's sections
COPIES = ["fdivp_newton.lean", "fdivp_srt.lean"]

# the sections every file of COPIES copies from fdivp.lean (D3), in file order
SHARED = ["IEEE754Proofs", "ScaleInvariance", "RneInterval", "RoundingBounds", "CertF", "DpN", "DpM", "DpQ", "DpR",
          "DpS", "DpT", "DpU", "DpG1", "DpG2", "DpG3", "DpG4"]

HEAD = re.compile(r"^/-! # Section `(\w+)`", re.M)


def sections(text):
    """name -> the text from the section's heading line through its `end <name>` line."""
    out = {}
    for m in HEAD.finditer(text):
        name = m.group(1)
        end = re.compile(r"^end " + re.escape(name) + r"$", re.M).search(text, m.end())
        if end is None:
            raise ValueError(f"section `{name}` has no closing line `end {name}`")
        if name in out:
            raise ValueError(f"section `{name}` appears twice")
        out[name] = text[m.start():end.end()]
    return out


def check(d3_text, nw_text, label="fdivp_newton.lean", base="fdivp.lean", shared=True):
    """The differences between the sections of `base` (text d3_text) and of `label` (text nw_text); `shared`: every
    section of SHARED must be in both."""
    a, b = sections(d3_text), sections(nw_text)
    errs = []
    if shared:
        for name in SHARED:
            for lab, s in ((base, a), (label, b)):
                if name not in s:
                    errs.append(f"section `{name}` is missing from {lab}")
    for name in sorted(set(a) & set(b)):
        if a[name] != b[name]:
            la, lb = a[name].split("\n"), b[name].split("\n")
            w = max(len(base), len(label)) + 1
            for k, (x, y) in enumerate(zip(la, lb)):
                if x != y:
                    errs.append(f"section `{name}` differs at its line {k + 1}:\n  {(base + ':').ljust(w)} {x!r}\n"
                                f"  {(label + ':').ljust(w)} {y!r}")
                    break
            else:
                errs.append(f"section `{name}` differs in length ({len(la)} vs {len(lb)} lines)")
    return errs


def main(argv):
    # newline="" keeps every \r: the sections are compared byte for byte, not after newline translation
    with open(REF / "fdivp.lean", encoding="utf-8", newline="") as f:
        d3 = f.read()
    with open(REF / "fdivp_newton.lean", encoding="utf-8", newline="") as f:
        nw = f.read()
    if "--selftest" in argv:
        assert check(d3, d3) == []
        assert check(d3, nw) == []
        i = nw.index("theorem norm_rows")
        assert check(d3, nw[:i] + "theorem norm_rows'" + nw[i + len("theorem norm_rows"):]) != [], \
            "a changed line must be caught"
        j = nw.index("/-! # Section `DpQ`")
        k = nw.index("end DpQ\n") + len("end DpQ\n")
        assert check(d3, nw[:j] + nw[k:]) != [], "a missing section must be caught"
        assert check(d3, nw.replace("end DpG4\n", "\nend DpG4\n", 1)) != [], "a changed layout must be caught"
        m = nw.index("theorem norm_rows")
        assert check(d3, nw[:m] + "\r" + nw[m:]) != [], "a carriage return must be caught"
        with open(REF / "fdivp_srt.lean", encoding="utf-8", newline="") as f:
            sr = f.read()
        assert check(d3, sr, "fdivp_srt.lean") == []
        extra = "\n/-! # Section `Xx` -/\nsection Xx\nend Xx\n"
        assert check(nw + extra, sr + extra.replace("section Xx", "section Xx\n"), "fdivp_srt.lean",
                     "fdivp_newton.lean", shared=False) != [], "a section two copies share must be compared"
        print("shared_sections selftest ok")
        return 0
    errs = []
    texts = {}
    for c in COPIES:
        with open(REF / c, encoding="utf-8", newline="") as f:
            texts[c] = f.read()
        errs += check(d3, texts[c], c)
    # a section two copies share without D3 must be identical too
    for i, c in enumerate(COPIES):
        for e in COPIES[i + 1:]:
            errs += check(texts[c], texts[e], e, c, shared=False)
    if errs:
        print("\n".join(errs))
        return 1
    print(f"{', '.join(COPIES)} have fdivp.lean's {len(SHARED)} shared sections, unchanged")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

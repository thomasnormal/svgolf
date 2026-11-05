#!/usr/bin/env python3
"""The golfer-facing claim of WP-G S1b gate d, as a pinned check: the reference proof of `add_proc` (the carry cell and
the sum bit in separate processes) holds, character for character, for `add_proc_m` (both in ONE `always_comb` body).

`sv_equations` names a fact by the signal it writes and the ordinal of the window among the windows that write that
signal (`eq_c_2` is the second window that writes `c`), so the two designs have the same aliases with the same
statements. The check compares everything after the leading doc comment of

    tasks/add/reference/add_proc.lean      and      tasks/add/reference/add_proc_m.lean

(the imports before it too): the proof is the same file. That the proof then CHECKS for `add_proc_m` is the
`references` step of tests/run.py (check.py, accepted), and `--selftest` shows the comparison is not vacuous.

    python3 tests/add/same_proof.py [--selftest]
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
REF = ROOT / "tasks" / "add" / "reference"


def split(text):
    """(imports before the first `/-!`, the text after its closing `-/`)."""
    i = text.index("/-!")
    j = text.index("-/", i) + 2
    return text[:i], text[j:]


def check(a_text, b_text):
    ha, ba = split(a_text)
    hb, bb = split(b_text)
    errs = []
    if ha != hb:
        errs.append("the imports differ")
    if ba != bb:
        la, lb = ba.splitlines(), bb.splitlines()
        for k, (x, y) in enumerate(zip(la, lb)):
            if x != y:
                errs.append(f"the proofs differ at line {k + 1} after the doc comment:\n  add_proc  : {x}\n  add_proc_m: {y}")
                break
        else:
            errs.append(f"the proofs differ in length ({len(la)} vs {len(lb)} lines after the doc comment)")
    return errs


def main(argv):
    a = (REF / "add_proc.lean").read_text()
    b = (REF / "add_proc_m.lean").read_text()
    if "--selftest" in argv:
        assert check(a, a) == []
        assert check(a, b) == []
        assert check(a, b.replace("eq_c_1 eq_p_1 eq_c_2", "eq_c_1 eq_p_1 eq_c_3", 1)) != [], "a changed alias must be caught"
        assert check(a, b.replace("import SvGolf.Comb", "import SvGolf.Task", 1)) != [], "a changed import must be caught"
        print("same_proof selftest ok")
        return 0
    errs = check(a, b)
    if errs:
        print("\n".join(errs))
        return 1
    print("add_proc_m.lean has add_proc.lean's proof, unchanged")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

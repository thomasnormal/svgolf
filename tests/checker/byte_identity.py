"""The byte-identity helper of the `--ppa` wiring (WP-X3): `check.py`'s result with every machine- and
run-dependent LEAF masked, so two results can be compared character for character.

The PPA columns are EXTRA: with `--ppa off` check.py's result must be exactly what it was before the wiring, and with
`--ppa auto` exactly that plus the result key `ppa` and the stage `stages.ppa`. The goldens in
`tests/checker/ppa_wiring/` are the NORMALIZED results of the baseline checker (svgolf-prep 49677a12, the commit
before the wiring) on the `add` and `aes_sbox` references; `PROVENANCE.txt` there has the commands.

Two masks, by what a leaf depends on:

  * RUN_VOLATILE: differs from run to run or machine to machine whatever the inputs: wall-clock times, the staging and
    work directories, the file count of the integrity snapshot. Masked everywhere.
  * BUILD_VOLATILE: deterministic in one checkout, but a function of more than (the design, the pinned flow): the
    identity of the tools (Yosys, Verilator, the lean-surfaces git revision, the extractor's and the svgolf-eval
    evaluator's builds), the sha256 of the extracted envelope (a function of the EXTRACTOR, which other work changes) and
    the comparator's count of submission constants, of toolchain modules and its replay record (functions of the proof file
    and of the ls-sv build). Masked in the comparison against the
    goldens, which were recorded by another commit; NOT masked (`strict`) when two results of ONE checkout are compared
    (`--ppa off` against `--ppa auto` in the same process), where they must be equal.

Every KEY survives either way, so an added, removed or renamed key is a difference; every other leaf, including every
deterministic value of the design and the flow (scores, rtlil/netlist/source hashes, vector counts, the oracle's verdict,
the comparator's axioms ...), is compared.

One list is compared as a SET (sorted, `ORDER_VOLATILE`): the comparator's `axioms`, which it reports in the order its walk
of the dependency closure meets them; that order is not even stable from run to run of one checkout (measured on `add_n`,
2026-11-03); which axioms appear is still compared exactly.
"""

import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
GOLDEN_DIR = os.path.join(HERE, "ppa_wiring")
MASK = "<volatile>"
RUN_VOLATILE = frozenset({
    # time
    "seconds", "cpu_seconds", "t_harvest_s", "t_lssv_s", "t_netlist_build_s", "t_netlist_run_s", "t_reread_s",
    "lssv_ms_per_vector", "lssv_timing",
    # where
    "stage_dir", "path", "extractor",
    # a count of the files in this machine's build trees
    "files",
})
BUILD_VOLATILE = frozenset({
    # which tool, which build
    "extractor_sha256", "lean_surfaces", "verilator", "yosys_version", "sveval_sha256",
    # a function of the extractor / of the proof file, not of the design and the pinned flow
    "envelope_sha256", "submission_constants_used",
    # the comparator's report of the toolchain modules it checked and of the kernel replay of the
    # dependency closure (WP-B review): functions of the proof file and of the ls-sv build
    "toolchain_modules", "replay",
})
VOLATILE = RUN_VOLATILE | BUILD_VOLATILE
# lists whose ORDER is a function of the ls-sv build (the comparator's walk of the dependency closure): compared sorted
ORDER_VOLATILE = frozenset({"axioms"})
# what the wiring adds, and nothing else
PPA_KEY = "ppa"
PPA_STAGE = "ppa"
# what the OS sandbox adds (WP-S) to a result made with `--sandbox auto|require`: the key `sandbox` and the stage
# `stages.sandbox`; `--sandbox off` (and a library caller that never configured one) adds neither
SANDBOX_KEY = "sandbox"
SANDBOX_STAGE = "sandbox"
# what a Lean slot wrapper adds (check.py, B7 of the newcomer study): `waited` in a stage's record, the seconds its Lean
# calls queued behind $SVGOLF_LEAN_WRAP (never part of the stage's `seconds`), and the key `lean_wrap` of a run that took
# the wrapper once ($SVGOLF_LEAN_WRAP_ONCE=1)
WAITED = "waited"
LEAN_WRAP_KEY = "lean_wrap"
# what the solution's progress report adds (check.py, item 9 of the from-scratch study): `progress` in the `solution`
# stage's record, the declarations the kernel finished and when each was reported (times of this run: volatile)
PROGRESS = "progress"
# the references whose proved (`full`) baseline result is recorded, by task
FULL_GOLDEN_REFERENCE = {"add": "add_n", "aes_sbox": "sbox_bp"}


def normalize(res, strict=False):
    """`res` (check.py's result) with the volatile leaves masked; a new object. `strict`: mask only RUN_VOLATILE (for two
    results of the same checkout)."""
    masked = RUN_VOLATILE if strict else VOLATILE

    def walk(x):
        if isinstance(x, dict):
            return {k: (MASK if k in masked else
                        sorted(walk(v)) if k in ORDER_VOLATILE and isinstance(v, list) else walk(v))
                    for k, v in x.items()}
        if isinstance(x, list):
            return [walk(v) for v in x]
        return x
    return walk(res)


def render(res, strict=False):
    """The normalized result as check.py prints a result (sorted keys, indent 2)."""
    return json.dumps(normalize(res, strict), indent=2, sort_keys=True) + "\n"


def without_ppa(res):
    """`res` minus exactly what `--ppa auto` / `require` add (the key `ppa` and the stage `stages.ppa`), what the
    sandbox adds (the key `sandbox` and the stage `stages.sandbox`) and what a Lean slot wrapper adds (`waited` in the
    stages whose Lean calls went behind it, `SVGOLF_LEAN_WRAP`; the key `lean_wrap` of `SVGOLF_LEAN_WRAP_ONCE=1`):
    whether a wrapper is in front of Lean is a property of the machine, not of the check; and the solution's
    `progress` record (its times are this run's)."""
    out = {k: v for k, v in res.items() if k not in (PPA_KEY, SANDBOX_KEY, LEAN_WRAP_KEY)}
    out["stages"] = {k: ({f: x for f, x in v.items() if f not in (WAITED, PROGRESS)} if isinstance(v, dict) else v)
                     for k, v in res["stages"].items() if k not in (PPA_STAGE, SANDBOX_STAGE)}
    return out


def golden_path(task, kind):
    """`kind` is "unproved" (`check.py --unproved`) or "full" (a proved run)."""
    return os.path.join(GOLDEN_DIR, f"{task}_{kind}.baseline.json")


def golden(task, kind):
    with open(golden_path(task, kind)) as fh:
        return fh.read()

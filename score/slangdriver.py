#!/usr/bin/env python3.12
"""slang's ANALYSIS errors, for the svGolf stages that elaborate a design with pyslang.

Decided 2026-11-01: "slang reports a program illegal" means the FULL slang driver
(parse, elaboration AND analysis errors; docs/sv-refusals.json, policy of that
date). `Compilation.getAllDiagnostics()`, which `banlist.py` and `fourstate.py`
read, does not contain the diagnostics of slang's analysis pass, the step the
`slang` command-line driver runs after elaboration (`Driver.runAnalysis`, i.e.
`pyslang.analysis.AnalysisManager.analyze`):

  MultipleAlwaysAssigns        variable 'y' driven by always_comb procedure cannot be
                               written to by any other process (IEEE 1800-2023 9.2.2.2,
                               9.2.2.4; an `initial` block is another process)
  MixedVarAssigns              cannot mix continuous and procedural assignments to
                               variable 'y' (6.5)
  MultipleContAssigns          cannot have multiple continuous assignments to variable
  InputPortAssign              cannot assign to input port 'a' (23.3.3.2)
  AlwaysWithoutTimingControl   'always' procedure does not advance time and so will
                               create a simulation deadlock (9.2.2.1)

Three of those are WARNINGS by slang's own definition (a bare `Diagnostic.isError()`
is False) and errors only because the driver promotes them, so the classification
here asks the driver's own DiagnosticEngine: a `slang` driver processed on the
stdin placeholder `-` (nothing is read) holds the driver's default severities and
analysis options. The severity is taken with the NULL source location, so that no
`pragma diagnostic` of the program can downgrade a diagnostic (the source gate
refuses pragma comments anyway; this does not rely on it).

Before this module the rule "a program slang rejects is rejected" held for these
shapes only through Yosys `check` (fourstate) and the Lean driver guards, and not at
all for `initial y = 0; always_comb y = a;` (docs/sv-tools-split-audit.md section 5,
finding 2). The analysis runs on a FRESH compilation that has the design's top as its
only top and the stage's parameter overrides applied, so a module the design does not
instantiate cannot refuse it and the verdict is per POINT, like the stage's own.

The same function is written down once more in the ls-sv extractor
(extractors/sv/extract.py, `_slang_analysis_errors`): the two must classify the same
diagnostics, which extractors/sv/test_slang_analysis.py checks when both are present.
Only the analysis pass is read here: the diagnostics that the driver promotes from
WARNING to ERROR at ELABORATION time (`IndexOOB`, `RangeOOB`, `DynamicNotProcedural`,
`UnknownSystemName`, ...) are not (fourstate's rule (c) refuses the out-of-range
ones as x sources); see docs/sv-refusals.json, the known hole "slang's driver promotes
some elaboration warnings".

    python3.12 score/slangdriver.py DESIGN.sv --top T [--point N=16]
"""

import os
import sys

sys.dont_write_bytecode = True

_DRIVER = None


def _driver():
    """One `slang` driver whose `diagEngine` holds the driver's default severities."""
    global _DRIVER
    if _DRIVER is None:
        from pyslang.driver import Driver
        driver = Driver()
        driver.addStandardArgs()
        driver.setTerminalColorsEnabled(False)
        if not (driver.parseCommandLine("slang -") and driver.processOptions()):
            raise RuntimeError("cannot configure the slang driver (default diagnostic severities)")
        _DRIVER = driver
    return _DRIVER


def diag_name(diagnostic):
    return str(diagnostic.code).split("(")[-1].rstrip(")")


def analysis_errors(trees, top, overrides=None):
    """The ERRORS of slang's analysis pass for `top` alone (its own hierarchy, the
    parameter `overrides` {name: value} applied): `[(code name, slang message, file,
    line)]`, sorted, empty when slang's driver finds none. `trees` are the design's
    SyntaxTrees. Fails closed: an analysis that cannot run is the error
    `AnalysisFailed`."""
    try:
        import pyslang
        from pyslang import ast
        from pyslang.analysis import AnalysisManager
        driver = _driver()
        options = ast.CompilationOptions()
        options.topModules = {top}
        if overrides:
            options.paramOverrides = [f"{k}={v}" for k, v in overrides.items()]
        comp = ast.Compilation(pyslang.Bag([options]))
        for t in trees:
            comp.addSyntaxTree(t)
        comp.getAllDiagnostics()                # elaborate: the analysis needs it
        manager = AnalysisManager(driver.analysisOptions)
        manager.analyze(comp)
        engine = driver.diagEngine
        sm = trees[0].sourceManager if trees else None
        found = set()
        for d in manager.getDiagnostics():
            severity = engine.getSeverity(d.code, pyslang.SourceLocation())
            if not (d.isError() or severity in (pyslang.DiagnosticSeverity.Error,
                                                pyslang.DiagnosticSeverity.Fatal)):
                continue
            try:
                where = (os.path.realpath(str(sm.getFileName(d.location))),
                         sm.getLineNumber(d.location))
            except Exception:      # noqa: BLE001
                where = ("?", 0)
            found.add((diag_name(d), " ".join(engine.formatMessage(d).split())) + where)
        return sorted(found, key=lambda f: (f[2], f[3], f[0], f[1]))
    except Exception as exc:       # noqa: BLE001  (fail closed)
        return [("AnalysisFailed", f"slang's analysis pass could not run: "
                 f"{type(exc).__name__}: {str(exc)[:200]}", "?", 0)]


def findings(trees, top, overrides=None):
    """The stage diagnostics (strings) for `analysis_errors`."""
    return [f"slang analysis error {code} at {path}:{line}: {message}"
            for code, message, path, line in analysis_errors(trees, top, overrides)]


def main(argv=None):
    import argparse
    from pyslang import syntax
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("sources", nargs="+")
    ap.add_argument("--top", required=True)
    ap.add_argument("--point", help="NAME=VALUE[,NAME=VALUE]")
    args = ap.parse_args(argv)
    point = ({kv.split("=")[0]: int(kv.split("=")[1]) for kv in args.point.split(",")}
             if args.point else {})
    import pyslang
    trees, sm = [], pyslang.SourceManager()
    for s in args.sources:
        with open(s) as fh:
            trees.append(syntax.SyntaxTree.fromText(fh.read(), sm, os.path.realpath(s)))
    found = findings(trees, args.top, point)
    for f in found:
        print(f)
    print("slang analysis:", "ERRORS" if found else "clean")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())

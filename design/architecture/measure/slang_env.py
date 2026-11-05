"""Shared pyslang loader for the WS4 measurement scripts (svgolf/design/architecture/measure/).

Every script here runs under `python3.12 -I` (isolated mode: no PYTHONPATH, no user site, no script directory on
sys.path), because some of them read fetched third-party SystemVerilog, which is untrusted data. Isolated mode also
hides the user-site pyslang install, so this module appends exactly that one directory (site.getusersitepackages())
and nothing else. Nothing from a source tree is ever imported or executed: sources are parsed by pyslang only.
"""
import os
import site
import sys


def pyslang():
    user_site = site.getusersitepackages()
    if user_site not in sys.path:
        sys.path.append(user_site)
    import pyslang as ps  # noqa: E402
    return ps


def compile_files(files, top=None, incdirs=(), defines=(), params=()):
    """Compile `files` as one compilation. Returns (comp, root, errors) where errors are formatted ERROR diagnostics."""
    ps = pyslang()
    from pyslang.ast import Compilation, CompilationOptions
    from pyslang.syntax import SyntaxTree
    sm = ps.SourceManager()
    popt = ps.parsing.PreprocessorOptions()
    popt.additionalIncludePaths = list(incdirs)
    if defines:
        popt.predefines = list(defines)
    bag = ps.Bag([popt])
    tree = SyntaxTree.fromFiles(list(files), sm, bag)
    opts = CompilationOptions()
    if top:
        opts.topModules = {top}
    if params:
        opts.paramOverrides = list(params)
    comp = Compilation(ps.Bag([opts]))
    comp.addSyntaxTree(tree)
    diags = comp.getAllDiagnostics()
    eng = ps.DiagnosticEngine(sm)
    errors = []
    for d in diags:
        if d.isError():
            try:
                loc = "%s:%d" % (os.path.basename(sm.getFileName(d.location)), sm.getLineNumber(d.location))
            except Exception:  # noqa: BLE001
                loc = "?"
            errors.append("%s %s %s" % (d.code, loc, " ".join(eng.formatMessage(d).split())[:200]))
    return comp, comp.getRoot(), errors, sm

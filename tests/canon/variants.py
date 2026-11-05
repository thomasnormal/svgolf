#!/usr/bin/env python3.12
"""Variants of a design that are the SAME circuit, for the canonical-scoring tests.

    python3.12 tests/canon/variants.py DESIGN.sv --top TOP --out DIR [--only v1,v2]

Writes `DIR/<stem>.<variant>.sv` for every variant below and prints their
paths. Every variant is the same circuit as the source gate's canonical text
of DESIGN.sv:

* LAYOUT (`KIND["layout"]`): the same token stream, only whitespace differs:
  leading blank lines, all tokens on one line (every line joined), one token
  per line, indentation stripped / doubled / tabs, a line break after every
  comma;
* RENAME (`KIND["rename"]`): a consistent renaming of the internal signals
  (nets and variables that are not ports), or of the generate-block labels
  and genvars;
* ORDER (`KIND["order"]`): the module's declarations hoisted to the top (in
  their order) and its other items (continuous assigns, always blocks,
  generate regions: concurrent, so order-independent) reversed or shuffled;
* COMMUTE (`KIND["commute"]`): the operands of every commutative binary
  operator (`& | ^ ^~ == != && ||`) swapped. The same function, but a
  different expression TREE, which the canonical scoring flow does not
  normalize (README.md, "Scoring"): it is recorded, not required equal.

The variants come from slang's token stream and syntax tree (pyslang), never
from regular expressions over the text, except `commabreak`, which only adds
whitespace after commas.
"""

import argparse
import os
import random
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(SVGOLF, "score"))
import srcgate  # noqa: E402
import pyslang  # noqa: E402
from pyslang import parsing, syntax  # noqa: E402


def canonical(path):
    canon, findings = srcgate.gate_file(path)
    if findings:
        raise ValueError(f"{path}: the source gate refuses it: {findings[:3]}")
    return canon


def nocomment(canon):
    """The gate's canonical text without the blank lines its stripped comments left."""
    lines = [ln.rstrip() for ln in canon.splitlines()]
    return "\n".join(ln for ln in lines if ln.strip()) + "\n"


def tokens(text):
    """slang's token stream: (kind, raw text, has leading trivia)."""
    tree = syntax.SyntaxTree.fromText(text, "x.sv")
    out = []

    def cb(node):
        if isinstance(node, parsing.Token):
            if node.kind != parsing.TokenKind.EndOfFile:
                out.append((str(node.kind).split(".")[-1], node.rawText, bool(node.trivia)))
        return pyslang.ast.VisitAction.Advance
    tree.root.visit(cb)
    return out


GLUE = ("IntegerBase", "IntegerLiteral", "UnbasedUnsizedLiteral")


def emit(toks, sep):
    """Join tokens with `sep` between them, keeping a based literal's pieces
    (`16`, `'h`, `BEEF`) together when the source wrote them together."""
    out = [toks[0][1]]
    for i in range(1, len(toks)):
        k, raw, triv = toks[i]
        pk = toks[i - 1][0]
        glued = not triv and ((k in GLUE and pk in ("IntegerLiteral", "IntegerBase"))
                              or pk == "IntegerBase")
        out.append("" if glued else sep)
        out.append(raw)
    return "".join(out) + "\n"


def oneline(text):
    return emit(tokens(text), " ")


def tokline(text):
    return emit(tokens(text), "\n")


def blank(text, k):
    return "\n" * k + text


def reindent(text, prefix):
    return "\n".join(prefix + ln.lstrip() if ln.strip() else ln
                     for ln in text.splitlines()) + "\n"


def commabreak(text):
    return re.sub(r",\s*", ",\n    ", text)


# ---------------------------------------------------------------- renaming

def internal_names(text, top):
    """Internal signals (nets/variables that are not ports), genvars and
    generate-block labels of module `top`, from slang's elaborated tree."""
    tree = syntax.SyntaxTree.fromText(text, "x.sv")
    comp = pyslang.ast.Compilation()
    comp.addSyntaxTree(tree)
    inst = [i for i in comp.getRoot().topInstances if i.name == top][0]
    ports = {p.name for p in inst.body.portList}
    sigs, genvars, labels = set(), set(), set()

    def visit(sym):
        k = str(sym.kind).split(".")[-1]
        if k in ("Net", "Variable") and sym.name and sym.name not in ports:
            sigs.add(sym.name)
        elif k == "Genvar":
            genvars.add(sym.name)
        elif k in ("GenerateBlockArray", "GenerateBlock") and sym.name:
            labels.add(sym.name)
        return pyslang.ast.VisitAction.Advance
    inst.body.visit(visit)
    # syntax-level labels (`begin : g_bit`), of generate arms not elaborated too
    labels |= set(re.findall(r"begin\s*:\s*(\w+)", text))
    return sigs, genvars, labels


def rename_tokens(text, mapping):
    """Rename identifier tokens by `mapping`, keeping all other text as is."""
    out, pos = [], 0
    for k, raw, _ in tokens(text):
        j = text.index(raw, pos)
        out.append(text[pos:j])
        out.append(mapping.get(raw, raw) if k == "Identifier" else raw)
        pos = j + len(raw)
    out.append(text[pos:])
    return "".join(out)


def rename_signals(text, top, style, seed=0):
    names = sorted(internal_names(text, top)[0])
    if style == "prefix":
        m = {n: "zz_" + n for n in names}
    elif style == "reverse":      # reverses the names' alphabetical order
        m = {n: "w%03d" % (len(names) - i) for i, n in enumerate(names)}
    elif style == "random":
        perm = list(range(len(names)))
        random.Random(seed).shuffle(perm)
        m = {n: "n%03d" % perm[i] for i, n in enumerate(names)}
    elif style == "long":
        m = {n: n + "_" + "q" * 40 for n in names}
    else:
        raise ValueError(style)
    return rename_tokens(text, m)


def rename_labels(text, top):
    _, genvars, labels = internal_names(text, top)
    m = {n: "lbl_" + n[::-1] for n in labels}
    m.update({n: "gv_" + n for n in genvars})
    return rename_tokens(text, m)


# ---------------------------------------------------------------- ordering

DECL_KINDS = {"DataDeclaration", "NetDeclaration", "GenvarDeclaration",
              "ParameterDeclarationStatement", "TypedefDeclaration"}


def reorder(text, top, how, seed=0):
    """Module `top`'s declarations hoisted to the top (in order), then its
    other items in the original, reversed or a shuffled order. Other modules
    of the file are kept as they are."""
    tree = syntax.SyntaxTree.fromText(text, "x.sv")
    r = tree.root
    mods = [r] if str(r.kind).endswith("ModuleDeclaration") else \
        [m for m in r.members if str(m.kind).endswith("ModuleDeclaration")]
    out = []
    for mod in mods:
        if mod.header.name.valueText != top:
            out.append(str(mod).strip())
            continue
        items = list(mod.members)
        decls = [m for m in items if str(m.kind).split(".")[-1] in DECL_KINDS]
        rest = [m for m in items if str(m.kind).split(".")[-1] not in DECL_KINDS]
        if how == "reverse":
            rest = rest[::-1]
        elif how == "shuffle":
            random.Random(seed).shuffle(rest)
        body = "".join("\n  " + str(m).strip() for m in decls + rest)
        out.append(str(mod.header).rstrip() + body + "\nendmodule")
    return "\n\n".join(out) + "\n"


# ---------------------------------------------------------------- commutation

COMMUTATIVE = {"BinaryAndExpression", "BinaryOrExpression", "BinaryXorExpression",
               "BinaryXnorExpression", "EqualityExpression", "InequalityExpression",
               "LogicalAndExpression", "LogicalOrExpression"}


def commute(text):
    tree = syntax.SyntaxTree.fromText(text, "x.sv")

    def pr(n):
        if isinstance(n, parsing.Token):
            lead = "".join(str(tv.getRawText()) for tv in n.trivia) if n.trivia else ""
            return lead + n.rawText
        k = str(n.kind).split(".")[-1]
        kids = [n[i] for i in range(len(n))]
        if k in COMMUTATIVE and len(kids) == 3:
            return " ((" + pr(kids[2]) + ") " + pr(kids[1]).strip() + " (" + pr(kids[0]) + ")) "
        return "".join(pr(c) for c in kids if c is not None)
    return pr(tree.root) + "\n"


# ---------------------------------------------------------------- the table

VARIANTS = {
    "nocomment": ("layout", lambda t, top: t),
    "blank1": ("layout", lambda t, top: blank(t, 1)),
    "blank5": ("layout", lambda t, top: blank(t, 5)),
    "blank30": ("layout", lambda t, top: blank(t, 30)),
    "blank1000": ("layout", lambda t, top: blank(t, 1000)),
    "oneline": ("layout", lambda t, top: oneline(t)),
    "tokline": ("layout", lambda t, top: tokline(t)),
    "indent0": ("layout", lambda t, top: reindent(t, "")),
    "indent8": ("layout", lambda t, top: reindent(t, "        ")),
    "tabs": ("layout", lambda t, top: reindent(t, "\t\t")),
    "commabreak": ("layout", lambda t, top: commabreak(t)),
    "ren_prefix": ("rename", lambda t, top: rename_signals(t, top, "prefix")),
    "ren_reverse": ("rename", lambda t, top: rename_signals(t, top, "reverse")),
    "ren_random": ("rename", lambda t, top: rename_signals(t, top, "random", 1)),
    "ren_long": ("rename", lambda t, top: rename_signals(t, top, "long")),
    "ren_labels": ("rename", lambda t, top: rename_labels(t, top)),
    "hoist": ("order", lambda t, top: reorder(t, top, "hoist")),
    "reverse": ("order", lambda t, top: reorder(t, top, "reverse")),
    "shuffle1": ("order", lambda t, top: reorder(t, top, "shuffle", 1)),
    "shuffle2": ("order", lambda t, top: reorder(t, top, "shuffle", 2)),
    "shuffle3": ("order", lambda t, top: reorder(t, top, "shuffle", 3)),
    "shuffle4": ("order", lambda t, top: reorder(t, top, "shuffle", 4)),
    "commute": ("commute", lambda t, top: commute(t)),
}
KIND = {k: [v for v, (kk, _) in VARIANTS.items() if kk == k]
        for k in ("layout", "rename", "order", "commute")}


def make_variants(path, top, outdir, names=None):
    """{variant: path}; a variant that does not apply raises."""
    nc = nocomment(canonical(path))
    stem = os.path.splitext(os.path.basename(path))[0]
    os.makedirs(outdir, exist_ok=True)
    out = {}
    for name, (_, f) in VARIANTS.items():
        if names and name not in names:
            continue
        p = os.path.join(outdir, f"{stem}.{name}.sv")
        with open(p, "w") as fh:
            fh.write(f(nc, top))
        out[name] = p
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("design")
    ap.add_argument("--top", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--only", default="")
    args = ap.parse_args()
    names = [v for v in args.only.split(",") if v] or None
    for v, p in make_variants(args.design, args.top, args.out, names).items():
        print(f"{v:12s} {VARIANTS[v][0]:8s} {p}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

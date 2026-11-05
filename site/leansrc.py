"""Lean source for the svGolf site: the declarations of a Lean file, found by name, and the file
rendered verbatim with an anchor on every line and every declaration.

`declarations(text)` indexes the top-level declarations of a Lean 4 file the way a reader finds
them: a `def`/`abbrev`/`theorem`/`structure`/... at the start of a line, its full name made from
the enclosing `namespace`s, its extent from its doc comment (and attributes) to the line before the
next command, with a notation declared right after it for it (`scoped infix " ⊨₂ " => Models2`)
counted as part of it. Comments and strings are masked first (highlight.py's tokenizer decides
what is one), so prose in a module docstring is never taken for a declaration. `excerpt` is the
text of one declaration, VERBATIM: the lines of the file, unchanged.

`anchored_html(text, decls)` is `text` as the inside of a `<pre><code>`: highlighted, one
`<span class="ln" id="L<n>" data-n="<n>">` per line (style.css draws the number from `data-n`, so
copying the text never copies a number) and one `<span class="decl" id="<full name>">` around each
declaration's lines. Its text content is `text`, byte for byte (the tags add no character).

Standard library only. Not a Lean parser: it reads the layout every svGolf and ls-sv file uses
(commands at column 0, their bodies indented), and `tests/site/test_units.py` checks that every
declaration a task's `properties.json` names is found in the file it names.
"""

import html
import re

from highlight import tokens

KEYWORDS = ("def", "abbrev", "theorem", "lemma", "structure", "inductive", "class", "instance",
            "opaque", "axiom")
MODIFIERS = ("private", "protected", "noncomputable", "partial", "unsafe", "nonrec")
_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:" + "|".join(MODIFIERS) + r")\s+)*"
    r"(?P<kw>class\s+inductive|" + "|".join(KEYWORDS) + r")\s+(?P<name>[^\s:({\[⦃]+)")
_ATTR = re.compile(r"^@\[[^\]]*\]\s*$")
_NAMESPACE = re.compile(r"^namespace\s+(\S+)")
_SECTION = re.compile(r"^(?:noncomputable\s+)?section\b(?:\s+(\S+))?")
_MUTUAL = re.compile(r"^mutual\b")
_END = re.compile(r"^end\b(?:\s+(\S+))?")
# a line that continues the command above it although it starts at column 0
_CONTINUES = re.compile(r"^(?:\||deriving\b|termination_by\b|decreasing_by\b|where\b)")
_NOTATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:scoped|local)\s+)?(?:infixl|infixr|infix|notation|prefix|postfix)\b"
    r".*=>\s*(?P<target>[^\s()]+)\s*$")


class Decl:
    """One declaration: its full name, the keyword, and its lines `start` (its doc comment or
    attribute, if any) to `end` (exclusive), 0-based; `head` is the line of the keyword."""

    def __init__(self, name, keyword, start, head, end):
        self.name, self.keyword, self.start, self.head, self.end = name, keyword, start, head, end

    @property
    def short(self):
        return self.name.rsplit(".", 1)[-1]

    def __repr__(self):
        return f"Decl({self.name!r}, lines {self.start + 1}-{self.end})"


def _masked_lines(text):
    """The lines of `text` with every comment and string replaced by spaces (newlines kept), and
    the 0-based lines on which a doc comment (`/--`) starts and ends, as {end line: start line}."""
    out, docs, line = [], {}, 0
    for kind, s in tokens(text, "lean"):
        if kind in ("com", "str"):
            if s.startswith("/--"):
                docs[line + s.count("\n")] = line
            out.append(re.sub(r"[^\n]", " ", s))
        else:
            out.append(s)
        line += s.count("\n")
    return "".join(out).split("\n"), docs


def declarations(text):
    """The top-level declarations of a Lean file, in file order (unnamed `instance`s left out)."""
    lines, docs = _masked_lines(text)
    raw = text.split("\n")
    n = len(lines)
    scopes = []                                   # (kind, name): namespace / section / mutual
    heads = []                                    # (line, full name, keyword)
    for i, ln in enumerate(lines):
        if not ln or ln[0].isspace():
            continue
        m = _NAMESPACE.match(ln)
        if m:
            scopes.extend(("namespace", part) for part in m.group(1).split("."))
            continue
        m = _SECTION.match(ln)
        if m:
            scopes.append(("section", m.group(1)))
            continue
        if _MUTUAL.match(ln):
            scopes.append(("mutual", None))
            continue
        m = _END.match(ln)
        if m:
            if m.group(1) and scopes and scopes[-1][0] == "namespace":
                for _ in m.group(1).split("."):
                    if scopes:
                        scopes.pop()
            elif scopes:
                scopes.pop()
            continue
        m = _DECL.match(ln)
        if m:
            name = m.group("name")
            keyword = " ".join(m.group("kw").split())
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join([p for k, p in scopes if k == "namespace"] + [name])
            heads.append((i, full, keyword))
    out, seen = [], set()
    for i, full, keyword in heads:
        start = i
        while start > 0 and _ATTR.match(lines[start - 1]):
            start -= 1
        if start - 1 in docs:
            start = docs[start - 1]
        end = i + 1
        while end < n and (not lines[end].strip() or lines[end][0].isspace() or _CONTINUES.match(lines[end])):
            end += 1
        while end > i + 1 and not lines[end - 1].strip():
            end -= 1                              # trailing blank (or comment-only) lines
        nxt = end
        while nxt < n and not raw[nxt].strip():
            nxt += 1
        if nxt < n:
            m = _NOTATION.match(lines[nxt])
            short = full.rsplit(".", 1)[-1]
            if m and m.group("target") in (short, full):
                end = nxt + 1
        if full not in seen:
            seen.add(full)
            out.append(Decl(full, keyword, start, i, end))
    return out


def find(text, name):
    """The declaration `name` (a full name) of `text`, or None."""
    return next((d for d in declarations(text) if d.name == name), None)


def excerpt(text, decl):
    """The lines of `decl`, verbatim."""
    return "\n".join(text.split("\n")[decl.start:decl.end])


def signature(text, decl):
    """A theorem's statement without its proof: its lines up to the `:=` that opens the proof."""
    body = excerpt(text, decl)
    head = body.split("\n")[decl.head - decl.start:]
    joined = "\n".join(head)
    at = joined.find(":= by")
    if at < 0:
        at = joined.find(":=")
    return (joined[:at].rstrip() + " := …") if at >= 0 else joined


def anchored_html(text, decls=()):
    """`text` as the inside of `<pre><code>`: highlighted, a span with an anchor per line, and a
    span per declaration around its lines (its id the declaration's full name)."""
    lines = [[]]
    for kind, s in tokens(text, "lean"):
        parts = s.split("\n")
        for k, part in enumerate(parts):
            if k:
                lines.append([])
            if part:
                lines[-1].append((kind, part))
    if text.endswith("\n"):
        lines.pop()                               # the newline that ends the file starts no line
    opens = {d.start: d for d in decls}
    closes = {d.end - 1 for d in decls}
    out = []
    for i, toks in enumerate(lines):
        if i in opens:
            out.append(f'<span class="decl" id="{html.escape(opens[i].name, quote=True)}">')
        body = "".join(html.escape(s, quote=False) if k is None else
                       f'<span class="hl-{k}">{html.escape(s, quote=False)}</span>' for k, s in toks)
        out.append(f'<span class="ln" id="L{i + 1}" data-n="{i + 1}">{body}</span>')
        if i in closes:
            out.append("</span>")
        if i < len(lines) - 1 or text.endswith("\n"):
            out.append("\n")
    return "".join(out)

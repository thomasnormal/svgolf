"""A small Markdown renderer for the svGolf site (standard library only).

It renders the few documents the site is built from (svgolf/README.md,
PROVING.md, the task READMEs, site/content/*.md) and nothing more general.
Vendoring a full CommonMark library would break the generator's
standard-library-only rule, and these documents use a small, known subset:

* blocks: ATX headings, paragraphs, fenced code (``` or ~~~, with a
  language), indented code, GFM tables (with alignment), bullet and ordered
  lists (nested by indentation, tight or loose), thematic breaks;
* inlines: code spans (any backtick run), `**strong**`, `*em*`, `_em_`,
  `[text](target)` links, backslash escapes.

Three rules differ from CommonMark / GFM on purpose:

* there is NO raw HTML: anything written as `<...>` is text and is escaped.
  The documents' "tags" are placeholders such as `<name>` or `<task>`;
* a `|` inside a code span does not split a table cell (GFM splits it and
  drops the cells past the header's; the documents mean the code span);
* a construct outside the subset (a blockquote, an image, a reference-style
  link or footnote, a setext heading, tab indentation, a table row with more
  cells than its header) raises MarkdownError naming file:line, instead of
  rendering wrongly.

`render(text, ...)` returns a Rendered (the HTML and the headings with their
anchor ids). Links go through the caller's `resolve_link(target)`, which
returns the href to write or None for "show the text, link nothing"; code
blocks go through `highlight(code, lang)`.
"""

import html
import re

__all__ = ["MarkdownError", "Rendered", "Slugger", "render", "render_inline", "split_blocks", "split_sections"]


class MarkdownError(Exception):
    """An unsupported or malformed construct, with the file and line."""

    def __init__(self, source, line, message):
        super().__init__(f"{source}:{line}: {message}")
        self.source, self.line = source, line


class Rendered:
    def __init__(self, html_text, headings):
        self.html, self.headings = html_text, headings   # headings: [(level, text_html, id)]


class Slugger:
    """GitHub-style heading anchors, unique within one page."""

    def __init__(self, taken=()):
        self.seen = {}
        for t in taken:
            self.seen[t] = 0

    def slug(self, text):
        base = re.sub(r"[^\w\- ]", "", text.lower(), flags=re.UNICODE).strip().replace(" ", "-")
        base = base or "section"
        n = self.seen.get(base)
        self.seen[base] = 0 if n is None else n + 1
        return base if n is None else f"{base}-{n + 1}"


_HEADING = re.compile(r"^ {0,3}(#{1,6})(?:[ \t]+(.*?))?(?:[ \t]+#+)?[ \t]*$")
_FENCE = re.compile(r"^( {0,3})(`{3,}|~{3,})[ \t]*([^`\s]*)[^`]*$")
_LIST = re.compile(r"^( {0,3})([-*+]|\d{1,9}[.)])(?:( +)|$)")
_TABLE_SEP = re.compile(r"^ {0,3}\|?[ \t]*:?-+:?[ \t]*(?:\|[ \t]*:?-+:?[ \t]*)*\|?[ \t]*$")
_HR = re.compile(r"^ {0,3}(?:(?:-[ \t]*){3,}|(?:\*[ \t]*){3,}|(?:_[ \t]*){3,})$")
_SETEXT = re.compile(r"^ {0,3}(?:=+|-+)[ \t]*$")
_UNSUPPORTED = [
    (re.compile(r"^ {0,3}>"), "blockquotes are not supported"),
    (re.compile(r"^ {0,3}\[[^\]]+\]:"), "reference-style link definitions are not supported"),
    (re.compile(r"^ *\t"), "tab indentation is not supported (use spaces)"),
]
# Emphasis, stricter than CommonMark's flanking rules on purpose: a delimiter opens only before a
# word character, a quote, a bracket or a code span, so the `*` of `LeanModels.Sv.*, SvGolf.*` or
# of `a * b` is never read as emphasis; it closes after anything but a space or another delimiter.
# (\x00 and \x01 delimit the placeholders of code spans and links.)
_OPEN = r"(?=[\w\x00\"'(\[])"
_CLOSE = r"(?<=[^\s*_])"
_EMPHASIS = [
    (re.compile(r"(?<![\w*])\*\*" + _OPEN + r"(.+?)" + _CLOSE + r"\*\*(?![\w*])", re.S), "strong"),
    (re.compile(r"(?<![\w_])__" + _OPEN + r"(.+?)" + _CLOSE + r"__(?![\w_])", re.S), "strong"),
    (re.compile(r"(?<![\w*])\*" + _OPEN + r"(.+?)" + _CLOSE + r"\*(?![\w*])", re.S), "em"),
    (re.compile(r"(?<![\w_])_" + _OPEN + r"(.+?)" + _CLOSE + r"_(?![\w_])", re.S), "em"),
]
_PUNCT = set("!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~")


def _indent(line):
    return len(line) - len(line.lstrip(" "))


def _tick_run(text, i):
    """The length of the backtick run that starts at i."""
    j = i
    while j < len(text) and text[j] == "`":
        j += 1
    return j - i


def _esc(s):
    return html.escape(s, quote=False)


def _attr(s):
    return html.escape(s, quote=True)


def split_sections(text):
    """[(level, title, start, end)] of the ATX headings of `text`, with the
    line range [start, end) each heading's section spans (up to the next
    heading of the same or a higher level). Lines are 0-based; fenced code is
    skipped, so a `#` comment inside a code block is not a heading."""
    lines = text.split("\n")
    heads, fence = [], None
    for i, line in enumerate(lines):
        m = _FENCE.match(line)
        if fence:
            if m and m.group(2)[0] == fence[0] and len(m.group(2)) >= len(fence) and not m.group(3):
                fence = None
            continue
        if m:
            fence = m.group(2)
            continue
        h = _HEADING.match(line)
        if h:
            heads.append((len(h.group(1)), (h.group(2) or "").strip(), i))
    out = []
    for k, (level, title, start) in enumerate(heads):
        end = next((s for lv, _, s in heads[k + 1:] if lv <= level), len(lines))
        out.append((level, title, start, end))
    return out


def split_blocks(text):
    """[(start, end, kind)] of the top-level chunks of `text`: runs of non-blank lines, each with its
    0-based line range [start, end); a fenced code block is one chunk, blank lines inside it included.
    `kind` is "fence" (the chunk is a fenced code block), "list" (it starts with a list item) or "text".
    For a caller that shows the parts of a section differently (site/build.py's "Proving a new design")."""
    lines = text.split("\n")
    out, i, n = [], 0, len(lines)
    while i < n:
        if not lines[i].strip():
            i += 1
            continue
        start = i
        m = _FENCE.match(lines[i])
        if m:
            fence = m.group(2)
            i += 1
            while i < n:
                c = _FENCE.match(lines[i])
                i += 1
                if c and c.group(2)[0] == fence[0] and len(c.group(2)) >= len(fence) and not c.group(3):
                    break
            out.append((start, i, "fence"))
            continue
        while i < n and lines[i].strip() and not (i > start and _FENCE.match(lines[i])):
            i += 1
        out.append((start, i, "list" if _LIST.match(lines[start]) else "text"))
    return out


class _Renderer:
    def __init__(self, source, resolve_link, highlight, slugger, heading_shift):
        self.source = source
        self.resolve_link = resolve_link or (lambda target: target)
        self.highlight = highlight or (lambda code, lang: _esc(code))
        self.slugger = slugger or Slugger()
        self.heading_shift = heading_shift
        self.headings = []

    def fail(self, line, message):
        raise MarkdownError(self.source, line, message)

    # -- blocks ------------------------------------------------------------

    def blocks(self, lines, tight=False):
        """HTML for `lines`, a list of (line number, text) pairs."""
        out, i, n = [], 0, len(lines)
        while i < n:
            no, line = lines[i]
            if not line.strip():
                i += 1
                continue
            for pat, why in _UNSUPPORTED:
                if pat.match(line):
                    self.fail(no, why)
            if _FENCE.match(line):
                i = self.fenced(lines, i, out)
            elif _HEADING.match(line):
                self.heading(no, line, out)
                i += 1
            elif self.table_starts(lines, i):
                i = self.table(lines, i, out)
            elif _HR.match(line):
                out.append("<hr>")
                i += 1
            elif _LIST.match(line):
                i = self.list(lines, i, out)
            elif _indent(line) >= 4:
                i = self.indented_code(lines, i, out)
            else:
                i = self.paragraph(lines, i, out, tight)
        return "\n".join(out)

    def starts_block(self, lines, i):
        """True when line i interrupts a paragraph."""
        line = lines[i][1]
        m = _LIST.match(line)
        if m and m.group(3) is not None:          # a list item with content
            if not m.group(2)[0].isdigit() or m.group(2)[:-1] == "1":
                return True
        return bool(_FENCE.match(line) or _HEADING.match(line) or _HR.match(line)
                    or self.table_starts(lines, i))

    def heading(self, no, line, out):
        m = _HEADING.match(line)
        text = (m.group(2) or "").strip()
        level = min(6, len(m.group(1)) + self.heading_shift)
        plain = re.sub(r"[`*]", "", text)
        hid = self.slugger.slug(plain)
        inner = self.inline(text, no)
        self.headings.append((level, inner, hid))
        out.append(f'<h{level} id="{_attr(hid)}">{inner}'
                   f' <a class="anchor" href="#{_attr(hid)}" aria-label="link to this section">#</a>'
                   f"</h{level}>")

    def fenced(self, lines, i, out):
        no, line = lines[i]
        m = _FENCE.match(line)
        indent, fence, lang = len(m.group(1)), m.group(2), m.group(3)
        body, j = [], i + 1
        while j < len(lines):
            text = lines[j][1]
            close = _FENCE.match(text)
            if (close and close.group(2)[0] == fence[0] and len(close.group(2)) >= len(fence)
                    and not close.group(3) and text.strip() == close.group(2)):
                break
            # CommonMark: up to `indent` spaces of the fence's own indentation are removed
            body.append(text[min(indent, _indent(text)):])
            j += 1
        else:
            self.fail(no, f"unterminated code fence {fence}")
        code = "\n".join(body)
        lang_attr = f' data-lang="{_attr(lang)}"' if lang else ""
        out.append(f'<pre class="code"{lang_attr}><code>{self.highlight(code, lang)}</code></pre>')
        return j + 1

    def indented_code(self, lines, i, out):
        body, j = [], i
        while j < len(lines) and (not lines[j][1].strip() or _indent(lines[j][1]) >= 4):
            body.append(lines[j][1][4:])
            j += 1
        while body and not body[-1].strip():
            body.pop()
        out.append(f'<pre class="code"><code>{_esc(chr(10).join(body))}</code></pre>')
        return j

    def paragraph(self, lines, i, out, tight):
        start_no, buf, j = lines[i][0], [], i
        while j < len(lines):
            no, line = lines[j]
            if not line.strip():
                break
            if buf:
                if _SETEXT.match(line):
                    self.fail(no, "setext headings (a line of = or - under text) are not supported")
                if self.starts_block(lines, j):
                    break
                for pat, why in _UNSUPPORTED:
                    if pat.match(line):
                        self.fail(no, why)
            buf.append(line.strip())
            j += 1
        text = self.inline("\n".join(buf), start_no)
        out.append(text if tight else f"<p>{text}</p>")
        return j

    def table_starts(self, lines, i):
        return ("|" in lines[i][1] and i + 1 < len(lines)
                and bool(_TABLE_SEP.match(lines[i + 1][1])) and "-" in lines[i + 1][1])

    def cells(self, line):
        """The cells of a table row. A `|` splits cells unless it is escaped
        (`\\|`) or inside a code span: `` `|a| / |b|` `` is one cell here,
        where GFM would split it (and lose the cells past the header's)."""
        s = line.strip()
        if s.startswith("|"):
            s = s[1:]
        cells, cur, i, n = [], [], 0, len(s)
        while i < n:
            c = s[i]
            if c == "\\" and i + 1 < n and s[i + 1] == "|":
                cur.append("|")
                i += 2
            elif c == "`":
                run = _tick_run(s, i)
                j = self._closing_ticks(s, i + run, run)
                end = i + run if j < 0 else j + run
                cur.append(s[i:end])
                i = end
            elif c == "|":
                cells.append("".join(cur).strip())
                cur, i = [], i + 1
            else:
                cur.append(c)
                i += 1
        if cur and "".join(cur).strip() or not cells:
            cells.append("".join(cur).strip())
        return cells

    def table(self, lines, i, out):
        no = lines[i][0]
        head = self.cells(lines[i][1])
        aligns = []
        for c in self.cells(lines[i + 1][1]):
            left, right = c.startswith(":"), c.endswith(":")
            aligns.append("center" if left and right else "right" if right else "left" if left else None)
        if len(aligns) != len(head):
            self.fail(no, f"table header has {len(head)} cells, its separator {len(aligns)}")
        rows, j = [], i + 2
        while j < len(lines) and lines[j][1].strip() and "|" in lines[j][1]:
            cells = self.cells(lines[j][1])
            if len(cells) > len(head):
                self.fail(lines[j][0], f"table row has {len(cells)} cells, the header {len(head)}")
            rows.append((lines[j][0], cells + [""] * (len(head) - len(cells))))
            j += 1

        def row(tag, row_no, cells):
            tds = []
            for a, c in zip(aligns, cells):
                style = f' class="al-{a}"' if a else ""
                tds.append(f"<{tag}{style}>{self.inline(c, row_no)}</{tag}>")
            return "<tr>" + "".join(tds) + "</tr>"

        body = "\n".join(row("td", rn, cells) for rn, cells in rows)
        out.append(f'<div class="table-wrap"><table>\n<thead>{row("th", no, head)}</thead>\n'
                   f"<tbody>\n{body}\n</tbody></table></div>")
        return j

    def list(self, lines, i, out):
        first = _LIST.match(lines[i][1])
        ordered = first.group(2)[0].isdigit()
        items, loose, j = [], False, i
        while j < len(lines):
            no, line = lines[j]
            m = _LIST.match(line)
            if not m or m.group(2)[0].isdigit() != ordered:
                break
            content = len(m.group(1)) + len(m.group(2)) + (len(m.group(3) or "") or 1)
            if m.group(3) and len(m.group(3)) > 4:          # `-     code`: content starts after one space
                content = len(m.group(1)) + len(m.group(2)) + 1
            body = [(no, line[content:] if len(line) > content else "")]
            j += 1
            blank = False
            while j < len(lines):
                no2, l2 = lines[j]
                if not l2.strip():
                    body.append((no2, ""))
                    blank, j = True, j + 1
                    continue
                if _indent(l2) >= content:
                    body.append((no2, l2[content:]))
                    blank, j = False, j + 1
                    continue
                if blank or _LIST.match(l2) or self.starts_block(lines, j):
                    break
                body.append((no2, l2.strip()))           # a lazy continuation line
                j += 1
            trailing_blank = blank
            while body and not body[-1][1].strip():
                body.pop()
            items.append(body)
            next_is_item = j < len(lines) and bool(_LIST.match(lines[j][1]))
            # loose: a blank line between two items, or between two blocks of one item
            loose |= (trailing_blank and next_is_item) or any(not t.strip() for _, t in body[1:])
            if not next_is_item:
                break
        rendered = [f"<li>{self.blocks(body, tight=not loose)}</li>" for body in items]
        if ordered:
            start = int(first.group(2)[:-1])
            attr = f' start="{start}"' if start != 1 else ""
            out.append(f"<ol{attr}>\n" + "\n".join(rendered) + "\n</ol>")
        else:
            out.append("<ul>\n" + "\n".join(rendered) + "\n</ul>")
        return j

    # -- inlines -----------------------------------------------------------

    def inline(self, text, no):
        stash = []

        def keep(fragment):
            stash.append(fragment)
            return f"\x00{len(stash) - 1}\x01"

        out, i, n = [], 0, len(text)
        while i < n:
            c = text[i]
            if c == "`":
                run = _tick_run(text, i)
                j = self._closing_ticks(text, i + run, run)
                if j < 0:
                    out.append(text[i:i + run])
                    i += run
                    continue
                code = text[i + run:j].replace("\n", " ")
                if len(code) > 1 and code[0] == " " and code[-1] == " " and code.strip():
                    code = code[1:-1]
                out.append(keep(f"<code>{_esc(code)}</code>"))
                i = j + run
            elif c == "\\" and i + 1 < n and text[i + 1] in _PUNCT:
                out.append(keep(_esc(text[i + 1])))
                i += 2
            elif text.startswith("![", i):
                self.fail(no, "images are not supported")
            elif c == "[":
                if text.startswith("[^", i):
                    self.fail(no, "footnotes are not supported")
                try:
                    link = self._link(text, i)
                except ValueError as e:
                    self.fail(no, f"unsupported link: {e}")
                if link is None:
                    out.append(c)
                    i += 1
                    continue
                label, target, i = link
                href = self.resolve_link(target)
                label_html = self.inline(label, no)
                if href is None:
                    out.append(keep(f'<span class="unlinked" title="{_attr(target)}">{label_html}</span>'))
                else:
                    out.append(keep(f'<a href="{_attr(href)}">{label_html}</a>'))
            else:
                out.append(c)
                i += 1
        s = _esc("".join(out))
        for pattern, tag in _EMPHASIS:
            s = pattern.sub(rf"<{tag}>\1</{tag}>", s)
        return re.sub("\x00(\\d+)\x01", lambda m: stash[int(m.group(1))], s)

    @staticmethod
    def _closing_ticks(text, i, run):
        """The start of the next backtick run of exactly `run` ticks, or -1."""
        while True:
            j = text.find("`" * run, i)
            if j < 0:
                return -1
            k = j + run
            if (j == 0 or text[j - 1] != "`") and (k >= len(text) or text[k] != "`"):
                return j
            while k < len(text) and text[k] == "`":
                k += 1
            i = k

    def _link(self, text, i):
        """(label, target, end) of a `[label](target)` link at i, or None."""
        depth, j, n = 0, i, len(text)
        while j < n:
            c = text[j]
            if c == "\\":
                j += 2
                continue
            if c == "`":
                run = _tick_run(text, j)
                k = self._closing_ticks(text, j + run, run)
                j = j + run if k < 0 else k + run
                continue
            if c == "[":
                depth += 1
            elif c == "]":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        else:
            return None
        if not text.startswith("(", j + 1):
            return None
        m = re.match(r"\(([^()\s]*(?:\([^()\s]*\)[^()\s]*)*)\)", text[j + 1:])
        if not m:
            raise ValueError("a link target with spaces, a title or unbalanced parentheses")
        return text[i + 1:j], m.group(1), j + 1 + m.end()


def render(text, *, source="<markdown>", first_line=1, resolve_link=None, highlight=None,
           slugger=None, heading_shift=0):
    """Render a Markdown document (or a fragment of one starting at line
    `first_line` of `source`) to a Rendered."""
    r = _Renderer(source, resolve_link, highlight, slugger, heading_shift)
    lines = list(enumerate(text.split("\n"), first_line))
    return Rendered(r.blocks(lines), r.headings)


def render_inline(text, *, source="<markdown>", line=1, resolve_link=None):
    """One line of inline Markdown (no blocks) as HTML."""
    return _Renderer(source, resolve_link, None, None, 0).inline(text, line)

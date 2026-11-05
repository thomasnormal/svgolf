"""Syntax highlighting for the svGolf site: Lean 4, SystemVerilog and bash.

One small regex tokenizer per language. `tokens(text, lang)` returns
`(kind, text)` pairs whose texts concatenate back to EXACTLY `text` (every
character the patterns do not claim becomes a plain token), and
`highlight(text, lang)` renders them as HTML-escaped text with one
`<span class="hl-KIND">` per highlighted token. Plain tokens carry no span.

Kinds: `com` (comment), `str` (string or character literal), `num`
(number or sized literal), `kw` (keyword), `sys` (SystemVerilog system task
or function), `dir` (compiler directive), `cmd` (the command word of a
shell line), `var` (shell variable), `opt` (shell option).

Standard library only. The tokenizers are meant to make code readable, not
to parse it: a construct they misread is shown in the wrong colour, never
changed (`tests/site/test_units.py` checks the round trip on every `.lean`
and `.sv` file of svGolf).
"""

import html
import re

LEAN_KEYWORDS = frozenset("""
    abbrev axiom by calc class decreasing_by def deriving do else end example
    extends fun have if import in inductive instance lemma let local macro match
    mutual namespace noncomputable opaque open partial private protected return
    scoped section set_option show structure syntax termination_by then theorem
    universe unsafe variable where with elab macro_rules attribute for unless
    from at sorry admit
""".split())

SV_KEYWORDS = frozenset("""
    module endmodule input output inout logic wire reg bit byte int integer
    shortint longint signed unsigned assign always always_comb always_ff
    always_latch initial begin end generate endgenerate genvar for if else case
    casez casex endcase default parameter localparam function endfunction task
    endtask automatic static return posedge negedge or and not unique unique0
    priority typedef enum struct union packed import export package endpackage
    while repeat forever do break continue void const var tri supply0 supply1
    wand wor timeunit timeprecision interface endinterface modport
""".split())

BASH_KEYWORDS = frozenset("""
    if then else elif fi for while until do done case esac in function select
    time export local return
""".split())

# Each language: an ordered list of (kind, pattern). The first pattern that
# matches at the current position wins. Kind None marks a token that is
# scanned but not highlighted; kind "ident" is looked up in the keyword set.
_LEAN = [
    ("com", r"--[^\n]*"),
    ("blockcom", r"/-"),                       # nested: scanned by _lean_block_comment
    ("str", r'"(?:\\.|[^"\\])*"'),
    ("str", r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'"),
    ("num", r"0[xX][0-9a-fA-F_]+|0[bB][01_]+|\d[\d_]*(?:\.\d+)?"),
    ("kw", r"#[a-z_]+"),                       # #eval, #check, #print, #guard, ...
    ("ident", r"[^\W\d][\w'!?₀-ₜ.]*"),
]

_SV = [
    ("com", r"//[^\n]*"),
    ("com", r"/\*[\s\S]*?(?:\*/|\Z)"),
    ("str", r'"(?:\\.|[^"\\\n])*"?'),
    ("num", r"\d[\d_]*\s*'[sS]?[bBoOdDhH]\s*[0-9a-fA-FxXzZ?_]+"),
    ("num", r"'[sS]?[bBoOdDhH]\s*[0-9a-fA-FxXzZ?_]+|'[01xXzZ]\b"),
    ("num", r"\d[\d_]*(?:\.\d+)?"),
    ("sys", r"\$[A-Za-z_][\w$]*"),
    ("dir", r"`[A-Za-z_]\w*"),
    (None, r"\\\S+"),                          # escaped identifier: never a keyword
    ("ident", r"[A-Za-z_][\w$]*"),
]

_BASH = [
    ("com", r"(?:^|(?<=\s))#[^\n]*"),
    ("str", r'"(?:\\.|[^"\\])*"?'),
    ("str", r"'[^']*'?"),
    ("var", r"\$\{[^}\n]*\}|\$[A-Za-z_]\w*|\$[0-9#?@*$!-]"),
    ("opt", r"(?:^|(?<=\s))--?[A-Za-z][\w-]*"),
    ("ident", r"[A-Za-z0-9_./][\w./+-]*"),
]

LANGS = {"lean": (_LEAN, LEAN_KEYWORDS), "sv": (_SV, SV_KEYWORDS), "bash": (_BASH, BASH_KEYWORDS)}

# Fence info strings and file extensions that name a language.
ALIASES = {"lean": "lean", "lean4": "lean", "systemverilog": "sv", "sv": "sv", "verilog": "sv",
           "v": "sv", "bash": "bash", "sh": "bash", "shell": "bash", "console": "bash"}


def language_of(name):
    """The tokenizer for a fence info string or a file name, or None (plain)."""
    if not name:
        return None
    key = name.lower()
    if "." in key:
        key = key.rsplit(".", 1)[1]
    return ALIASES.get(key)


def _compile(rules):
    return re.compile("|".join(f"(?P<g{i}>{pat})" for i, (_, pat) in enumerate(rules)), re.M)


_COMPILED = {lang: (_compile(rules), rules, kws) for lang, (rules, kws) in LANGS.items()}


def _lean_block_comment(text, i):
    """The end of the (nested) Lean block comment that starts at `i`."""
    depth, j, n = 0, i, len(text)
    while j < n:
        if text.startswith("/-", j):
            depth += 1
            j += 2
        elif text.startswith("-/", j):
            depth -= 1
            j += 2
            if depth == 0:
                return j
        else:
            j += 1
    return n


def _bash_word(kind, word, at_command, keywords, *, assigned, assigns):
    """The kind of a bash token and whether the next word is a command. The
    first word of a line (or after `;`, `|`, `&&`, a keyword such as `then`)
    is the command; `NAME=value` before it is an assignment, which keeps the
    command position open."""
    if kind == "ident" and assigns and at_command:
        return "var", True                        # `LEAN_PATH=...` before the command
    if assigned:
        return (None if kind == "ident" else kind), at_command
    if kind == "ident":
        if word in keywords:
            return "kw", word in _BASH_COMMAND_AFTER
        return ("cmd" if at_command else None), False
    return kind, at_command if kind == "com" else False


_BASH_COMMAND_AFTER = frozenset(("if", "then", "else", "elif", "do", "while", "until", "time"))


def tokens(text, lang):
    """`(kind, text)` pairs covering `text` exactly; kind None is plain."""
    if lang not in _COMPILED:
        return [(None, text)] if text else []
    pattern, rules, keywords = _COMPILED[lang]
    out, plain, i, n = [], [], 0, len(text)
    at_command = True                             # bash: the next word is a command

    def emit(kind, s):
        if kind is None:
            plain.append(s)
            return
        if plain:
            out.append((None, "".join(plain)))
            plain.clear()
        out.append((kind, s))

    while i < n:
        m = pattern.match(text, i)
        if not m or m.end() == i:
            ch = text[i]
            emit(None, ch)
            if lang == "bash" and ch in "\n;|&(`":
                # a backslash-newline continues the command; any other newline ends it
                at_command = not (ch == "\n" and i > 0 and text[i - 1] == "\\")
            i += 1
            continue
        kind = rules[int(m.lastgroup[1:])][0]
        end = m.end()
        if kind == "blockcom":
            kind, end = "com", _lean_block_comment(text, i)
        word = text[i:end]
        if lang == "bash":
            kind, at_command = _bash_word(kind, word, at_command, keywords,
                                          assigned=i > 0 and text[i - 1] == "=",
                                          assigns=text.startswith("=", end))
        elif kind == "ident":
            kind = "kw" if word in keywords else None
        emit(kind, word)
        i = end
    if plain:
        out.append((None, "".join(plain)))
    return out


def highlight(text, lang):
    """`text` as HTML: escaped, with a span per highlighted token."""
    parts = []
    for kind, s in tokens(text, lang):
        s = html.escape(s, quote=False)
        parts.append(s if kind is None else f'<span class="hl-{kind}">{s}</span>')
    return "".join(parts)

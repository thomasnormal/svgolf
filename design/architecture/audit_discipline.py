#!/usr/bin/env python3
"""audit_discipline.py: the X4 discipline audit of hand-written SystemVerilog testbenches.

The clocking discipline (ARCH-NOTE §4.3, `Disciplined` in `LeanModels/Sv/Kernel/Core1Disc.lean`):
in every time slot where the clock rises, no other input changes. The generated testbenches
(`harness/sv/gen_tb.py`, `gen_tb2.py`) satisfy it by construction (inputs at 3k with the clock
low, posedge alone at 3k+1), and `clockExpand` satisfies it by theorem. This script reads the
hand-written ones (`initial` blocks that drive a clock) and classifies each file:

  no-edge      the testbench never raises the clock;
  generator    the clock is an `always #d` generator (time arithmetic needed: listed for READ);
  ok           every time step that raises the clock assigns nothing else;
  same-step    some time step raises the clock and assigns another variable, and the file is
               not a known scheduling test (none today);
  deliberate   a same-step file that is a deliberate scheduling test, listed with the rule
               that excludes it from the disciplined stimulus (`DELIBERATE` below);
  unparsed     the `initial` block uses constructs this reader does not follow (fork, loops,
               event waits): listed for READ.

A heuristic reader (regular expressions over `initial begin ... end`, sequential `#d` delays), not
a parser. It reads files only; nothing is executed. Usage: `python3 -I audit_discipline.py <dir>...`.
"""
import re
import sys
from pathlib import Path

CLOCKS = ("clk", "clock", "CLK")

# Deliberate scheduling tests (lead's ruling, 2026-11-02): not violations, each excluded by a rule.
DELIBERATE = {
    "always_ff_capture.sv":
        "the clock and `d` change in one time step, and a `#0` pulse uses the Inactive region: "
        "excluded by the discipline (no other input changes in an active-edge slot) and by "
        "E-core-1's slot model (no `#0` events)",
    "events.sv":
        "intra-assignment event controls (`repeat (n) @(posedge clk)`): excluded by the profile "
        "(no timing control inside an assignment)",
    "always_ff_event_iff_neg.sv":
        "`@(negedge clk iff en)`: disciplined under the active-edge rule (D-X1k: the changes "
        "fall on the posedge, its inactive edge); its `iff` guard is excluded by the profile",
}
ASSIGN = re.compile(r"^\s*(?:#\s*(\d+)\s*)?([A-Za-z_][A-Za-z0-9_]*)\s*(<?=)\s*([^;]*);")
DELAY = re.compile(r"#\s*(\d+)")
HARD = re.compile(r"\b(fork|repeat|for|while|forever|wait)\b|@\s*\(")


def initial_blocks(text):
    """The bodies of `initial begin ... end` blocks (begin/end nesting counted)."""
    out = []
    for m in re.finditer(r"\binitial\s+begin\b", text):
        depth, i = 1, m.end()
        for tok in re.finditer(r"\bbegin\b|\bend\b", text[i:]):
            depth += 1 if tok.group(0) == "begin" else -1
            if depth == 0:
                out.append(text[i:i + tok.start()])
                break
    return out


def rises(name, value):
    v = value.replace(" ", "")
    return name in CLOCKS and (v in ("1", "1'b1", "1'h1", "'1") or v == "~" + name or v == "!" + name)


def classify(text):
    if re.search(r"\balways\s+#", text):
        return "generator", []
    blocks = initial_blocks(text)
    drives = [b for b in blocks if any(re.search(r"\b%s\s*<?=" % c, b) for c in CLOCKS)]
    if not drives:
        return "no-edge", []
    findings = []
    for b in drives:
        if HARD.search(b):
            return "unparsed", []
        t, step = 0, {}
        for stmt in b.replace("\n", " ").split(";"):
            stmt = stmt.strip()
            if not stmt:
                continue
            for d in DELAY.findall(stmt):
                t += int(d)
            core = DELAY.sub("", stmt).strip()
            m = ASSIGN.match(core + ";")
            if m:
                step.setdefault(t, []).append((m.group(2), m.group(4).strip()))
        for t, assigns in sorted(step.items()):
            if any(rises(n, v) for n, v in assigns):
                others = [n for n, _ in assigns if n not in CLOCKS]
                if others:
                    findings.append((t, others))
    return ("same-step" if findings else "ok"), findings


def main(dirs):
    rows = {}
    for d in dirs:
        for f in sorted(Path(d).rglob("*.sv")):
            text = f.read_text(errors="replace")
            if "initial" not in text or not any(c in text for c in CLOCKS):
                continue
            kind, findings = classify(text)
            if kind == "same-step" and f.name in DELIBERATE:
                kind, findings = "deliberate", DELIBERATE[f.name]
            rows.setdefault(kind, []).append((str(f), findings))
    for kind in ("ok", "no-edge", "deliberate", "same-step", "generator", "unparsed"):
        items = rows.get(kind, [])
        print("%-10s %d" % (kind, len(items)))
        if kind in ("deliberate", "same-step", "generator", "unparsed"):
            for f, findings in items:
                print("    %s %s" % (f, findings if findings else ""))


if __name__ == "__main__":
    main(sys.argv[1:] or ["."])

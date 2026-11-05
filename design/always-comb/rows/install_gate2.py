#!/usr/bin/env python3
"""Install the staged WP-G rows into a lean-surfaces checkout (Gate 2 step; NOT run in Gate 1).

  python3 install_gate2.py --root /path/to/lean-surfaces            # dry run: prints what it would do
  python3 install_gate2.py --root /path/to/lean-surfaces --apply    # copies, extracts, merges

For every row of cases_wpg.json it
  1. copies <row>/<row>.sv to <root>/Examples/system-verilog/sem2/<row>/,
  2. regenerates the envelope there with `python3.12 extractors/sv/extract.py --top <row>` from <root>
     (the envelope records its repo-relative source path and sha256, so the staged .sv.json is NOT copied),
  3. appends the case to <root>/harness/sv/cases2.json (idempotent: an identical row is left alone, a different
     row of the same name is an error). The file is rewritten with json indent=2, ensure_ascii=False, which
     round-trips the committed file byte for byte, so the diff is exactly the appended rows.
It then prints the Xcelium pin commands (they need the Lean model for the prepare phase, hence the Lean slot).
Plain Python; no Lean, no simulator.
"""
import argparse, json, os, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True)
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--python', default='python3.12', help='interpreter for the extractor')
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    rows = json.load(open(os.path.join(HERE, 'cases_wpg.json')))
    cpath = os.path.join(root, 'harness', 'sv', 'cases2.json')
    raw = open(cpath).read()
    doc = json.loads(raw)
    assert json.dumps(doc, indent=2, ensure_ascii=False) + "\n" == raw, "cases2.json does not round-trip: refuse to rewrite it"
    have = {c['name']: c for c in doc['cases']}
    added = []
    for r in rows:
        n = r['name']
        dest = os.path.join(root, 'Examples', 'system-verilog', 'sem2', n)
        rel = os.path.relpath(os.path.join(dest, n + '.sv'), root)
        print(f"{n}: {'copy+extract -> ' + rel}")
        if n in have:
            if have[n] != r:
                sys.exit(f"{n}: a different row of this name is already in cases2.json")
            print(f"{n}: row already present (identical)")
        else:
            added.append(r)
        if a.apply:
            os.makedirs(dest, exist_ok=True)
            shutil.copyfile(os.path.join(HERE, n, n + '.sv'), os.path.join(dest, n + '.sv'))
            subprocess.run([a.python, os.path.join('extractors', 'sv', 'extract.py'), '--top', n,
                            '-o', rel + '.json', rel],
                           cwd=root, check=True, stdout=subprocess.DEVNULL)
    if added and a.apply:
        doc['cases'].extend(added)
        open(cpath, 'w').write(json.dumps(doc, indent=2, ensure_ascii=False) + "\n")
    print(f"{len(added)} row(s) {'appended' if a.apply else 'to append'} to harness/sv/cases2.json")
    names = "--case " + " ".join(r['name'] for r in rows if 'refusal' not in r)   # nargs="*": ONE --case flag
    print("\nPin on Xcelium (Lean slot for `prepare`; one Xcelium run at a time; scratch copy of the golden file, then merge):")
    print(f"  python3 harness/sv/xcelium_batch.py prepare --workdir $W --lean-wrapper \"$SVGOLF_LEAN_WRAP\" {names}")
    print(f"  python3 harness/sv/xcelium_batch.py run --workdir $W {names}")
    print("  for c in " + " ".join(r['name'] for r in rows) + "; do python3 harness/sv/diff_test2.py --golden --case $c; done   # diff_test2 takes ONE name")
    print("The refusal row wpg_local is not pinned (no testbench is produced for a refused design); its Xcelium trace is in `measured`.")

main()

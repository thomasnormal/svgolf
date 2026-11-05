#!/bin/sh
# Reproduces the measurements of svgolf/design/hierarchy/WP-I-NOTE.md (appendix A). No Lean process.
# Run from the repository root; needs python3.12 with pyslang (the pinned extractor) and yosys 0.53.
set -e
P=svgolf/design/hierarchy/probe
T=${TMPDIR:-/tmp}/wpi-probe
mkdir -p "$T"
echo "== extractor: which nodes stay Unsupported, which instances arrive"
for spec in mul_h:mul_h rec_xor:top rec_xor_base:top conn_forms:top; do
  f=${spec%%:*}; top=${spec##*:}
  echo "-- $f.sv (top $top)"
  python3.12 extractors/sv/extract.py --top "$top" "$P/$f.sv" -o "$T/$f.json" 2>&1 | grep -v '^$' | tail -1 || true
  python3 "$P/summarize.py" "$T/$f.json"
done
echo "== scorer: hierarchy against the flat references (pinned flow, source gate on)"
( cd svgolf
  for N in 4 8; do
    python3.12 score/score.py ../$P/mul_h.sv --top mul_h --param N=$N | python3 -c 'import sys,json; d=json.load(sys.stdin); print("mul_h  N=%d" % d["params"]["N"], d["area_mge"], d["depth"], d["num_gates"])'
    python3.12 score/score.py tasks/mul/reference/mul_n.sv --top mul_n --param N=$N | python3 -c 'import sys,json; d=json.load(sys.stdin); print("mul_n  N=%d" % d["params"]["N"], d["area_mge"], d["depth"], d["num_gates"])'
  done
  python3.12 score/score.py ../Examples/system-verilog/ripple_fa/ripple_fa.sv --top ripple_fa --param N=16 | python3 -c 'import sys,json; d=json.load(sys.stdin); print("ripple_fa N=16", d["area_mge"], d["depth"], d["num_gates"])'
  python3.12 score/score.py tasks/add/reference/add_n.sv --top add_n --param N=16 | python3 -c 'import sys,json; d=json.load(sys.stdin); print("add_n     N=16", d["area_mge"], d["depth"], d["num_gates"])'
)
echo "== equivalence (silent = proved)"
yosys -q -s "$P/equiv.ys"
echo "ok"

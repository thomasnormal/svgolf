#!/bin/bash
# compile-x7.sh: the X7 acceptance (ibex_alu `always_comb` blocks over E-core-0, and the latch fixture,
# X7Blocks.lean), in a scratch directory: the ibex code (third-party) is generated there and never
# enters this repository.
#   X7SRC=<dir>      holds ibex/rtl/ibex_alu.sv and ibex/rtl/ibex_pkg.sv at RB0's pinned commit
#   X7MEASURE=<dir>  holds x7_slice.py, slang_env.py and files.tsv, copied read-only from arch-measure
#                    (svgolf/design/architecture/measure/, svgolf/design/real-world-sv/rb0/files.tsv)
#   SCRATCH=<dir>    where everything is written (default: a fresh temp dir)
#   SVGOLF_LEAN_WRAP=<slot wrapper>  command prefix for lean (optional)
# Needs, built beforehand from the repository root: lake build LeanModels.Sv.CombSlotE
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
SCRATCH=${SCRATCH:-$(mktemp -d)}
mkdir -p "$SCRATCH"
python3.12 -I "$X7MEASURE/x7_slice.py" --src "$X7SRC" --files-tsv "$X7MEASURE/files.tsv" \
  --out "$SCRATCH/slice" --slice "ibex_alu@rv32bnone"
python3.12 -I "$HERE/x7_blocks.py" --slice "$SCRATCH/slice/ibex_alu@rv32bnone/ibex_alu.sv" \
  --out "$SCRATCH/x7blocks"
for b in adder_flags adder_in_a adder_in_b shifter bwlogic result_mux; do
  python3.12 "$ROOT/extractors/sv/extract.py" --top "x7_$b" "$SCRATCH/x7blocks/$b.sv" \
    -o "$SCRATCH/x7blocks/$b.sv.json" > /dev/null
done
python3.12 "$ROOT/extractors/sv/extract.py" --top x7_latch "$HERE/latch.sv" \
  -o "$SCRATCH/x7blocks/latch.sv.json" > /dev/null   # the negative fixture (own code)
cp "$HERE/X7Blocks.lean" "$SCRATCH/"
cd "$ROOT"
LP="$(lake env printenv LEAN_PATH)"
LEAN="$(lake env which lean)"
cd "$SCRATCH"              # load_design_sv2 reads x7blocks/*.sv.json relative to here
${SVGOLF_LEAN_WRAP:-} env LEAN_PATH="$LP" "$LEAN" X7Blocks.lean
echo "scratch: $SCRATCH"

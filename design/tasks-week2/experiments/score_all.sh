#!/bin/bash
# Re-measures every number quoted in README.md with the repo's pinned scorer (svgolf/score/score.py,
# Yosys + ABC, source gate included). Run from svgolf/:  bash design/tasks-week2/experiments/score_all.sh
# Needs python3.12 (pyslang), yosys. Writes only to a temp directory.
set -e
HERE=$(cd "$(dirname "$0")" && pwd); T=$(mktemp -d); cd "$HERE/../../.."
sc() { python3.12 score/score.py "$@" 2>&1 | python3 -c "import sys,json; d=json.load(sys.stdin); print('   %9.3f GE  depth %3d' % (d['area_ge'], d['depth']))"; }
echo "== keccak_round (textbook), W=16,64";  for W in 16 64; do sc design/tasks-week2/keccak_round/reference/keccak_round.sv --top keccak_round --param W=$W; done
echo "== keccak_round chi as a^c^(b&c), W=16"; sc design/tasks-week2/keccak_round/reference/keccak_round_xor3.sv --top keccak_round --param W=16
echo "== aes_sbox: case table, Boyar-Peralta 113-gate SLP"
sc design/tasks-week2/aes_sbox/reference/sbox_table.sv --top sbox_table; sc design/tasks-week2/aes_sbox/reference/sbox_bp.sv --top sbox_bp
echo "== clmul, N=16 and 32: schoolbook, Karatsuba with base 1,2,4,8"
for N in 16 32; do for cfg in "school 1" "kara 1" "kara 2" "kara 4" "kara 8"; do set -- $cfg
  python3 design/tasks-week2/experiments/clmul_gen.py $N $1 $2 $T/c.sv; sc $T/c.sv --top clmul; done; done
echo "== CRC-32 over 32 data bits: subset-XOR, Paar greedy CSE"
( cd $T && python3 "$HERE/crc_gen.py" 32 >/dev/null ); sc $T/crc_plain_32.sv --top crcm; sc $T/crc_paar_32.sv --top crcm
echo "== ChaCha quarter round: adders from gates (ripple), Yosys +"
( cd $T && python3 "$HERE/chacha_qr_gen.py" ); sc $T/qr_ripple.sv --top qr; sc $T/qr_plus.sv --top qr

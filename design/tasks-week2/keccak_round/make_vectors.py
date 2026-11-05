"""Writes vectors.json: golden (W, a, rc, y) rows. `source` says where y comes from.
 xkcp   : XKCP tests/TestVectors/KeccakF-<25W>-IntermediateValues.txt, round r of example e
          (a = the state before the round, y = 'After iota' of that round), fetched 2026-10-30.
 sha3   : state after absorbing the padded empty message (hashlib-verified permutation), round 0 input.
 oracle : produced by oracle.py (two agreeing implementations); no published vector for this width.
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oracle import *
from validate import parse_xkcp, lanes_to_int

rows = []
here = os.path.dirname(os.path.abspath(__file__))
for W in (8, 16, 32, 64):
    steps = parse_xkcp(os.path.join(here, "xkcp", f"KeccakF-{25*W}.txt"))
    rounds = 12 + 2 * (W.bit_length() - 1)
    for ex in (0,):
        s = 0
        for r in range(rounds):
            y = lanes_to_int(W, steps[(ex, r, "iota")])
            if r in (0, 1, 2, rounds - 1):
                rows.append({"W": W, "rc": RC64[r] & ((1 << W) - 1), "a": s, "y": y,
                             "source": f"xkcp KeccakF-{25*W}-IntermediateValues example {ex} round {r}"})
            s = y
# SHA3-256("") padded block through round 0 of Keccak-f[1600]
blk = bytearray(200); blk[0] ^= 0x06; blk[135] ^= 0x80
a = int.from_bytes(bytes(blk), "little")
rows.append({"W": 64, "rc": RC64[0], "a": a, "y": round_lanes(64, a, RC64[0]),
             "source": "sha3: round 0 of the permutation inside SHA3-256(''); the 24 rounds' composition equals hashlib.sha3_256"})
rnd = __import__("random").Random(2026)
for W in (1, 2, 4):
    for _ in range(2):
        a = rnd.getrandbits(25 * W); rc = rnd.getrandbits(W)
        rows.append({"W": W, "rc": rc, "a": a, "y": round_lanes(W, a, rc), "source": "oracle (no published vector at this width)"})
json.dump({"_format": "ints; state packing = flat bit index W*(5*y+x)+z (FIPS 202 3.1.2)", "rows": rows},
          open(os.path.join(here, "vectors.json"), "w"), indent=1)
print(len(rows), "rows")

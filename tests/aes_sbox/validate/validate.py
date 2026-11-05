#!/usr/bin/env python3.12
"""Independent cross-checks of task `aes_sbox`, and simulation of its designs (Verilator).

    python3.12 tests/aes_sbox/validate/validate.py [--good DESIGN.sv ...] [--bad DESIGN.sv ...]
                                                   [--only table,anchors,aes,bp,vectors,sim]

Steps (default: all; every step prints one line and the script exits 0 iff all passed):

  table    tasks/aes_sbox/oracle.py equals the 256-entry table `vectors.json`, which was PARSED
           from Table 4 of FIPS 197 (2023 edition, NIST PDF; source and date in the file), and the
           table is a permutation of the bytes;
  anchors  the standard's own worked values: S(53) = ed (Section 5.1.1), S(00) = 63, S(ff) = 16,
           the first row of Table 4, {57} * {13} = {fe} (2023 text, Equation 4.7) and
           {57} * {83} = {c1} (2001 text), all through the oracle's GF(2^8) arithmetic;
  aes      a textbook AES-128 built on the oracle's S-box reproduces the FIPS 197 (2001)
           Appendix C.1 ciphertext (key 000102..0f, plaintext 00112233..ff ->
           69c4e0d86a7b0430d8cdb78070b4c55a), and agrees with OpenSSL's AES-128 (the `cryptography`
           package) on 300 random blocks (a wrong table entry would be hit; skipped, and said so,
           when `cryptography` is not installed);
  bp       the two Boyar-Peralta netlists of the Yale page
           https://www.cs.yale.edu/homes/peralta/CircuitStuff/ (pinned URL and sha256 in NETLISTS;
           they carry no licence, so they are NOT committed: the step downloads each once, verifies
           its sha256 and caches it next to this script under the name below, gitignored; offline
           and without a cached copy the step is SKIPPED, and says so):
           `SLP_AES_113.txt` (113 gates) and `SLP_AES_125_depth16.txt` (the page's AESDEPTH16SIZE125,
           125 gates, depth 16) are translated gate for gate: tasks/aes_sbox/reference/sbox_bp.sv
           and tests/aes_sbox/baselines/sbox_bp_d16.sv have the same gates in the same order with
           the same names, input U<i> = x[7-i], output S<i> = y[7-i], `+` = ^, `x` = &,
           `#` (XNOR) = ^ 1'b1; each netlist's own evaluation (Python) equals the table on all 256
           inputs; the gate counts and the depth (levels) are computed here and checked;
  vectors  the post-synthesis check is EXHAUSTIVE: with task.json's `postsynth` block, the full vector
           set (fixed vectors + task corners) and the LIGHT one (`light_vectors`) both contain all
           256 inputs, recomputed with check/postsynth.py's own `fixed_vectors` and `light_select`
           (the generic fixed vectors are 18 distinct inputs, the task corners the other 238);
  sim      every design of --good simulated in Verilator on ALL 256 inputs against the oracle's
           table: 0 mismatches; every design of --bad: at least one mismatch (a negative design
           that is right would be a bad test). The testbench compares with `!==`; Verilator is
           2-state, so an `x` output cannot show here (that is the checker's `fourstate` and
           `postsynth` job): this checks the FUNCTION.

Needs verilator (5) for `sim`.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(SVGOLF, "tasks", "aes_sbox"))
sys.dont_write_bytecode = True
from oracle import gmul, sbox  # noqa: E402

VECTORS = os.path.join(HERE, "vectors.json")
REF_SV = os.path.join(SVGOLF, "tasks", "aes_sbox", "reference", "sbox_bp.sv")
TABLE = [sbox(x) for x in range(256)]


def table():
    t = json.load(open(VECTORS))["table"]["values"]
    assert len(t) == 256, len(t)
    bad = [x for x in range(256) if t[x] != TABLE[x]]
    assert not bad, f"oracle differs from FIPS 197 Table 4 at {bad[:5]}"
    assert len(set(TABLE)) == 256, "not a permutation"
    return "oracle = FIPS 197 Table 4 (parsed from the NIST PDF) on all 256 entries; a permutation"


def anchors():
    v = json.load(open(VECTORS))
    for a in v["anchors"]:
        assert TABLE[a["x"]] == a["y"], a
    assert TABLE[0x53] == 0xED and TABLE[0x00] == 0x63 and TABLE[0xFF] == 0x16 and TABLE[0x01] == 0x7C
    assert TABLE[:16] == [0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b,
                          0xfe, 0xd7, 0xab, 0x76]
    for p in v["gf_products"]:
        assert gmul(p["a"], p["b"]) == p["ab"], p
    return "S(53)=ed, S(00)=63, S(ff)=16, row 0 of Table 4, {57}*{13}={fe}, {57}*{83}={c1}"


def aes128_encrypt(key, pt):
    """Textbook AES-128 (FIPS 197 Section 5), column-major state, on the oracle's S-box."""
    def xt(a):
        return ((a << 1) ^ 0x11B) & 0xFF if a & 0x80 else a << 1

    def mc(a):
        return [xt(a[0]) ^ (xt(a[1]) ^ a[1]) ^ a[2] ^ a[3],
                a[0] ^ xt(a[1]) ^ (xt(a[2]) ^ a[2]) ^ a[3],
                a[0] ^ a[1] ^ xt(a[2]) ^ (xt(a[3]) ^ a[3]),
                (xt(a[0]) ^ a[0]) ^ a[1] ^ a[2] ^ xt(a[3])]
    w, rcon = [list(key[4 * i:4 * i + 4]) for i in range(4)], 1
    for i in range(4, 44):
        t = list(w[i - 1])
        if i % 4 == 0:
            t = [TABLE[t[1]] ^ rcon, TABLE[t[2]], TABLE[t[3]], TABLE[t[0]]]
            rcon = xt(rcon)
        w.append([w[i - 4][j] ^ t[j] for j in range(4)])
    rk = [sum(w[4 * r:4 * r + 4], []) for r in range(11)]
    s = [pt[i] ^ rk[0][i] for i in range(16)]
    for r in range(1, 11):
        s = [TABLE[b] for b in s]
        s = [s[(i + 4 * (i % 4)) % 16] for i in range(16)]          # ShiftRows
        if r < 10:
            s = sum([mc(s[4 * c:4 * c + 4]) for c in range(4)], [])  # MixColumns
        s = [s[i] ^ rk[r][i] for i in range(16)]
    return bytes(s)


def aes():
    a = json.load(open(VECTORS))["aes128"]
    ct = aes128_encrypt(bytes.fromhex(a["key"]), bytes.fromhex(a["plaintext"]))
    assert ct.hex() == a["ciphertext"], ct.hex()
    try:
        from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    except ImportError:
        return "FIPS 197 Appendix C.1 ciphertext reproduced; OpenSSL comparison SKIPPED (no `cryptography`)"
    import random
    rnd, n = random.Random(9), 0
    for _ in range(300):
        key = bytes(rnd.getrandbits(8) for _ in range(16))
        pt = bytes(rnd.getrandbits(8) for _ in range(16))
        enc = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
        assert enc.update(pt) + enc.finalize() == aes128_encrypt(key, pt), (key.hex(), pt.hex())
        n += 1
    return f"FIPS 197 Appendix C.1 ciphertext reproduced; {n} random blocks agree with OpenSSL AES-128"


# The Boyar-Peralta netlists: (cache file name, URL, sha256, the SystemVerilog translation,
# (gates, depth, AND, XOR, XNOR)). The sha256 are those of the files as fetched on 2026-10-30
# (re-fetched and equal on 2026-11-04).
BP_PAGE = "https://www.cs.yale.edu/homes/peralta/CircuitStuff/"
NETLISTS = [
    ("SLP_AES_113.txt", BP_PAGE + "SLP_AES_113.txt",
     "de1d21c85eaa1e4146f24b59a4f8bae515757f2a7d0011527841ebb5518b55c0",
     os.path.join(SVGOLF, "tasks", "aes_sbox", "reference", "sbox_bp.sv"), (113, 27, 32, 77, 4)),
    ("SLP_AES_125_depth16.txt", BP_PAGE + "AESDEPTH16SIZE125",
     "b72f635d5a58e06b44d4040b95901da27418ec5a037f9123392155e96966f162",
     os.path.join(SVGOLF, "tests", "aes_sbox", "baselines", "sbox_bp_d16.sv"), (125, 16, 34, 87, 4)),
]


class Unavailable(Exception):
    """A pinned third-party file is neither cached nor downloadable (offline): the step is skipped."""


def fetch_pinned(name, url, sha):
    """The bytes of the pinned file `name`: the cached copy next to this script when its sha256 is the pinned
    one, else a fresh download from `url`, verified BEFORE it is cached (a wrong download is an error, never
    cached). `Unavailable` when there is no cached copy and the download fails."""
    path = os.path.join(HERE, name)
    if os.path.isfile(path):
        raw = open(path, "rb").read()
        if hashlib.sha256(raw).hexdigest() == sha:
            return raw
    try:
        with urllib.request.urlopen(url, timeout=60) as resp:
            raw = resp.read()
    except OSError as e:
        raise Unavailable(f"{name}: no cached copy with the pinned sha256, and the download of {url} failed ({e})")
    got = hashlib.sha256(raw).hexdigest()
    assert got == sha, f"{name}: the download of {url} has sha256 {got}, not the pinned {sha}"
    fd, part = tempfile.mkstemp(prefix=name + ".", suffix=".part", dir=HERE)
    with os.fdopen(fd, "wb") as out:
        out.write(raw)
    os.chmod(part, 0o644)
    os.replace(part, path)
    return raw


def check_netlist(slp_name, url, sha, sv_path, want):
    raw = fetch_pinned(slp_name, url, sha)
    prog = []
    for line in raw.decode().splitlines():
        m = re.fullmatch(r"(\w+) = (\w+) ([+x#]) (\w+)", line.strip())
        if m:
            prog.append(m.groups())
    assert len(prog) == want[0], f"{slp_name}: {len(prog)} gates, expected {want[0]}"

    def src_name(n):
        m = re.fullmatch(r"U(\d)", n)
        if m:
            return f"x[{7 - int(m.group(1))}]"
        m = re.fullmatch(r"S(\d)", n)
        if m:
            return f"y[{7 - int(m.group(1))}]"
        return n
    wanted = []
    for d, a, o, b in prog:
        rhs = {"+": f"{src_name(a)} ^ {src_name(b)}", "x": f"{src_name(a)} & {src_name(b)}",
               "#": f"{src_name(a)} ^ {src_name(b)} ^ 1'b1"}[o]
        wanted.append(f"assign {src_name(d)} = {rhs};")
    code = re.sub(r"//[^\n]*", "", open(sv_path).read())
    got = [" ".join(s.split()) for s in re.findall(r"assign[^;]*;", code)]
    assert got == wanted, next((f"{os.path.basename(sv_path)} gate {i}: {g!r} != {w!r}"
                                for i, (g, w) in enumerate(zip(got, wanted)) if g != w),
                               f"{len(got)} gates against {len(wanted)}")
    for x in range(256):
        env = {f"U{i}": (x >> (7 - i)) & 1 for i in range(8)}
        for d, a, o, b in prog:
            env[d] = env[a] ^ env[b] if o == "+" else env[a] & env[b] if o == "x" else 1 ^ env[a] ^ env[b]
        assert sum(env[f"S{i}"] << (7 - i) for i in range(8)) == TABLE[x], f"{slp_name}: x = {x:#04x}"
    depth = {f"U{i}": 0 for i in range(8)}
    for d, a, o, b in prog:
        depth[d] = max(depth[a], depth[b]) + 1
    kinds = tuple(sum(1 for p in prog if p[2] == k) for k in "x+#")
    got_shape = (len(prog), max(depth[f"S{i}"] for i in range(8))) + kinds
    assert got_shape == want, f"{slp_name}: (gates, depth, AND, XOR, XNOR) = {got_shape}, expected {want}"
    return (f"{os.path.basename(sv_path)} = {slp_name} gate for gate ({got_shape[0]} gates: {got_shape[2]} "
            f"AND, {got_shape[3]} XOR, {got_shape[4]} XNOR; depth {got_shape[1]} levels), and the "
            "netlist equals the table on all 256 inputs")


def bp():
    try:
        return "; ".join(check_netlist(*n) for n in NETLISTS)
    except Unavailable as e:
        return f"SKIPPED (offline: the Boyar-Peralta netlists are fetched, not committed): {e}"


def vectors():
    sys.path.insert(0, os.path.join(SVGOLF, "check"))
    sys.path.insert(0, os.path.join(SVGOLF, "score"))
    import postsynth
    task = json.load(open(os.path.join(SVGOLF, "tasks", "aes_sbox", "task.json")))
    cfg = postsynth.config(task)
    ins = [("x", 8)]
    fixed, nfixed = postsynth.fixed_vectors(ins, cfg["corners"])
    full = postsynth.dedup(ins, fixed)
    light, _ = postsynth.light_select(fixed, nfixed, [], 0, [], int(cfg["light_vectors"]))
    light = postsynth.dedup(ins, light)
    assert cfg["random"] == 0
    assert sorted(v["x"] for v in full) == list(range(256)), f"full mode: {len(full)} distinct inputs"
    assert sorted(v["x"] for v in light) == list(range(256)), f"light mode: {len(light)} distinct inputs"
    return (f"full and light post-synthesis vector sets are both all 256 inputs "
            f"({nfixed} generic fixed vectors, {len(fixed) - nfixed} task corners, light_vectors "
            f"{cfg['light_vectors']})")


TB = """module tb;
  logic [7:0] x;
  wire  [7:0] y;
  logic [7:0] exp [0:255];
  integer i, errors;
  aes_sbox dut (.x(x), .y(y));
  initial begin
    $readmemh("exp.hex", exp);
    errors = 0;
    for (i = 0; i < 256; i = i + 1) begin
      x = i[7:0];
      #1;
      if (y !== exp[i]) begin
        errors = errors + 1;
        if (errors <= 3) $display("MISMATCH x=%02x y=%02x expected %02x", x, y, exp[i]);
      end
    end
    $display("RESULT inputs=256 errors=%0d", errors);
    $finish;
  end
endmodule
"""


def simulate(design, work, tag):
    d = os.path.join(work, tag)
    os.makedirs(d)
    with open(os.path.join(d, "tb.sv"), "w") as fh:
        fh.write(TB)
    with open(os.path.join(d, "exp.hex"), "w") as fh:
        fh.write("\n".join(f"{v:02x}" for v in TABLE) + "\n")
    proc = subprocess.run(["verilator", "--binary", "--timing", "-j", "2", "-Wno-fatal", "-Wno-WIDTH",
                           "--top-module", "tb", "tb.sv", os.path.abspath(design), "-Mdir", "obj",
                           "-o", "vtb"], cwd=d, capture_output=True, text=True)
    if proc.returncode != 0:
        return None, (proc.stderr or proc.stdout)[-600:]
    out = subprocess.run(["obj/vtb"], cwd=d, capture_output=True, text=True).stdout
    m = re.search(r"RESULT inputs=256 errors=(\d+)", out)
    return (int(m.group(1)) if m else None), out[-300:]


def sim(good, bad):
    if shutil.which("verilator") is None:
        raise RuntimeError("verilator not found")
    msgs = []
    with tempfile.TemporaryDirectory(prefix="svgolf-aes-sim-") as work:
        for kind, designs in (("good", good), ("bad", bad)):
            for k, dsg in enumerate(designs):
                errs, tail = simulate(dsg, work, f"{kind}{k}")
                assert errs is not None, f"{dsg}: no result: {tail}"
                if kind == "good":
                    assert errs == 0, f"{dsg}: {errs} of 256 inputs differ from the S-box: {tail}"
                else:
                    assert errs > 0, f"{dsg}: a negative design that matches the S-box on all 256 inputs"
                msgs.append(f"{os.path.basename(dsg)} {'= S-box on all 256 inputs' if kind == 'good' else f'differs on {errs} of 256'}")
    return "; ".join(msgs) if msgs else "no design given"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--good", nargs="*", default=[])
    ap.add_argument("--bad", nargs="*", default=[])
    ap.add_argument("--only", default="table,anchors,aes,bp,vectors,sim")
    args = ap.parse_args()
    steps = args.only.split(",")
    failed = 0
    for name in steps:
        try:
            fn = {"table": table, "anchors": anchors, "aes": aes, "bp": bp,
                  "vectors": vectors, "sim": lambda: sim(args.good, args.bad)}[name]
            print(f"[ok] {name}: {fn()}", flush=True)
        except (AssertionError, RuntimeError, OSError) as e:
            failed += 1
            print(f"[FAIL] {name}: {type(e).__name__}: {e}", flush=True)
    print("validate:", "PASS" if not failed else f"FAIL ({failed} step(s))")
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())

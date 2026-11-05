"""Independent cross-checks of oracle.py (python3.12 validate.py [path/to/SLP_AES_113.txt]; the OpenSSL check needs `cryptography`).
 0. The whole 256-entry table equals FIPS 197 (2023 edition) Table 4, parsed from the NIST PDF into vectors.json.
 1. FIPS 197 anchors: S(00)=63, S(01)=7c, S(53)=ed (Section 5.1.1 example), S(10)=ca, S(ff)=16, first row of Table 4.
 2. The 113-gate Boyar-Peralta straight-line program (an independently derived circuit) equals the
    table on all 256 inputs (needs the netlist file; fetched from the URL in reference/sbox_bp.sv).
 3. AES-128 encryption through a textbook AES using this S-box: the FIPS 197 (2001) Appendix C.1 example
    (key 000102..0f, plaintext 00112233..ff -> 69c4e0d86a7b0430d8cdb78070b4c55a) and 300 random blocks against
    OpenSSL's AES (`cryptography` package): a wrong table entry would be hit by random blocks.
 4. GF(2^8) multiplication anchors of Section 4.2: {57}*{13} = {fe} (2023 text, eq. 4.7), {57}*{83} = {c1} (2001 text).
"""
import json, re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oracle import sbox, TABLE, gmul

def table4():
    here = os.path.dirname(os.path.abspath(__file__))
    t = json.load(open(os.path.join(here, "vectors.json")))["table"]["values"]
    assert t == TABLE and len(t) == 256
    return 256

def anchors():
    assert TABLE[0x00] == 0x63 and TABLE[0x01] == 0x7C and TABLE[0x53] == 0xED
    assert TABLE[0x10] == 0xCA and TABLE[0xFF] == 0x16
    assert TABLE[:16] == [0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76]
    assert gmul(0x57, 0x83) == 0xC1 and gmul(0x57, 0x13) == 0xFE
    assert len(set(TABLE)) == 256            # a permutation
    return 5

def bp(path):
    prog = []
    for l in open(path).read().split("\n"):
        m = re.match(r"(\w+) = (\w+) ([+x#]) (\w+)", l)
        if m: prog.append(m.groups())
    def run(x):
        env = {f"U{i}": (x >> (7 - i)) & 1 for i in range(8)}
        for d, a, o, b in prog:
            env[d] = env[a] ^ env[b] if o == "+" else env[a] & env[b] if o == "x" else 1 ^ env[a] ^ env[b]
        return sum(env[f"S{i}"] << (7 - i) for i in range(8))
    assert len(prog) == 113
    bad = [x for x in range(256) if run(x) != TABLE[x]]
    assert not bad, bad
    return 256

def aes128_encrypt(key, pt):
    def xt(a): return ((a << 1) ^ 0x11B) & 0xFF if a & 0x80 else a << 1
    def mc(c):
        a = c; return [xt(a[0]) ^ (xt(a[1]) ^ a[1]) ^ a[2] ^ a[3], a[0] ^ xt(a[1]) ^ (xt(a[2]) ^ a[2]) ^ a[3],
                       a[0] ^ a[1] ^ xt(a[2]) ^ (xt(a[3]) ^ a[3]), (xt(a[0]) ^ a[0]) ^ a[1] ^ a[2] ^ xt(a[3])]
    w = [list(key[4*i:4*i+4]) for i in range(4)]; rcon = 1
    for i in range(4, 44):
        t = list(w[i-1])
        if i % 4 == 0:
            t = [TABLE[t[1]] ^ rcon, TABLE[t[2]], TABLE[t[3]], TABLE[t[0]]]; rcon = xt(rcon)
        w.append([w[i-4][j] ^ t[j] for j in range(4)])
    rk = [sum(w[4*r:4*r+4], []) for r in range(11)]
    s = [pt[i] ^ rk[0][i] for i in range(16)]
    for r in range(1, 11):
        s = [TABLE[b] for b in s]
        s = [s[(i + 4 * (i % 4)) % 16] for i in range(16)]           # ShiftRows (column-major state)
        if r < 10:
            s = sum([mc(s[4*c:4*c+4]) for c in range(4)], [])
        s = [s[i] ^ rk[r][i] for i in range(16)]
    return bytes(s)

def aes128():
    ct = aes128_encrypt(bytes(range(16)), bytes.fromhex("00112233445566778899aabbccddeeff"))
    assert ct.hex() == "69c4e0d86a7b0430d8cdb78070b4c55a", ct.hex()
    return 1

def openssl_aes():
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    import random
    rnd = random.Random(9); n = 0
    for _ in range(300):
        key = bytes(rnd.getrandbits(8) for _ in range(16)); pt = bytes(rnd.getrandbits(8) for _ in range(16))
        enc = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
        assert enc.update(pt) + enc.finalize() == aes128_encrypt(key, pt); n += 1
    return n

if __name__ == "__main__":
    print("FIPS 197 Table 4 (256)  :", table4())
    print("anchors              :", anchors())
    p = sys.argv[1] if len(sys.argv) > 1 else None
    if p: print("BP 113-gate SLP vs table:", bp(p), "inputs")
    print("AES-128 C.1 example   :", aes128())
    try: print("AES-128 vs OpenSSL     :", openssl_aes(), "blocks")
    except ImportError: print("AES-128 vs OpenSSL     : skipped (no `cryptography`)")
    print("ALL OK")

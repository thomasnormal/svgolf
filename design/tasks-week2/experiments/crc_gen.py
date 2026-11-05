import sys, zlib, random, itertools
POLY = 0xEDB88320  # reflected CRC-32 (IEEE 802.3), RevEng catalogue CRC-32/ISO-HDLC, check("123456789") = 0xCBF43926
def step_bit(c, bit):          # one bit-serial step, reflected, data bit LSB-first
    fb = (c ^ bit) & 1
    c >>= 1
    return c ^ (POLY if fb else 0)
def update(c, data, nbits):    # raw register update (no init/xorout), data LSB first
    for i in range(nbits): c = step_bit(c, (data >> i) & 1)
    return c
# independent check: zlib continues from a previous crc: crc32(data, prev) = raw_update(prev ^ 0xFFFFFFFF, data) ^ 0xFFFFFFFF
def zlib_update(c, data, nbytes):
    prev = c ^ 0xFFFFFFFF
    return zlib.crc32(data.to_bytes(nbytes, "little"), prev) ^ 0xFFFFFFFF
rnd = random.Random(3)
for _ in range(200):
    c = rnd.getrandbits(32); d = rnd.getrandbits(32)
    assert update(c, d, 32) == zlib_update(c, d, 4)
assert update(update(0xFFFFFFFF, int.from_bytes(b"123456789","little") & 0, 0), 0, 0) == 0xFFFFFFFF
# check value
c = 0xFFFFFFFF
for ch in b"123456789":
    c = update(c, ch, 8)
assert c ^ 0xFFFFFFFF == 0xCBF43926
# linear map: out bits as XOR of (crc bits, data bits): columns by unit vectors
def matrix(nbits):
    rows = [0] * 32   # bitmask over 32 crc bits + nbits data bits
    for j in range(32):
        out = update(1 << j, 0, nbits)
        for i in range(32):
            if (out >> i) & 1: rows[i] |= 1 << j
    for j in range(nbits):
        out = update(0, 1 << j, nbits)
        for i in range(32):
            if (out >> i) & 1: rows[i] |= 1 << (32 + j)
    return rows
def names(nbits): return [f"c[{j}]" for j in range(32)] + [f"d[{j}]" for j in range(nbits)]
def sv_plain(nbits, rows):
    nm = names(nbits); L = [f"module crcm(input logic [31:0] c, input logic [{nbits-1}:0] d, output logic [31:0] y);"]
    for i, r in enumerate(rows):
        ts = [nm[j] for j in range(32 + nbits) if (r >> j) & 1]
        L.append(f"  assign y[{i}] = " + (" ^ ".join(ts) if ts else "1'b0") + ";")
    return "\n".join(L) + "\nendmodule\n", sum(bin(r).count("1") - 1 for r in rows)
def sv_paar(nbits, rows):
    # Paar greedy CSE on the XOR matrix
    nm = names(nbits); n0 = len(nm)
    rs = [set(j for j in range(n0) if (r >> j) & 1) for r in rows]
    defs = []  # (newidx, a, b)
    nxt = n0
    while True:
        cnt = {}
        for r in rs:
            l = sorted(r)
            for a, b in itertools.combinations(l, 2): cnt[(a, b)] = cnt.get((a, b), 0) + 1
        if not cnt: break
        (a, b), k = max(cnt.items(), key=lambda kv: (kv[1], -kv[0][0], -kv[0][1]))
        if k < 2: break
        defs.append((nxt, a, b))
        for r in rs:
            if a in r and b in r: r.discard(a); r.discard(b); r.add(nxt)
        nxt += 1
    L = [f"module crcm(input logic [31:0] c, input logic [{nbits-1}:0] d, output logic [31:0] y);"]
    def nme(j): return nm[j] if j < n0 else f"t{j}"
    if defs: L.append("  logic " + ", ".join(f"t{k}" for k, _, _ in defs) + ";")
    for k, a, b in defs: L.append(f"  assign t{k} = {nme(a)} ^ {nme(b)};")
    xc = len(defs)
    for i, r in enumerate(rs):
        ts = [nme(j) for j in sorted(r)]
        xc += max(len(ts) - 1, 0)
        L.append(f"  assign y[{i}] = " + (" ^ ".join(ts) if ts else "1'b0") + ";")
    return "\n".join(L) + "\nendmodule\n", xc
def sv_serial(nbits):
    L = [f"module crcm(input logic [31:0] c, input logic [{nbits-1}:0] d, output logic [31:0] y);",
         f"  logic [{nbits}:0][31:0] s;", "  assign s[0] = c;"]
    for i in range(nbits):
        bits = []
        for k in range(32):
            sh = f"s[{i}][{k+1}]" if k < 31 else "1'b0"
            if (POLY >> k) & 1: bits.append(f"{sh} ^ (s[{i}][0] ^ d[{i}])")
            else: bits.append(sh)
        L.append(f"  assign s[{i+1}] = {{" + ", ".join(reversed(bits)) + "};")
    L.append(f"  assign y = s[{nbits}];")
    return "\n".join(L) + "\nendmodule\n"
if __name__ == "__main__":
    nbits = int(sys.argv[1]); rows = matrix(nbits)
    sv, x = sv_plain(nbits, rows); open(f"crc_plain_{nbits}.sv", "w").write(sv); print("plain XOR2 count", x)
    sv, x = sv_paar(nbits, rows); open(f"crc_paar_{nbits}.sv", "w").write(sv); print("paar  XOR2 count", x)
    open(f"crc_serial_{nbits}.sv", "w").write(sv_serial(nbits))

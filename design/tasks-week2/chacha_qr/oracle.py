"""Advisory oracle for the draft task `chacha_qr` (NOT part of the trusted statement): RFC 8439 Section 2.1."""
M = 0xFFFFFFFF
def rotl(x, n): return ((x << n) | (x >> (32 - n))) & M
def qr(a, b, c, d):
    a = (a + b) & M; d ^= a; d = rotl(d, 16)
    c = (c + d) & M; b ^= c; b = rotl(b, 12)
    a = (a + b) & M; d ^= a; d = rotl(d, 8)
    c = (c + d) & M; b ^= c; b = rotl(b, 7)
    return a, b, c, d
def oracle(params, inputs):
    ra, rb, rc, rd = qr(inputs["a"], inputs["b"], inputs["c"], inputs["d"])
    return {"ra": ra, "rb": rb, "rc": rc, "rd": rd}

"""Advisory oracle for the draft task `aes_sbox` (NOT part of the trusted statement).

The AES S-box, FIPS 197 Section 5.1.1: multiplicative inverse in GF(2^8) (modulus x^8+x^4+x^3+x+1;
0 maps to 0), then the affine map b' = b ^ rotl(b,1) ^ rotl(b,2) ^ rotl(b,3) ^ rotl(b,4) ^ 0x63.
oracle(params, inputs) has the signature svGolf's `task.json` "oracle" key expects.
"""
def gmul(a, b):
    r = 0
    for _ in range(8):
        if b & 1: r ^= a
        a <<= 1
        if a & 0x100: a ^= 0x11B
        b >>= 1
    return r

def ginv(a):
    # a^254 (= a^-1 for a != 0, and 0 for a = 0)
    r = 1
    p = a
    for _ in range(7):
        p = gmul(p, p)          # a^2, a^4, ..., a^128
        r = gmul(r, p)
    return r

def rotl8(b, k): return ((b << k) | (b >> (8 - k))) & 0xFF

def sbox(x):
    b = ginv(x)
    return b ^ rotl8(b, 1) ^ rotl8(b, 2) ^ rotl8(b, 3) ^ rotl8(b, 4) ^ 0x63

TABLE = [sbox(x) for x in range(256)]

def oracle(params, inputs):
    return {"y": sbox(inputs["x"] & 0xFF)}

"""Advisory oracle for the draft task `keccak_round` (NOT part of the trusted statement).

One round of Keccak-p on a state of 25 lanes of W bits: iota(rc) o chi o pi o rho o theta,
FIPS 202 Algorithms 1-6 (Section 3.2), with the lane width W a free parameter (the standard
widths are W = 2^l, l = 0..6; the formulas are also defined for any other W >= 1, where the
rho rotation is by (t+1)(t+2)/2 mod W).

Two independent implementations live here and are cross-checked by validate.py:

  * round_bits  -- literal FIPS 202: the state is A[x][y][z] of single bits, every step is the
                   bit formula of the standard (no lanes, no big integers);
  * round_lanes -- the "Keccak reference" lane form on Python integers.

State packing (FIPS 202 Section 3.1.2, as in svGolf's draft Spec.lean): flat bit index
W*(5*y + x) + z holds bit z of lane (x, y); a state is a Python int below 2**(25*W).

oracle(params, inputs) has the signature svGolf's `task.json` "oracle" key expects:
params {"W": 16}, inputs {"a": <state int>, "rc": <int>} -> {"y": <state int>}.
"""

# rho offsets: r[0,0] = 0; (x,y) <- (y, 2x+3y) from (1,0), r = (t+1)(t+2)/2 at step t (unreduced).
def rho_offsets():
    r = [[0] * 5 for _ in range(5)]
    x, y = 1, 0
    for t in range(24):
        r[x][y] = (t + 1) * (t + 2) // 2
        x, y = y, (2 * x + 3 * y) % 5
    return r  # r[x][y]

RHO = rho_offsets()


def unpack_bits(W, s):
    """flat int -> A[x][y][z] (list of lists of lists of 0/1)."""
    A = [[[0] * W for _ in range(5)] for _ in range(5)]
    for x in range(5):
        for y in range(5):
            for z in range(W):
                A[x][y][z] = (s >> (W * (5 * y + x) + z)) & 1
    return A


def pack_bits(W, A):
    s = 0
    for x in range(5):
        for y in range(5):
            for z in range(W):
                s |= A[x][y][z] << (W * (5 * y + x) + z)
    return s


def round_bits(W, s, rc):
    """FIPS 202 on single bits."""
    A = unpack_bits(W, s)
    # theta
    C = [[A[x][0][z] ^ A[x][1][z] ^ A[x][2][z] ^ A[x][3][z] ^ A[x][4][z] for z in range(W)] for x in range(5)]
    D = [[C[(x - 1) % 5][z] ^ C[(x + 1) % 5][(z - 1) % W] for z in range(W)] for x in range(5)]
    A1 = [[[A[x][y][z] ^ D[x][z] for z in range(W)] for y in range(5)] for x in range(5)]
    # rho
    A2 = [[[A1[x][y][(z - RHO[x][y]) % W] for z in range(W)] for y in range(5)] for x in range(5)]
    # pi: A'[x,y,z] = A[(x + 3y) mod 5, x, z]
    A3 = [[[A2[(x + 3 * y) % 5][x][z] for z in range(W)] for y in range(5)] for x in range(5)]
    # chi
    A4 = [[[A3[x][y][z] ^ ((A3[(x + 1) % 5][y][z] ^ 1) & A3[(x + 2) % 5][y][z]) for z in range(W)]
            for y in range(5)] for x in range(5)]
    # iota: lane (0,0) ^= rc (rc taken mod 2^W)
    for z in range(W):
        A4[0][0][z] ^= (rc >> z) & 1
    return pack_bits(W, A4)


def rotl(W, v, n):
    n %= W
    return ((v << n) | (v >> (W - n))) & ((1 << W) - 1) if n else v


def round_lanes(W, s, rc):
    """Lane form (Keccak reference, Section 1.2) on Python integers."""
    m = (1 << W) - 1
    A = [[(s >> (W * (5 * y + x))) & m for y in range(5)] for x in range(5)]
    C = [A[x][0] ^ A[x][1] ^ A[x][2] ^ A[x][3] ^ A[x][4] for x in range(5)]
    D = [C[(x - 1) % 5] ^ rotl(W, C[(x + 1) % 5], 1) for x in range(5)]
    A = [[A[x][y] ^ D[x] for y in range(5)] for x in range(5)]
    B = [[0] * 5 for _ in range(5)]
    for x in range(5):
        for y in range(5):
            B[y][(2 * x + 3 * y) % 5] = rotl(W, A[x][y], RHO[x][y])
    A = [[B[x][y] ^ ((B[(x + 1) % 5][y] ^ m) & B[(x + 2) % 5][y]) for y in range(5)] for x in range(5)]
    A[0][0] ^= rc & m
    out = 0
    for x in range(5):
        for y in range(5):
            out |= A[x][y] << (W * (5 * y + x))
    return out


# Round constants for W = 64 (FIPS 202 Table / Keccak reference); lane width W uses rc mod 2^W.
RC64 = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]


def rc_lfsr(i, W):
    """RC[i] truncated to W bits from the LFSR rc(t) of FIPS 202 Algorithm 5 (independent of RC64)."""
    def rc_bit(t):
        if t % 255 == 0:
            return 1
        R = 1
        for _ in range(t % 255):
            R <<= 1
            if R & 0x100:
                R ^= 0x171  # x^8 + x^6 + x^5 + x^4 + 1
        return R & 1
    l = W.bit_length() - 1
    rc = 0
    for j in range(l + 1):
        rc |= rc_bit(j + 7 * i) << ((1 << j) - 1)
    return rc


def permutation(W, s):
    """Keccak-f[25W] for W = 2^l: 12 + 2l rounds."""
    l = W.bit_length() - 1
    for i in range(12 + 2 * l):
        s = round_lanes(W, s, RC64[i] & ((1 << W) - 1))
    return s


def oracle(params, inputs):
    W = params["W"]
    m = (1 << (25 * W)) - 1
    return {"y": round_lanes(W, inputs["a"] & m, inputs["rc"] & ((1 << W) - 1))}

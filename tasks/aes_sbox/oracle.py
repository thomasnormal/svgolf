"""Advisory oracle of task `aes_sbox`: y = SubBytes(x), the AES S-box of FIPS 197 Section 5.1.1
(README.md, task.json `oracle`).

NOT part of the trusted statement (`Spec.lean` is): a convenience that lets `check.py` tell a
contestant, before any proof, that their design computes something else. It is the same algebra
as `Spec.lean`, written separately in Python: the multiplicative inverse in
GF(2^8) = GF(2)[x]/(x^8+x^4+x^3+x+1) (0 is sent to 0), then the affine transformation
b' = b ^ rotl(b,1) ^ rotl(b,2) ^ rotl(b,3) ^ rotl(b,4) ^ 0x63.
tests/aes_sbox/validate/validate.py compares it with the table of FIPS 197 (Table 4 of the 2023
edition, parsed from the NIST PDF) on all 256 inputs, and tests/checker/test_advisories.py checks
that every task's oracle loads. `params` is the point ({} here: the task has no parameter),
`inputs` maps the input ports to ints; the result maps the output ports to ints already masked to
their widths.
"""


def gmul(a, b):
    """Multiplication in GF(2^8) (FIPS 197 Section 4.2), shift and add."""
    r = 0
    for _ in range(8):
        if b & 1:
            r ^= a
        a <<= 1
        if a & 0x100:
            a ^= 0x11B
        b >>= 1
    return r


def ginv(a):
    """a^254 = a^2 * a^4 * ... * a^128: the inverse for a != 0 (the group has order 255), 0 for 0."""
    r, p = 1, a
    for _ in range(7):
        p = gmul(p, p)
        r = gmul(r, p)
    return r


def rotl8(b, k):
    return ((b << k) | (b >> (8 - k))) & 0xFF


def sbox(x):
    b = ginv(x)
    return b ^ rotl8(b, 1) ^ rotl8(b, 2) ^ rotl8(b, 3) ^ rotl8(b, 4) ^ 0x63


def oracle(params, inputs):
    return {"y": sbox(inputs["x"] & 0xFF)}

"""Advisory oracle of task `clmul`: the carry-less product, p = a (x) b on 2N-1 bits
(README.md, task.json `oracle`).

NOT part of the trusted statement (`Spec.lean` is): a convenience that lets `check.py` tell a contestant,
before any proof, that their design computes something else. `params` is the point the checker evaluates
at ({"N": 16}), `inputs` maps the input ports to ints; the result maps the output ports to ints already
masked to their widths.

Bit i of a vector is the coefficient of x^i; the product of two polynomials of degree below N is
sum over i, j of a_i b_j x^(i+j) over GF(2), i.e. shift-and-XOR: XOR of (a << i) over the set bits i of b.
"""


def oracle(params, inputs):
    n = params["N"]
    a, b = inputs["a"], inputs["b"]
    p = 0
    for i in range(n):
        if (b >> i) & 1:
            p ^= a << i
    return {"p": p & ((1 << (2 * n - 1)) - 1)}

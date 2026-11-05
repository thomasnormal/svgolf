"""Advisory oracle of task `mul`: p = a * b on 2N bits (README.md, task.json `oracle`).

NOT part of the trusted statement (`Spec.lean` is): a convenience that lets
`check.py` tell a contestant, before any proof, that their design computes
something else. `params` is the point the checker evaluates at ({"N": 16}),
`inputs` maps the input ports to ints; the result maps the output ports to
ints already masked to their widths.
"""


def oracle(params, inputs):
    n = params["N"]
    return {"p": (inputs["a"] * inputs["b"]) % (1 << (2 * n))}

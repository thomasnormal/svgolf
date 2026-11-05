"""Advisory oracle of task `add`: {cout, s} = a + b + cin (README.md, task.json `oracle`).

NOT part of the trusted statement (`Spec.lean` is): a convenience that lets
`check.py` tell a contestant, before any proof, that their design computes
something else. `params` is the point the checker evaluates at ({"N": 16}),
`inputs` maps the input ports to ints; the result maps the output ports to
ints already masked to their widths.
"""


def oracle(params, inputs):
    n = params["N"]
    t = inputs["a"] + inputs["b"] + inputs["cin"]
    return {"s": t % (1 << n), "cout": (t >> n) & 1}

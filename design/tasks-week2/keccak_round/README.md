# keccak_round (draft, bonus deliverable of the week-2 task study)

One round of Keccak-p on 25 lanes of W bits, for every W >= 1. See `../catalogue-comb.md` (A4) for the card and the measured
"flat golf" finding.

| file | what |
|---|---|
| `Spec.lean` | DRAFT trusted statement (generated from `Spec.template.lean` by `make_spec.py`); compiles against `SvGolf.Task` |
| `SpecFacts.lean` | untrusted facts a proof wants: `getLsbD_ofBits`, `unpack_pack`, `pack_unpack` |
| `SpecVectors.lean` | the heavy golden vectors (W = 16, 32, 64, SHA3-256("") round 0) by `decide +kernel` (about 2 minutes) |
| `oracle.py`, `validate.py` | two Python implementations and every cross-check (XKCP, hashlib, LFSR constants) |
| `vectors.json`, `make_vectors.py` | 23 golden rows `(W, a, rc, y, source)` |
| `reference/*.sv`, `gen_ref.py`, `sim_check.py` | textbook reference design (generated), simulated with iverilog against the oracle |
| `xkcp/` | the Keccak team's intermediate-value files, unmodified (`SOURCE.txt`; their terms, public domain under CC0, in `LICENSE`) |

Module names: `SpecFacts.lean` and `SpecVectors.lean` say `import Spec`. In the task tree they become `import tasks.keccak_round.Spec`;
the study compiled them as scratch copies with the module renamed `KeccakSpec`, because a module called `Spec` collides with the `spec`
library on a case-insensitive filesystem.

Reproduce: `python3 validate.py` (needs nothing but the standard library), `python3 sim_check.py reference/keccak_round.sv` (needs iverilog).

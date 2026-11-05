# `aes_sbox`: designs that must be rejected

Each design here tries one way to look like the S-box without meeting the statement. `tests/run.py` runs
`check.py` on them with the task's reference proof `tasks/aes_sbox/reference/sbox_bp.lean`: that proof is about
the Boyar-Peralta netlist, so for a different design it fails to compile at the `solution` stage (a design
outside the tactic fragment fails in its first lines, a wrong netlist in the equation of the gate that
differs; the two netlist negatives run the whole 100 s before they fail). There is no `Refute.lean` for this
task yet: the evidence that each design is wrong is the exhaustive Verilator simulation of
`tests/aes_sbox/validate/validate.py` (the four functional negatives must differ from the S-box somewhere,
and the counts below are measured there).

| design | what it tries | how it fails | checker stage |
|---|---|---|---|
| `no_constant.sv` | the affine constant `0x63` forgotten: the Boyar-Peralta circuit with its four XNORs written as XORs | computes `S(x) ^ 0x63`; wrong on all 256 inputs | `solution` |
| `one_entry.sv` | a 256-entry table whose entry for `0x53` is `0xec`, not `0xed` | right on 255 of 256 inputs; the statement quantifies over all of them | `solution` |
| `reversed_bits.sv` | the bit-order mistake: the right circuit fed `x[i]` where it wants `x[7-i]` | wrong on 240 of 256 inputs | `solution` |
| `inverse_sbox.sv` | the inverse S-box (decryption), a table of the same shape and cost | wrong on 254 of 256 inputs (it agrees with S on exactly 2) | `solution` |
| `wrong_names.sv` | the right circuit on ports `a`, `s` | the interface conjunct pins the port names (the stimulus drives `x`) | `solution` |
| `undriven_bit.sv` | `y[0]` never assigned | x in ls-sv; the fourstate stage refuses the undriven net before any proof | `fourstate` |
| `x_default.sv` | a correct 256-entry table with an unreachable `default: y = 8'bxxxxxxxx` | correct on every input, but an x literal has no meaning shared by the proof and the score | `source` |

The first four are the functional negatives (`validate.py --bad`). `one_entry.sv` is the one that matters most
for a table-shaped task: nothing short of a check on all 256 inputs separates it from the S-box.

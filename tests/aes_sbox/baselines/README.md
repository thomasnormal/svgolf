# A proved design of task `aes_sbox` besides the references: an entry

Every design here comes with a kernel-checked proof of the task's statement, its `.lean` beside it (decided
2026-11-12: every design the site shows is proved). None uses a banned operator, so each is an ENTRY (decided
2026-11-12: par is one design per task, the simplest algorithm, `leaderboard/par.json`: here the table `sbox_table.sv`;
every other proved design, the reference `sbox_bp.sv` too, is an entry), recorded on the board under a handle of its
own like any player's, and shown on the site once that record exists. `tests/run.py`, step `baseline-proofs`, checks
each proof
through `check.py` (accepted, standard axioms only); its scores are in `tests/expected.json` and re-measured by
`tests/run.py`, which also checks that the banlist (no task-specific operator for this task) passes it, that the
4-state rules pass, and that the checker's post-synthesis check passes it: ls-sv and the scored netlist agree on
all 256 inputs, and the task's oracle agrees with both. `tasks/aes_sbox/README.md`, "Comparison points", has the
table with provenance.

* `sbox_bp_d16.sv` + `sbox_bp_d16.lean`: the depth-16 Boyar-Peralta circuit (J. Boyar and R. Peralta, "A small
  depth-16 circuit for the AES S-box", IFIP SEC 2012), translated gate for gate from the authors' netlist file
  `AESDEPTH16SIZE125` (125 gates: 34 AND, 87 XOR, 4 XNOR, depth 16; 216.322 GE, depth 18 in this flow), a second
  point of the Pareto front beside the 113-gate reference. A flat netlist over `& ^` with XNOR as `^ 1'b1`, proved
  on the 113-gate reference's route (PROVING.md, section 12); the proof is generated from the netlist by
  `tests/aes_sbox/validate/gen_d16_proof.py` (`--check`: `tests/run.py`, step `layout`).

It is simulated on ALL 256 inputs in Verilator by `tests/aes_sbox/validate/validate.py` (`tasks/aes_sbox/README.md`,
"Validation"). The 256-entry `case` table, what a naive golfer writes, is the proved reference `sbox_table`
(until 2026-11-12 it was also listed here under a second path, the same tokens).

Not built: a tower-field (Canright) S-box and the smaller or shallower circuits of the later literature
(recalled, not checked); a `T[x]` ROM written as a packed constant scores exactly like the `case` table
(786.894 GE, depth 11, measured), so it is not a separate design.

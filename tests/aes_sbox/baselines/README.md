# Baselines for task `aes_sbox` (NOT entries)

Designs that are scored but never accepted: none of them has a proof, so none is an svGolf entry. (The
task's own reference, `tasks/aes_sbox/reference/sbox_bp.sv` with its proof, is not a baseline.) Their
scores are in `tests/expected.json` and re-measured by `tests/run.py`, which also checks that the banlist
(empty for this task) passes them, that the 4-state rules pass, and that the checker's post-synthesis check
passes them: ls-sv and the scored netlist agree on all 256 inputs, and the task's oracle agrees with both.
`tasks/aes_sbox/README.md`, "Comparison points", has the table with provenance.

* `sbox_table.sv`: the S-box as a 256-entry `always_comb` `case` table, what a naive golfer writes
  (786.894 GE, depth 11, 612 gates after ABC). It loads in ls-sv with no unsupported node, so
  `check.py --unproved` reaches the end for it, and since WP-G S3a it is inside the `sv_comb` tactic
  fragment (a plain `case` with a `default` and single-assignment arms): `tasks/aes_sbox/reference/sbox_table.*`
  is the same design with its proof (`by sv_exhaustive`).
* `sbox_bp_d16.sv`: the depth-16 Boyar-Peralta circuit (J. Boyar and R. Peralta, "A small depth-16 circuit
  for the AES S-box", IFIP SEC 2012), translated gate for gate from the authors' netlist file
  `AESDEPTH16SIZE125` (125 gates: 34 AND, 87 XOR, 4 XNOR, depth 16; 216.322 GE, depth 18 in this flow).
  It is a flat netlist over `& ^` with XNOR as `^ 1'b1`, so it is inside the tactic fragment, but only the
  113-gate circuit is proved (when the proof lands); this one is a second point of the Pareto front.

Both are simulated on ALL 256 inputs in Verilator by `tests/aes_sbox/validate/validate.py`
(`tasks/aes_sbox/README.md`, "Validation").

Not built: a tower-field (Canright) S-box and the smaller or shallower circuits of the later literature
(recalled, not checked); a `T[x]` ROM written as a packed constant scores exactly like the `case` table
(786.894 GE, depth 11, measured), so it is not a separate baseline.

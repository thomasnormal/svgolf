Compute the AES S-box (FIPS 197, Section 5.1.1): eight bits in, eight bits out, `y = S(x)`. The statement
defines `S` the way the standard does, algebraically (the multiplicative inverse in GF(2^8), then an affine
map), so a lookup table and a gate network are judged against the same mathematics.

The task has one fixed size, bans no operator but the run-time `/ % **` every task bans, and its post-synthesis
check covers all 256 inputs. The
proved Boyar-Peralta 113-gate circuit has {{sbox_bp.area}} and a {{sbox_bp.time}} critical path on sky130
({{sbox_bp.ge}}, depth {{sbox_bp.depth}}), {{sbox_bp.score}}: par. The proved 256-entry table is almost four
times larger and nearly twice as fast, {{sbox_table.area}} at {{sbox_table.time}} ({{sbox_table.ge}}, depth
{{sbox_table.depth}}). The S-box is the most golfed Boolean function in cryptography, so the
published circuits are strong comparison points.

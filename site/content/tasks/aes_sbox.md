Compute the AES S-box (FIPS 197, Section 5.1.1): eight bits in, eight bits out, `y = S(x)`. The statement
defines `S` the way the standard does, algebraically (the multiplicative inverse in GF(2^8), then an affine
map), so a lookup table and a gate network are judged against the same mathematics.

The task has one fixed size, bans no operator but the run-time `/ % **` every task bans, and its post-synthesis
check covers all 256 inputs. Par is the
proved 256-entry lookup table: {{sbox_table.area}} and a {{sbox_table.time}} critical path on sky130
({{sbox_table.ge}}, depth {{sbox_table.depth}}), {{sbox_table.score}}. The S-box is the most golfed Boolean
function in cryptography, so the published gate circuits (Boyar and Peralta's of 113 gates among them) are strong
comparison points.

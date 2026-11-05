Compute the AES S-box (FIPS 197, Section 5.1.1): eight bits in, eight bits out, `y = S(x)`. The statement
defines `S` the way the standard does, algebraically (the multiplicative inverse in GF(2^8), then an affine
map), so a lookup table and a gate network are judged against the same mathematics.

The task has one fixed size, bans no operator, and its post-synthesis check covers all 256 inputs. The
proved Boyar-Peralta 113-gate circuit has 892.1 µm² and a 4.26 ns critical path on sky130 (200.986 GE,
depth 21); the proved 256-entry table is almost four times larger and nearly twice as fast, 3445.8 µm² at
2.29 ns (786.894 GE, depth 11). The S-box is the most golfed Boolean function in cryptography, so the
published circuits are strong comparison points.

# Carry-select adder, 6-bit blocks

A carry-select adder for every `N`: `Q = N / 6` blocks of six bits and a ripple tail of `R = N % 6` bits, both counts integer localparams. At the scoring width `N = 16` that is two blocks and a four-bit tail. It beats par on sky130.

## The idea

Each block computes its carries twice, as two ripple chains stored in row `j` of the 2-D arrays `c0` (block carry-in 0) and `c1` (block carry-in 1). A row of multiplexers, `cs[j][t]`, uses the block carry `cb[j]` to pick the real carry into each bit. The block carries ripple through one multiplexer per block: `cb[j+1] = cb[j] ? c1[j][6] : c0[j][6]`. The tail ripples from `cb[Q]`, and the sum bits are `p ^ carry`, written in two trailing loops. Row `Q` of each array is unused and tied to a literal, so that every declared bit is driven.

## Why it scores as it does

On sky130 it measures 474.2 µm² and 2479 ps, giving 1175.6 µm²·ns against par's 1202.2. That is about 3% more area than the ripple for about 5% less delay. The netlist is only three cells larger than the ripple's: 83 cells (49 NAND2, 28 XOR2, three OR2, and one each of MUX2, AND2 and XNOR2) against 80. Its critical path to `s[15]` is 30 cells long, against the ripple's 32. The gain does not carry over to the routed ASAP7 course, where it measures 7.19 µm² and 554 ps, or 3.98 µm²·ns, behind par's design at 3.92.

## The proof

The proof is 332 code lines and follows the tactic route. Its own rank function, `cselRank`, is defined by cases on the site ids of the nested loops, and `sv_structure` with `sv_rowmajor` closes the structure obligations. After `sv_equations`, one `sv_bridge` per equation family passes the equations to the arithmetic in `Nat`-index form, bridging 2-D cells through `rmN` or the file's own lemma `rmN_flat`.

The arithmetic is generic in the block size `K` and lives in a namespace that never mentions the design:

- `rip` is the ripple carry restarted at any position from any carry. `chain_eq` shows that a stored chain is one of these, and `rip_add` shows that restarting at the true carry changes nothing.
- `mux_rip` shows that a multiplexer between the two chains equals the chain started from the select value.
- `csel_carry` proves, by induction on the block index and then on the tail, that the selected carries are the ripple carries. `csel_view` then gives `CombLib.AddView`, and `add_spec` finishes.

## What did not work

Scoring sweeps chose the block size and where the sum assigns go. The task README records that putting the same sum assigns inside the block loop scored worse in both area and delay than giving them loops of their own.

Writeup by the maintainers, from the design and proof files.

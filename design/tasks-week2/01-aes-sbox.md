# 01. `aes_sbox`: the AES S-box (combinational, fixed size)

**Pitch.** Eight bits in, eight bits out, the most-golfed boolean function in cryptography. A `case` table
scores 787 GE; the published 113-gate Boyar-Peralta circuit scores 201 GE in our flow (3.9 times smaller,
twice as deep). The statement is one line of algebra and the proof is a 256-case check. Best
golf-per-proof-effort of anything on the list.

**Header** (fixed size, no parameter):

```systemverilog
module aes_sbox (input logic [7:0] x, output logic [7:0] y);
```

**Trusted statement.** Exactly the ports `x` (8, input) and `y` (8, output); no clocked process; every run
terminates; whenever a stimulus drives `x` with a known value, `y = sbox x` where `sbox` is FIPS 197
Section 5.1.1: multiplicative inverse in GF(2^8) = GF(2)[x]/(x^8+x^4+x^3+x+1) with 0 sent to 0, then
`b ^ rotl b 1 ^ rotl b 2 ^ rotl b 3 ^ rotl b 4 ^ 0x63`. It is `CombTask.StatementFixed`; **no change to the
trusted `CombTask`**.

**`Spec.lean`** (draft, compiles against `SvGolf.Task`; `aes_sbox/Spec.lean`, 130 lines with the table):

```lean
def xtime (a : BitVec 8) : BitVec 8 := (a <<< 1) ^^^ (if a.msb then 0x1b#8 else 0#8)
def gmulAux : Nat → BitVec 8 → BitVec 8 → BitVec 8 → BitVec 8
  | 0, _, _, acc => acc
  | n + 1, a, b, acc => gmulAux n (xtime a) (b >>> 1) (if b.getLsbD 0 then acc ^^^ a else acc)
def gmul (a b : BitVec 8) := gmulAux 8 a b 0
def ginv (a : BitVec 8) : BitVec 8 := /- a^254 = a^2 * a^4 * ... * a^128 by 7 squarings -/ ...
def affine (b : BitVec 8) := b ^^^ b.rotateLeft 1 ^^^ b.rotateLeft 2 ^^^ b.rotateLeft 3 ^^^ b.rotateLeft 4 ^^^ 0x63#8
def sbox (x : BitVec 8) := affine (ginv x)
def task : CombTask where
  inRange N := N = 0
  inputs _ := [("x", 8)]
  outputs _ := [("y", 8)]
  fn _ := fun (x, ()) => (sbox x, ())
abbrev Statement : LeanModels.Sv.Design2 → Prop := task.StatementFixed
```

The draft also proves, by `decide +kernel`: the FIPS 197 products `{57}*{83}={c1}`, `{57}*{13}={fe}`; `S(00)=63`, `S(53)=ed`, `S(ff)=16`; the
algebra equals the 256-entry table of FIPS 197 (Table 4 in the 2023 edition; kept only as a cross-check); the S-box is a permutation.

**Oracle and independent checks** (`aes_sbox/oracle.py`, `validate.py`, all green):
the same algebra in Python; the 113-gate Boyar-Peralta netlist (an independently derived circuit,
`cs.yale.edu/homes/peralta/CircuitStuff/SLP_AES_113.txt`) agrees with the table on all 256 inputs; a textbook
AES-128 built on the table reproduces the FIPS 197 (2001) Appendix C.1 ciphertext `69c4e0d86a7b0430d8cdb78070b4c55a` and
agrees with OpenSSL's AES on 300 random blocks; **the whole table equals Table 4 of the 2023 edition of FIPS 197, parsed from
the NIST PDF** (`aes_sbox/vectors.json` holds table, anchors and sources); anchors `S(00)=63 S(53)=ed S(ff)=16`.

**Banlist, scoring.** Ban `+ - * / % **` (nothing here needs them; keeps the rule uniform with `add`/`mul`).
Fixed point, area then depth. Baselines, measured with the pinned flow (`experiments/score_all.sh`):

| design | area GE | depth |
|---|---|---|
| 256-entry `case` table (`reference/sbox_table.sv`) | 786.894 | 11 |
| Boyar-Peralta 113-gate SLP (`reference/sbox_bp.sv`: 32 AND, 77 XOR, 4 XNOR) | 200.986 (ABC maps it to 123 gates) | 21 |

Known bars to cite (recalled from the literature, to be checked before they go on a board): Canright 2005 tower-field
S-box; Boyar-Peralta 2010/2012: 115, then 113 gates (32 AND) at depth 27, and a depth-16 circuit of 128 gates;
smaller or shallower circuits since (Reyhani-Masoleh et al. 2018, Maximov-Ekdahl 2019). Because ABC re-derives
the network, depth in our flow is not the published depth; the headroom the data show is 4 times in area.

**What it needs from ls-sv and the tactics.**
* `~` (or `~^`): BP's circuit has four XNORs. WP-G gives `~` this week; T2 day 2 gives `~^` (`ex-xnor`, rank 4).
  Without either, write XNOR as `x ^ y ^ 1'b1`, which is in the fragment today, so the first reference does not wait.
* The `case` baseline needs `always_comb` with constant `case` (WP-G); it is a baseline, not a reference.
* `sv_structure`/`sv_equations` on a fixed straight-line design with about 113 equations and no generate loop.
  Worth measuring early: the tactics were tuned on loops (a few sites, many instances), not on 113 distinct sites.

**Proof strategy.** Structure goals are trivial (no loops, no arrays; every net driven once; rank = gate depth).
The equations give each net as a Boolean function of earlier nets; the arithmetic is an identity in 8 Boolean
variables, 8 outputs, checked by `cases` on the 8 input bits (256 cases) or `decide +kernel` on a reflected
evaluator. The scalable piece, useful for every fixed-size XOR/AND netlist task (CRC, MixColumns, MDS matrices,
SECDED), is a **reflective straight-line-program checker**: `eval : SLP → (Fin n → Bool) → ...` with a lemma
that the `sv_equations` conjunction is `eval` of the netlist term; then `decide +kernel` closes it. Library
work for the lead (WP-R, 1 to 2 days); the first S-box proof can be done by `simp` plus `decide` without it.
No SAT-based and no native-code decision procedure is needed.

**Effort: S to M** (spec, oracle and reference done in this draft; proof 1 day after WP-G, plus the reflection
helper if the plain `simp` route is too slow).

**Risks.** (1) The spec: a table typo or a wrong affine direction. Defence: the spec is the algebra, the table is a
check, and four independent sources agree (above). (2) Small search space invites exhaustive-synthesis
cheating? No: area/depth are scored on the netlist and the function is total; there is nothing to hide. (3)
Tactic scalability on 113 sites (above). (4) The task is a sprint: the proof is mechanical and the interest is in
the circuit, so it ranks first on golf-per-effort but is not by itself an "ambitious" proof.

**Cheating and checker coverage.** Statement is total on 2^8 inputs. x/z tricks are closed by the source gate
and the `fourstate` stage; a design that reads an uninitialised function-local is refused by the `postsynth`
fail-closed rule; the table baseline is legal and simply loses. The `postsynth` stage can be made exhaustive here
(`task.json` `postsynth.corners` = all 256 values of `x`, a few ms per vector), so the "sampling" limit of the
checker does not apply: a rare-input disagreement between ls-sv and Yosys cannot hide.

**Appeal: 5/5.** Famous benchmark, decades of published bars, a 4x gradient from naive to published, a second
axis (depth) with a real Pareto front, trivial to state and verify. The ladder continues: inverse S-box, combined
S-box and inverse, then `aes_round` (16 S-boxes, ShiftRows, MixColumns, AddRoundKey; fixed 128 bits; vector
FIPS 197 (2001) Appendix B, or OpenSSL's AES), where the shared linear layer is the SLP problem of `catalogue-comb.md` A5.

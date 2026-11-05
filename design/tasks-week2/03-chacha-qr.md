# 03. `chacha_qr`: the ChaCha quarter round (combinational, fixed 32-bit words)

**Pitch.** Four 32-bit additions, four XORs, four rotations: the smallest honest add-rotate-xor primitive and the
first task where adders appear *in context* (the road to an ALU). With `+` banned, the player builds the four adders
from gates, so every trick from `add` (ripple, lookahead, carry-select) now acts on a chain of dependent adders
whose rotations decouple bit positions; the area/depth front is wide and not obvious.

**Header** (fixed size; `do` is an SV keyword, hence `r*` for results):

```systemverilog
module chacha_qr (input logic [31:0] a, b, c, d, output logic [31:0] ra, rb, rc, rd);
```

**Trusted statement.** Exactly these ports; no clocked process; every run terminates; whenever `a b c d` are
driven with known values, `(ra, rb, rc, rd) = qr a b c d`, RFC 8439 Section 2.1 (`a += b; d ^= a; d <<<= 16;
c += d; b ^= c; b <<<= 12; a += b; d ^= a; d <<<= 8; c += d; b ^= c; b <<<= 7`, additions modulo `2^32`).
`CombTask.StatementFixed`; **no change to the trusted `CombTask`.**

**`Spec.lean`** (draft, compiles: `chacha_qr/Spec.lean`):

```lean
def qr (a b c d : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a := a + b;  let d := (d ^^^ a).rotateLeft 16
  let c := c + d;  let b := (b ^^^ c).rotateLeft 12
  let a := a + b;  let d := (d ^^^ a).rotateLeft 8
  let c := c + d;  let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)
def task : CombTask where
  inRange N := N = 0
  inputs _ := [("a", 32), ("b", 32), ("c", 32), ("d", 32)]
  outputs _ := [("ra", 32), ("rb", 32), ("rc", 32), ("rd", 32)]
  fn _ := fun (a, b, c, d, ()) => let r := qr a b c d; (r.1, r.2.1, r.2.2.1, r.2.2.2, ())
abbrev Statement : LeanModels.Sv.Design2 → Prop := task.StatementFixed
```

Draft examples (`decide`): the two quarter-round vectors of RFC 8439, Section 2.1.1
(`11111111 01020304 9b8d6f43 01234567 -> ea2a92f4 cb1cf8ce 4581472e 5881c4bb`) and Section 2.2.1
(`516461b1 2a5f714c 53372767 3d631689 -> bdb886dc cfacafd2 e46bea80 ccc07c79`). Both reproduced by the Python
oracle (written independently of the Lean), so the published vectors cross-check both implementations.

**Banlist, scoring.** Ban `+ - * / % **` (the additions are the task; Yosys merges `+` chains). Scoring point
fixed. Measured with the pinned flow (`experiments/chacha_qr_gen.py`; both versions simulated against the oracle
on 61 vectors including the RFC one):

| design | area GE | depth |
|---|---|---|
| four 32-bit ripple adders from gates (full adder: `a^b^c`, `(a&b)|(c&(a^b))`) | 1184.607 | 192 |
| Yosys's own `+` (banlist lifted) | 1212.254 | 192 |

Ripple-from-gates is already smaller than Yosys's adder, as in `add` (112.0 vs 117.994 GE at N = 16). The depth
192 (about 6 adder lengths; the chained ripples overlap thanks to the rotations) is the lever: `add`'s own
numbers (ripple 112 GE depth 33, Sklansky 127.7 depth 28, Kogge-Stone 149.7 depth 24) say what each adder
architecture buys, and which adders in the chain to speed up is a genuine scheduling problem.

**What it needs.** Nothing beyond today's fragment: four one-level generate loops of ripple rows (the `add_n`
site shapes, `cin = 1'b0`), vector XORs, rotations as concatenations of constant part-selects. No `~`, no
`always_comb`, no word-level operators. (With WP-B2 a *spec* may use `+` natively; here the spec already does,
on `BitVec`.)

**Proof strategy.** `sv_structure` (rank: the four adders in order, carry `i` before bit `i+1`), `sv_equations`; then
four applications of CombLib's `ripple_row` (`val s + 2^N * c N = val x + val y + c 0` with `c 0 = 0`, turned
into `s = x + y` by `bitvec_eq_ofNat_of_val`), XOR layers by `BitVec.eq_of_getLsbD_eq` + `getLsbD_xor`,
rotations by a lemma `rotateLeft_eq_concat` for the four constants (`getLsbD_rotateLeft`, case `i < r`). The
glue is the work (4 adder rows + 8 plain assigns, 40 to 60 `sv_equations` obligations), not any mathematics.

**Effort: M to L** (3 days: draft spec/oracle/vectors/reference are done; the proof is `add_n` times four plus glue).

**Risks.** (1) Direction of rotations and order of the four steps: cross-checked by the two RFC vectors and by 50 full
ChaCha20 blocks (the block function built on the oracle's quarter round equals OpenSSL's keystream through the
`cryptography` package: `chacha_qr/validate.py`). (2) None for gaming: total function, no hidden state. (3) Competition value depends on adder
choices already seen in `add`; the new content is the interaction between adders. Mitigation: it is the
natural stepping stone to `speck_round` (parametric N) and `sha256_round`.

**Variants worth queueing.** `speck_round`, parametric in the word size `N >= 9`, rotations (8, 3) as in Speck's
64/96/128-bit variants (published Speck128/128 vector, reproduced here: key `0f0e0d0c0b0a0908 0706050403020100`,
plaintext `6c61766975716520 7469206564616d20`, ciphertext `a65d985179783265 7860fedf5c570d18`, 32 rounds of the
round function). It adds the "for all N" requirement to the same glue. A sequential `chacha_block` core (one
quarter round or one double round per cycle) is the later sequential rung.

**Appeal: 4/5.** Real primitive, tiny spec, rich front, and the bridge from bitwise tasks to word-level
arithmetic; no published gate-count bar that I could verify, so the first records set the bar.

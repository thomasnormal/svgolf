# Catalogue A: combinational candidates (full cards)

Effort: S under 1 day, M 1 to 3 days, L more (spec + oracle + reference + proof, on a free Lean slot).
Register ids are `docs/sv-refusals.json` ids; WP-F/G/P/B2 are PLAN2's packages (F localparams, G `always_comb`/`~`/`?:`,
P proof API and speed, B2 word-level operators). "Needs" lists what is missing from the CURRENT fragment
(`fragment.md`); everything not listed is in it. Lean sketches marked *compiled* are in this directory and
typecheck against `SvGolf.Task` on 2026-10-30; the others are sketches. Numbers marked *measured* were
produced by the repo's pinned scorer (`experiments/score_all.sh`); numbers marked *recalled* come from memory of
the literature and must be checked before they appear on a board.

Ranking key: appeal (golf headroom, prestige, known bar) x feasibility this week x proof tractability, each 1 to 5.

| id | task | A | F | P | product |
|---|---|---|---|---|---|
| A1 | `aes_sbox` | 5 | 4 | 5 | 100 |
| A2 | `clmul` | 4 | 5 | 4 | 80 |
| A3 | `chacha_qr` | 4 | 4 | 3 | 48 |
| A4 | `keccak_round` | 3 | 4 | 4 | 48 |
| A5 | linear layers: `crc32_d32`, `aes_mixcol`, `secded_enc` | 4 | 3 | 4 | 48 |
| A6 | `sha256_round` | 4 | 3 | 3 | 36 |
| A7 | `sort8` (comparator network, B-bit keys) | 4 | 3 | 3 | 36 |
| A8 | `aes_round` | 5 | 2 | 3 | 30 |
| A9 | `speck_round` (parametric ARX) | 3 | 3 | 3 | 27 |
| A10 | `intdiv` (restoring divider, N bits) | 3 | 3 | 3 | 27 |
| A11 | `mersenne_mul` (mod 2^N - 1) | 4 | 2 | 3 | 24 |
| A12 | `secded` (encoder + corrector pair) | 4 | 2 | 3 | 24 |
| A13 | `popcount` / `lzc` | 2 | 3 | 4 | 24 |
| A14 | `fmul16` / parametric FP add, mul, fma | 4 | 1 | 1 | 16 |
| A15 | barrel shifter / rotator | 2 | 2 | 3 | 12 |

---

## A1. `aes_sbox`: see `01-aes-sbox.md`
*Fixed 8-bit S-box. Measured: table 786.9 GE (d 11), Boyar-Peralta 113-gate SLP 201.0 GE (d 21). Needs `~`/`~^` (WP-G, T2 day 2; `x ^ y ^ 1'b1` works today). Draft compiled.*

## A2. `clmul`: see `02-clmul.md`
*Parametric N, output 2N-1 bits. Measured: schoolbook 775.6 GE, Karatsuba base 4 622.3 GE at N = 16; 3226 vs 2124 at N = 32. In today's fragment. Draft compiled.*

## A3. `chacha_qr`: see `03-chacha-qr.md`
*Fixed 32-bit ARX. Measured 1184.6 GE d 192 (gate ripple adders) vs 1212.3 (Yosys `+`). In today's fragment. Draft compiled; oracle checked against OpenSSL ChaCha20.*

## A4. `keccak_round`: the lead's seed, the zk.golf family, and a surprise
- **Pitch.** One round (theta, rho, pi, chi, iota) of Keccak-p on 25 lanes of W bits, **for every lane width W >= 1**;
  W in {1, 2, 4, ..., 64} are Keccak-f[25], [50], ..., [1600] (zk.golf has three Keccak challenges); the proof is
  parametric where theirs is a fixed 1600.
- **Header.** `module keccak_round #(parameter int W = 16) (input logic [24:0][W-1:0] a, input logic [W-1:0] rc, output logic [24:0][W-1:0] y);` (flat widths `25*W`, `W`, `25*W`; a 2-D packed port has the same flat width).
- **Statement.** Ports exact; unclocked; terminating; whenever `a`, `rc` known, `y = iota rc (chi (pi (rho (theta A))))`, `A` the state `a` encodes (bit `W*(x+5y)+z` is `A[x][y][z]`), steps written bit by bit as FIPS 202 Algorithms 1 to 4 and 6. `rc` is an *input*: the LFSR of Algorithm 5 is not tested here (`keccak_core`, B9, does).
- **Spec.lean** (*compiled*, `keccak_round/Spec.lean`, 165 lines): `abbrev Bits := Nat → Nat → Nat → Bool`; `theta W A x y z := A x y z ^^ colPar A ((x+4)%5) z ^^ colPar A ((x+1)%5) ((z+W-1)%W)`; `rho W A x y z := A x y ((z + W - rhoOffset x y % W) % W)` with `rhoOffset` derived from Algorithm 2's walk `(x,y) <- (y, 2x+3y)` and cross-checked against the XKCP table; `pi A x y z := A ((x+3*y)%5) x z`; `chi`; `iota`; `task` with `inputs W := [("a", 25*W), ("rc", W)]`, `outputs W := [("y", 25*W)]`, `fn W (a, rc, ()) := pack W (round W rc (unpack W a))`. `SpecFacts.lean` (*compiled*) proves `unpack_pack`, `pack_unpack`, `getLsbD_ofBits`.
- **Oracle and independent validation** (`keccak_round/oracle.py`, `validate.py`; all green): two implementations (literal bit-level FIPS 202, and lanes on integers) agree on 200 random rounds at 10 widths; round constants regenerated from the LFSR of Algorithm 5 equal the table; the 24-round composition equals `hashlib.sha3_256`/`sha3_512` digests (7 messages); every round of both XKCP intermediate-value examples (`KeccakF-{200,400,800,1600}-IntermediateValues.txt`, widths 8/16/32/64, 168 rounds); the Lean spec reproduces XKCP rounds at W = 8, 16, 16 (round 19), 32 (round 21), 64 (rounds 2 and 23) and the first round inside SHA3-256("") by `decide +kernel` (`golden vectors`: `vectors.json`, 23 rows with sources). No published vector exists for W = 1, 2, 4: those rows are oracle-only (two agreeing implementations).
- **Banned.** Arithmetic `+ - * / % **` on run-time operands (none is needed); `%` in `localparam` is constant arithmetic and allowed. Scoring point W = 16 (Keccak-f[400], 2965 GE) or 32.
- **Needs.** 2-D packed arrays, doubled-vector rotation `cc[x][2*W-1-R : W-R]` with a localparam `R`, 25 literal lanes (no `i % 5` on a genvar). **WP-F2: a localparam atom `R = c % W` (`c` literal, `W` a parameter) with the facts `0 <= R < W`** (WP-F covers `%` by literals only; `rhoOffset x y % W` is the spec's own reduction, so the defining equation matches the spec). `~` (WP-G), or `a ^ c ^ (b & c)`, which is `a ^ (~b & c)` and needs only `& ^`.
- **Proof strategy.** Bit-level: each of the 25W output bits equals the spec formula at its coordinates. Index lemmas: lane permutation `j = y + 5*((2x+3y)%5)` (25 cases, `decide`), doubled-vector rotation `(W - R + z)` versus `(z + W - R) % W` (case `z < R`), `rhoOffset x y % W = R_i` (25 cases). Library: `SpecFacts`. No arithmetic beyond `Nat.mod` facts.
- **Reference.** `keccak_round/reference/keccak_round.sv` (generated by `gen_ref.py`, 155 lines): simulated by iverilog against the oracle on 383 vectors at W in {1,2,3,4,5,8,16,32,64}. Measured: W = 16 2965.2 GE, W = 64 11860.8 GE, depth 7. Per bit-column 185.3 GE = 76 XOR + 25 ANDNOT.
- **Effort: M** (2 days: spec, oracle, reference done; proof about 300 lines after WP-F2).
- **Risks.** **Golf headroom is close to zero**: the `a ^ (~b & c)` and `a ^ c ^ (b & c)` forms score identically (2965.2 GE), an explicit lane-complementing polarity assignment (the Keccak team's trick, which should save about 3.6% by turning 20 of 25 ANDNOTs into 1-GE NAND/NOR) also collapses to 2965.2 because ABC normalises polarity, and 76 XOR per column is the structural count of theta+chi. A leaderboard would be a tie at the textbook point, with only depth (7, perhaps 6 at an area price) to play for. The task is a strong *proof* showcase ("for every lane width") and the base of a real sequential core (B9), not a strong golf. Also: W not a power of two is a natural extension, not the standard (state it); `rc` as an input hides the LFSR.
- **Cheating.** None specific; total function. Spec bug places: `x`/`y` order of lanes, rho table, pi direction: all three covered by XKCP's per-step values.
- **Appeal: 3/5** for golf (measured), 5/5 for recognisability.

## A5. Linear layers: `crc32_d32`, `aes_mixcol`, `secded_enc`
- **Pitch.** Fixed-size GF(2)-linear maps (an XOR network and nothing else): CRC-32 over 32 data bits, AES MixColumns (32 to 32), a (72,64) Hsiao encoder. Golf = shortest linear program: ABC does not do XOR common-subexpression sharing, so there is a lot of room (CRC-32: 1394 GE as written per output, 494 GE with greedy Paar sharing, 2.8 times, *measured*; XOR2 count 872 to 247).
- **Header (CRC).** `module crc32_d32 (input logic [31:0] c, d, output logic [31:0] y);`
- **Statement.** `y = update c d`, 32 bit-serial steps of reflected CRC-32 (poly `0xEDB88320`).
- **Spec sketch.** `def stepBit (c : BitVec 32) (b : Bool) := (c >>> 1) ^^^ (if c.getLsbD 0 ^^ b then 0xEDB88320#32 else 0#32)`; `def update c d := (List.range 32).foldl (fun c i => stepBit c (d.getLsbD i)) c`; `task` fixed-size, `fn _ (c, d, ()) := (update c d, ())`.
- **Oracle / independent.** `zlib.crc32` continuation identity (200 random cases) and the RevEng check `0xCBF43926` for "123456789" (verified, `experiments/crc_gen.py`). AES MixColumns: the textbook AES in `aes_sbox/validate.py` uses it and agrees with OpenSSL's AES on 300 random blocks and with the FIPS 197 (2001) Appendix C.1 ciphertext. Hsiao: the code's distance property is proved in Lean about the spec itself.
- **Banned / scoring.** Arithmetic ops; scoring is the fixed point.
- **Needs.** Nothing: flat `assign y[k] = ... ^ ... ;` lines (the reference is generated from the matrix). For the proof: a **linearity-transfer library** (WP-L, new).
- **Proof strategy.** `update` is linear in `(c, d)` (induction on the fold); an XOR-only netlist is linear (a meta-theorem on the `sv_equations` conjunction: every equation is an XOR of earlier nets and inputs); two linear maps agreeing on the 64 basis vectors agree everywhere; evaluate the 64 basis vectors by `decide +kernel`. For parametric-width variants (data width `D` as a parameter) the serial unrolled reference is in the fragment with an induction on the step, but a contestant's optimised XOR network is not parametric, which is why the tasks are fixed width.
- **Reference.** Generated flat XOR networks: `experiments/crc_gen.py` (plain, Paar). Measured: plain 1394 GE d 6, Paar 494 GE d 6.
- **Effort: M** (library 2 days, each task 1).
- **Risks.** Spec orientation (reflected vs normal, LSB-first): covered by zlib. SLP optimisation is a well-studied NP-hard problem, so the board will quickly reach the literature's heuristics (Paar, Boyar-Peralta, later work); the interest is then depth and the honest XOR count.
- **Appeal: 4/5.** Known bars (AES MixColumns: published XOR counts in the 90s, *recalled*; check before quoting).

## A6. `sha256_round`
- **Pitch.** One SHA-256 round (zk.golf's headline primitive): `Ch`, `Maj`, `Sigma0`, `Sigma1` and a five-operand sum for `T1`, a two-operand `T2`, two outputs that are sums.
- **Header.** `module sha256_round (input logic [31:0] a,b,c,d,e,f,g,h, k, w, output logic [31:0] a2,b2,c2,d2,e2,f2,g2,h2);` (fixed).
- **Statement.** FIPS 180-4 Section 6.2.2 step 3: `T1 = h + Sigma1(e) + Ch(e,f,g) + k + w`, `T2 = Sigma0(a) + Maj(a,b,c)`, `(a2,...,h2) = (T1+T2, a, b, c, d+T1, e, f, g)`.
- **Spec sketch.** `def round (s : Fin 8 → BitVec 32) (k w : BitVec 32)` with `Ch e f g := (e &&& f) ^^^ (~~~e &&& g)`, `Sigma1 e := e.rotateRight 6 ^^^ e.rotateRight 11 ^^^ e.rotateRight 25`; task as `chacha_qr` with ten inputs, eight outputs.
- **Oracle / independent.** Verified in the study: round 0 of SHA-256("abc") gives `a = 5d6aebcd`, `e = fa2a4622` (NIST example values), and the 64-round composition equals `hashlib.sha256("abc")`. Use `hashlib` for random blocks too (compose the oracle).
- **Banned / scoring.** `+ - * / % **` banned (adders from gates; carry-save trees are the golf); fixed point.
- **Needs.** Nothing beyond today's fragment (CSA rows are 3:2 compressors per bit; final adders ripple rows).
- **Proof strategy.** `csa_row` (new lemma: three bit vectors, `x + y + z = s + 2c` per bit by `fullAdder_arith`) and `ripple_row`; the five-operand and two-operand sums as trees of rows; `BitVec` glue and rotations as in `chacha_qr`. mul_tree and mul_wallace already proved carry-save trees, so the pattern exists.
- **Reference.** Not measured in the study. Expected structure: 5-to-2 compression of `T1` operands, one CPA for `T1`, one for `a2`, one for `e2`.
- **Effort: L** (4 to 5 days). **Risks:** large glue (about 200 `sv_equations`), proof time; none for gaming. **Appeal: 4.5/5** (zk.golf's flagship; known comparison points: circom, zk-email, xJsnark are R1CS numbers, not comparable in GE).

## A7. `sort8`: a comparator network on 8 B-bit keys
- **Pitch.** Sort eight unsigned B-bit words, for every B; the network is the classical golf object (19 comparators is optimal for 8 inputs, 60 for 16, *recalled*), the cell (compare-exchange of B-bit words) is the hardware golf.
- **Header.** `module sort8 #(parameter int B = 4) (input logic [B-1:0] x0,x1,x2,x3,x4,x5,x6,x7, output logic [B-1:0] y0,...,y7);`
- **Statement.** `(y0..y7)` is the ascending sort of `(x0..x7)` as unsigned numbers.
- **Spec sketch.** `fn B := fun (x0,...,x7,()) => let l := [x0,...,x7].toArray.insertionSort (fun a b => a.toNat ≤ b.toNat)`; then read `l[0]..l[7]`, with `l.size = 8` in the statement. (Use core's `insertionSort`: structural, kernel-friendly; `mergeSort` is well-founded and does not reduce.)
- **Oracle.** `sorted()`. Independent: the Lean spec and Python agree on all 8-tuples of 2-bit keys (65 536) and random for larger B.
- **Banned / scoring.** Ban relational operators `< <= > >=` and `+ - * / % **` (comparators from gates); scoring B = 4.
- **Needs.** `?:` or `~` (WP-G) for the mux, bitwise compare chain (in-fragment otherwise).
- **Proof strategy.** (1) the **0-1 principle** for a fixed list of comparator pairs (new library, about 200 lines: a comparator network commutes with monotone maps; if it sorts all 0-1 inputs it sorts everything); (2) the compare-exchange cell lemma by induction on the bit chain, for every B; (3) the 19 comparators checked on the 256 0-1 inputs by `decide +kernel`.
- **Reference.** Batcher's odd-even merge sort for 8 (19 comparators, depth 6) built from a generated list of 19 cells.
- **Effort: L.** **Risks:** the 0-1 principle library is the investment; the cell is where the golf is, and optimal networks leave little room beyond the cell. **Appeal: 4/5** (Dobbelaere-style public lists of best networks give a bar).

## A8. `aes_round`
- **Pitch.** One AES-128 encryption round (SubBytes, ShiftRows, MixColumns, AddRoundKey) on 128 bits: the S-box golf times 16 plus the MixColumns linear layer.
- **Header.** `module aes_round (input logic [127:0] s, k, output logic [127:0] y);` (fixed; column-major state as in FIPS 197).
- **Statement / Lean sketch** (not compiled): `def aesRound (s k : BitVec 128) : BitVec 128 := addKey (mixColumns (shiftRows (subBytes s))) k` with `subBytes` applying `AesSbox.sbox` (A1's definition) per byte, `shiftRows` the index map `(i + 4*(i%4)) % 16`, `mixColumns` by `xtime` as in FIPS 197 Section 5.1.3; `task` with `inputs := [("s",128),("k",128)]`, `outputs := [("y",128)]`, fixed.
- **Oracle / independent.** `aes_sbox/validate.py` already contains a textbook round-based AES-128 that agrees with OpenSSL's AES on 300 random blocks; take one round of it, and cross-check the 10-round composition against `cryptography`.
- **Banned / scoring.** `+ - * / % **`; fixed point. Baseline: 16 table S-boxes (about 16 x 787 GE) + naive MixColumns; target: 16 x ~201 GE + MixColumns SLP.
- **Needs.** A1's features; the 16 S-boxes as one generate body over byte index (affine `8*i + j` is NOT affine in two variables: write the S-box body with `x[8*i+j]` replaced by a 2-D packed port `[15:0][7:0]` so the index is `x[i][j]`). Instances (WP-I) would make the proof compositional.
- **Proof.** A1's S-box lemma per byte, MixColumns by the linearity-transfer library (A5), ShiftRows is wiring. Effort L (M with instances). Risks: size of the flat netlist for the tactics (1808 S-box sites). Appeal 5/5.

## A9. `speck_round`, parametric ARX
- **Pitch.** `chacha_qr` with the "for all N": one Speck round on N-bit words.
- **Header.** `module speck_round #(parameter int N = 32) (input logic [N-1:0] x, y, k, output logic [N-1:0] xo, yo);` (range `N >= 9`: rotations 8 and 3 are Speck's for every size except Speck32.)
- **Statement / Lean sketch** (not compiled): `def rnd (N) (x y k : BitVec N) := let x' := (x.rotateRight 8 + y) ^^^ k; (x', y.rotateLeft 3 ^^^ x')`; `task.inRange N := 9 ≤ N`, `inputs N := [("x",N),("y",N),("k",N)]`, `outputs N := [("xo",N),("yo",N)]`, `fn N (x,y,k,()) := let r := rnd N x y k; (r.1, r.2, ())`.
- **Oracle / independent.** Python round; published Speck128/128 vector (key `0f0e0d0c0b0a0908 0706050403020100`, plaintext `6c61766975716520 7469206564616d20`, ciphertext `a65d985179783265 7860fedf5c570d18`) reproduced by 32 rounds of this function with the Speck key schedule (done in the study).
- **Banned / scoring.** `+ - * / % **`; scoring N = 32 (Speck64) or 64.
- **Needs.** Nothing new: one ripple row, rotations as concatenations of part-selects with constant offsets `8 < N`, `3 < N`.
- **Proof.** `add_n` as a lemma (`ripple_row`), rotation lemma for `ror 8`, `rol 3` at every `N >= 9`. Effort M. Risks: none for gaming; competition value close to `chacha_qr`. Appeal 3/5.

## A10. `intdiv`, N-bit restoring divider
- **Pitch.** The combinational RISC-V `DIV`: quotient and remainder of two N-bit numbers, for every N; the cheapest on-ramp to the `fdiv16` recurrence machinery.
- **Header.** `module intdiv #(parameter int N = 8) (input logic [N-1:0] a, b, output logic [N-1:0] q, r);`
- **Statement / Lean sketch** (not compiled): `fn N (a, b, ()) := if b = 0#N then (BitVec.allOnes N, a, ()) else (a / b, a % b, ())` (the `b = 0` convention is RISC-V's and is written out, not left to a library default).
- **Oracle / independent.** Python `divmod`, and Lean `decide` on all pairs for N <= 4.
- **Banned / scoring.** Ban `/ %` always; ban `+ - * **` until WP-B2 (then allow `-` and `<` and watch the design collapse into "write the algorithm"); N = 8 or 16.
- **Needs.** N stages of subtract-and-select: ripple rows, muxes (`?:`/`~`, WP-G); in the fragment otherwise (AND-OR muxes).
- **Proof.** Stage invariant `a_hi * 2^(N-i) + ... = q_i * b + r_i, r_i < b` by induction on `i`; the recurrence arithmetic WP-H1 proves for `fdiv` is the same shape and reusable. Effort L. Risks: `b = 0` convention; no published gate-count bar. Appeal 3/5.

## A11. `mersenne_mul`: `a * b mod (2^N - 1)`
- **Pitch.** M31 (`N = 31`, the Circle-STARK field) and Mersenne multiplication for every N; zk-relevant like BabyBear and Goldilocks.
- **Header.** `module mersenne_mul #(parameter int N = 31) (input logic [N-1:0] a, b, output logic [N-1:0] p);`
- **Statement / Lean sketch** (not compiled): `fn N (a, b, ()) := (BitVec.ofNat N (a.toNat * b.toNat % (2^N - 1)), ())`, range `N >= 2`. The canonical result is below `2^N - 1`; an all-ones input means 0.
- **Oracle / independent.** Python big ints; M31 anchors from the field definition.
- **Banned / scoring.** `+ - * / % **`; scoring N = 16 (or 31).
- **Needs.** The full multiplier of `mul` inside the design; the hierarchy to reuse its proof (WP-I) or a flat copy; the fold (end-around add) and canonicalisation (compare with all ones).
- **Proof.** `mul_n` proof + `x mod (2^N-1)` folding lemma (`x = hi * 2^N + lo` so `x ≡ hi + lo`, one more fold, then `if = 2^N-1 then 0`). Effort L to XL. Risks: size; the all-ones representation of zero is the classic spec trap (stated). Appeal 4/5.

## A12. `secded`: encoder + single-error corrector, one design
- **Pitch.** Any (72,64) code that corrects one bit and detects two; the code is the player's free choice, so a lookup table cannot be copied.
- **Header.** `module secded (input logic [63:0] d, input logic [71:0] e, output logic [63:0] dc, output logic ok, derr);` (`e` is the injected error vector: encode, flip, decode in one block.)
- **Statement / Lean sketch** (not compiled, needs the new class): `structure RelTask where inRange; inputs; outputs; rel : (N : Nat) → Vals ins → Vals outs → Prop`; the statement says the outputs hold SOME known `w` with `rel v w`; `rel (d, e) (dc, ok, derr) := weight e ≤ 1 → dc = d ∧ ok ∧ ¬derr` and `weight e = 2 → derr`, and `True` otherwise (a don't-care region).
- **Oracle / independent.** Python brute force over all single and a random sample of double errors; the code properties (distinct odd-weight columns) proved in Lean about the player's H matrix.
- **Banned / scoring.** Arithmetic banned; fixed point. **Needs** `RelTask` (new trusted class), XOR trees and a syndrome decoder (`==` against constants or AND trees).
- **Proof.** The player proves the distance property of their own columns by `decide` and the syndrome logic against it. Effort L. Risks: the don't-care region is where a spec bug or an exploit hides (an `rel` that is too weak proves everything), so it needs the heaviest review; Appeal 4/5.

## A13. `popcount`, `lzc`
- **Pitch.** Count ones (or leading zeros) of a fixed-width word; building blocks for others rather than headline tasks.
- **Header.** `module popcount15 (input logic [14:0] x, output logic [3:0] n);` (widths `$clog2` are outside the fragment; `N = 2^K - 1` makes the output exactly `K` bits.)
- **Statement / Lean sketch** (not compiled): `def pop (x : BitVec n) := (List.range n).foldl (fun a i => a + if x.getLsbD i then 1 else 0) 0`; `fn _ (x, ()) := (BitVec.ofNat 4 (pop x), ())`.
- **Oracle / independent.** Python `bin(x).count('1')`; Lean `decide` on all 2^15 inputs.
- **Banned / scoring.** Ban `+ - * / % **` and `$countones`; fixed point.
- **Needs.** Full-adder rows (in fragment); `lzc` needs `casez` (T2 day 5).
- **Proof.** Exhaustive `decide +kernel` for N = 15; a parametric tree needs `csa_row` (A6). The standard full-adder tree uses `N - K` full adders (57 for 63 bits), so the golf is cell choice and depth only. Effort M. Appeal 2/5.

## A14. `fmul16` and parametric floating point
- **Pitch.** IEEE 754 binary16 multiplication under the same trusted rounding spec as `fdiv16`, then `(w, p)`-parametric add/mul/fma. A moonshot: the fdiv16 proof is not finished after days; fmul removes the recurrence but keeps rounding, packing, special cases.
- **Header.** `module fmul16 (input logic [15:0] a, b, output logic [15:0] q);`
- **Statement / Lean sketch** (not compiled): `fn _ (a, b, ()) := (SvGolf.IEEE754.fmul16 a b, ())` with `fmul16` to be written beside `fdiv16` in `spec/IEEE754.lean` (round to nearest even, canonical NaN, subnormals).
- **Oracle / independent.** The existing Verilator exhaustive method (all 2^32 pairs) against a softfloat reference (Berkeley SoftFloat / `numpy.float16` for the finite cases).
- **Banned / scoring.** `* ** / %` banned (so the 11x11 integer multiplier is built from gates: `mul`'s lemmas); fixed point.
- **Proof.** WP-H1's certificate bridge (`certF_bridge`) for every format; the integer product from `mul_n`. Effort L (fixed) to XL (parametric). Appeal 4/5.

## A15. Barrel shifter / rotator, prefix adder, comparator
- **Pitch.** Log-depth structures (the shifter's `K` mux layers, the prefix adder's `log N` levels); stand-alone tasks of low interest, better as better references for `add`/`mul`.
- **Header.** `module rotl_n #(parameter int K = 4) (input logic [2**K-1:0] x, input logic [K-1:0] s, output logic [2**K-1:0] y);` (widths `2^K` are not affine: outside the fragment).
- **Statement / Lean sketch** (not compiled): `fn K (x, s, ()) := (x.rotateLeft s.toNat, ())`.
- **Oracle / independent.** Python rotation. **Banned / scoring.** Arithmetic banned; `K = 4`.
- **Needs.** Stage shifts `2^k`, conditional generate and dynamic indices: none in the fragment; the Sklansky/Kogge-Stone adders need conditional generate (known, PROVING section 7). **Proof:** by induction on stages once `2^k` exists. Effort M each. Appeal 2/5.

# svGolf week 2: which ambitious tasks next (WP-T0 task study, 10/30)

Decided 2026-10-30: more ambitious tasks, with zk.golf as the model; the long-term aim is whole CPUs, so clocked and
asynchronous designs come into view. This directory is the study: zk.golf read from
outside, the current proof fragment, 27 candidates with statement sketches, measured baselines from the repo's own
scorer, drafts that compile, and a recommendation. Nothing outside `svgolf/design/tasks-week2/` was edited.

## The picks (page one)

| | pick | why, in one line |
|---|---|---|
| **Comb 1** | **`aes_sbox`** (fixed 8 bit) | 4x gap between a `case` table (786.9 GE) and the published 113-gate circuit (201.0 GE), decades of bars, statement is 8 lines of algebra, proof is a 256-case check. [01-aes-sbox.md](01-aes-sbox.md) |
| **Comb 2** | **`clmul`** (N-bit carry-less multiply, every N) | In today's fragment with no tactic work; Karatsuba makes it 20% smaller at N = 16 and 34% at N = 32 (measured); the first task whose best designs want recursion. [02-clmul.md](02-clmul.md) |
| **Comb 3** | **`chacha_qr`** (fixed 32 bit ARX) | First word-level task and the road to an ALU: four adders in context, RFC 8439 vectors, oracle checked against OpenSSL. In today's fragment. [03-chacha-qr.md](03-chacha-qr.md) |
| Seq 1 | **`pipe_mul`** (`PipeTask`: any comb task with delay D >= 1) | No reset, no protocol; new golf axis (where to cut: flops vs period); reuses every comb task. [04-pipe-fn.md](04-pipe-fn.md) |
| Seq 2 | **`crc32_step`** (`SeqTask` from reset) | Smallest stateful task with a published oracle (`zlib`), a real golf problem (XOR network 1394 vs 494 GE) and the reset/one-step-simulation machinery everything later needs. [05-crc-step.md](05-crc-step.md) |
| Moonshots | `keccak_core`, `fdivp_iter` (an iterative binary16 divider, `fdivp` at `(5, 11)`; the catalogues predate 2026-11-03 and name it after the former 16-bit task), `aes_round`, `mersenne_mul` (M31), `secded`, `acc_cpu`, `rv_core`, `async_fifo` | [catalogue-comb.md](catalogue-comb.md), [catalogue-seq.md](catalogue-seq.md) |

**Surprise worth knowing before choosing.** The lead's seed, the Keccak round for every lane width (draft complete:
spec, oracle, reference, vectors, `keccak_round/`), is a beautiful *proof* showcase and a poor *golf*: `a ^ (~b & c)`,
`a ^ c ^ (b & c)` and an explicit lane-complementing polarity assignment all score identically (2965.2 GE at W = 16,
11860.8 at W = 64, depth 7), because ABC canonicalises polarity and 76 XOR + 25 ANDNOT per bit column is the structure.
It also needs one small tactic extension (a localparam `c % W`, "WP-F2"). I rank it fourth among the combinational tasks and keep it ready; if a
zk.golf-recognisable name matters more than golf headroom, build it instead of `chacha_qr`.

**No change to the trusted `CombTask` is needed for the three combinational picks** (`aes_sbox`, `chacha_qr` are
`StatementFixed`; `clmul` is a plain one-parameter family). Sequential tasks need WP-S0's `SeqTask` (below).

## Ranked table

Effort: S under 1 day, M 1 to 3, L more (spec + oracle + reference + proof). Appeal 1 to 5 (golf headroom, prestige,
known bar). Score = appeal x feasibility this week x proof tractability (each 1 to 5; derivation in the catalogues).

| # | task | group | effort | appeal | main blocker | score |
|---|---|---|---|---|---|---|
| 1 | `aes_sbox` | comb, fixed | S to M | 5 | `~`/`~^` (WP-G / T2 day 2; `x ^ y ^ 1'b1` works now); tactics on a 113-site netlist | 100 |
| 2 | `clmul` | comb, param N | M | 4 | none; Karatsuba for every N needs recursion (WP-I, F3b) | 80 |
| 3 | `pipe_mul` (`PipeTask`) | seq | M to L | 4 | `SeqTask` groundwork: `ClockedBy`, flop price, clocked `postsynth` | 64 |
| 4 | counter / LFSR / shift register | seq (WP-S0 spike) | S to M | 2 (5 as foundation) | WP-S0 spike | 50 |
| 5 | `crc32_step` | seq | M | 3.5 | `SeqTask` + linear library | 49 |
| 6 | `chacha_qr` | comb, fixed | M to L | 4 | none; glue-heavy proof (4 adder rows) | 48 |
| 7 | `keccak_round` | comb, param W | M | 3 (measured flat) | WP-F2: localparam `c % W` | 48 |
| 8 | linear layers (`crc32_d32`, `aes_mixcol`, `secded_enc`) | comb, fixed | M | 4 | linearity-transfer library (new) | 48 |
| 9 | `sha256_round` | comb, fixed | L | 4.5 | carry-save row lemma; big glue | 36 |
| 10 | `sort8` (B-bit keys) | comb, param B | L | 4 | `?:`/`~` (WP-G); 0-1 principle library | 36 |
| 11 | `serial_mul` | seq | M to L | 4 | `LatencyTask` class (start/done) | 36 |
| 12 | `arbiter_rr` | seq, param K | M to L | 3.5 | `SeqTask` | 31 |
| 13 | `uart_tx` | seq, param D | L | 3.5 | `HistoryTask` class | 31 |
| 14 | `aes_round` | comb, fixed 128 | L | 5 | needs 1 + 8; 16 S-boxes | 30 |
| 15 | `speck_round` | comb, param N | M | 3 | none | 27 |
| 16 | `intdiv` | comb, param N | L | 3 | gate-level subtract or WP-B2; shares arithmetic with fdiv | 27 |
| 17 | `mersenne_mul` (M31) | comb, param N | L to XL | 4 | hierarchy (WP-I) to reuse `mul_n` | 24 |
| 18 | `secded` pair | comb | L | 4 | `RelTask` (don't-care spec): new class | 24 |
| 19 | `popcount` / `lzc` | comb | M | 2 | `$clog2` widths, `casez` | 24 |
| 20 | `fifo_sync` | seq, 2 params | L | 4 | run-time indexed arrays (T2) | 24 |
| 21 | `keccak_core` | seq | L to XL | 4 | `LatencyTask` + WP-F2 | 16 |
| 22 | `fmul16` / parametric FP | comb | L to XL | 4 | rounding certificate (WP-H1) | 16 |
| 23 | `div_iter`, `fdivp_iter` | seq | L / XL | 3.5 / 4 | `LatencyTask` + divider arithmetic | 14 |
| 24 | shifters, prefix adders | comb | M | 2 | conditional generate, `$clog2` | 12 |
| 25 | `acc_cpu` (accumulator machine + ROM) | seq | XL | 4.5 | `ClosedLoopTask` (environment predicate) | 9 |
| 26 | `rv_core` (RV32I subset, retirement interface) | seq | XXL | 5 | everything above | 5 |
| 27 | `async_fifo` (Gray pointers, two clocks) | seq | XXL | 4 | scheduler and CDC model (WP-S0 S5 to S7) | 4 |

## zk.golf in five lines (details: [zkgolf.md](zkgolf.md))

1. 13 circuit problems from production ZK (Keccak, SHA-256, BLAKE3, RSA-4096, secp256k1 and BLS12-381 scalar multiplication, JSON claim extraction), each with an outside baseline (circom, gnark, zk-email, Flock).
2. Score = allocations + constraints of an R1CS circuit, one additive number, *proved* in Lean (`mainCost`); leaderboard keeps the record frontier.
3. Trusted statement = human-readable `Spec` + caller `Assumptions`; the player proves soundness AND completeness (so an unsatisfiable circuit cannot win).
4. Anti-cheating = organizers' statements checked by `comparator` with a permitted-axiom list, no native-code decision procedures, structural theorems (`isR1CS`, `witgenIsIR`, `computableWitness`), pinned toolchain, public submissions.
5. Attractive = tiny spec + huge design space + published bar + hard to game; the same primitive reappears under several cost models (prime-field Keccak, GF(2) Keccak-p, K12), which is the pattern behind `keccak_round` then `keccak_core`.

## Measured headroom (repo's pinned scorer, Yosys 0.53; `experiments/score_all.sh` reproduces every row)

| task | baseline | structured / published | gap |
|---|---|---|---|
| `aes_sbox` | `case` table 786.9 GE, depth 11 | Boyar-Peralta 113 gates: 201.0 GE, depth 21 | 3.9x area, 1.9x depth |
| `clmul` N = 16 | schoolbook 775.6 GE, d 5 | Karatsuba with 4-bit base 622.3 GE, d 8 | -20% area |
| `clmul` N = 32 | schoolbook 3226.1 GE, d 6 | Karatsuba with 4-bit base 2124.2 GE, d 10 | -34% area |
| CRC-32 over 32 bits | per-output XOR of subsets 1394 GE | greedy shared XOR (Paar) 494 GE | 2.8x |
| `chacha_qr` | Yosys `+` 1212.3 GE, d 192 | gate ripple adders 1184.6 GE, d 192 | 2%, depth open |
| `keccak_round` | textbook 2965.2 GE (W = 16), d 7 | the same under every rewrite tried | about 0 |

## What the current fragment allows (details: [fragment.md](fragment.md))

Proof fragment today: flat top, continuous `assign` over `& | ^` with known literals, generate loops two deep, 1-D/2-D
packed arrays, concatenation, part-select and row targets, integer `localparam` atoms (literal `+ - *`, `/ %` by
literals). Planned this week: `~ ! ?:` and `always_comb` bodies (WP-G), `~^`, temporaries, procedural `for`, constant
functions, `$countones`, `casez`, casts, 2-state, signed (T2 days 2 to 7), word-level `+ - == < >>` (WP-B2, riskiest),
instances (WP-I, design only). Sequential: nothing in the tactics yet; ls-sv's cycle model exists (`cycleStep2`) and
WP-S0 has proved a counter for all N and all cycles (`design/sequential/CounterCycle.lean`). The three combinational
picks need only `^ & ~/~^` and generate loops; the two sequential picks need WP-S0's groundwork.

## Sequential: the first two and what they force

Reconciled with `svgolf/design/sequential/README.md` (WP-S0, written in parallel): its `SeqTask` (Lean machine +
reset protocol + Moore observation after the edge, `ClockedBy` instead of `Unclocked`, claim from every reset,
reduction theorem `satisfiedAt_of_cycle`) is the class; the counter is its spike. This study adds task content.

* **`pipe_mul`** needs two generalisations of `SeqTask.Follows`: no reset port, and a partial observation (no claim
  until the pipeline window is full, since registers start at `x`). Finding recorded in the note: *in ls-sv's
  snapshot-after-the-edge model one register stage is indistinguishable from combinational logic*, so observable
  delay is `D = stages - 1 >= 1` (proved as a sanity lemma in `seq_sketch/PipeSpec.lean`). Groundwork: `ClockedBy`
  check, `$_DFF_P_` price + `dfflegalize` (WP-S0 section 5.1; I confirmed the flow stops with "cells the GE table does not price: {'$_DFF_P_': 16}" on a 2-stage pipeline), sequence-based `postsynth`, the stage-wise generic theorem `Pipelined.of_stages`.
* **`crc32_step`** is exactly `SeqTask` (WP-S0 ladder rung 2, `D = 32` steps per clock). It forces the reset protocol, the
  one-step-simulation proof principle, and the linearity-transfer library that also serves A5.
* **Not before these two:** iterative units (`serial_mul`, `div_iter`) need a `LatencyTask` class (start/done, exact
  or bounded latency); protocol blocks (`uart_tx`) a `HistoryTask`; CPUs a `ClosedLoopTask`. WP-S0 section 6 prices the
  whole ladder at roughly ten months of lane time; the shortcut this study offers is to *reuse combinational specs
  as step functions* (`keccak_round` inside `keccak_core`, `mul` inside `pipe_mul` and `serial_mul`, `fdivp` at `(5, 11)` inside
  `fdivp_iter`), so that every sequential spec is already cross-checked.

## Where a bug could hide in the spec, and the independent cross-check used

| task | the place | cross-check (all run in this study unless marked) |
|---|---|---|
| `aes_sbox` | affine constant and direction, table typo, polynomial | algebra vs 256-entry table vs the independently derived Boyar-Peralta SLP (all 256 inputs) vs FIPS 197 Table 4 (parsed from the NIST PDF, all 256) vs AES-128 against OpenSSL (300 random blocks) and the 2001 Appendix C.1 ciphertext |
| `clmul` | bit orientation, off-by-one in output width | Kronecker-substitution implementation (integer multiply, 8 sizes), FIPS 197 `{57}*{13}={fe}` (2023, Eq. 4.7) and `{57}*{83}={c1}` (2001) after reduction |
| `chacha_qr` | rotation direction, step order | RFC 8439 vectors (2.1.1, 2.2.1), 50 full ChaCha20 blocks vs OpenSSL via `cryptography` |
| `keccak_round` | lane order, rho table, pi direction, mod-W reading, `rc` as input | two Python implementations, hashlib SHA3 (24-round composition), XKCP per-round vectors at 4 widths, Lean `decide +kernel` on 10 XKCP/SHA3/oracle rows; rho table derived from the walk and compared with the table; W = 1, 2, 4 have NO published vector (oracle only) |
| `sha256_round` | Ch/Maj operand order | NIST "abc" round 0 (`a = 5d6aebcd`, `e = fa2a4622`) and `hashlib.sha256` through 64 rounds |
| `crc32_*` | reflection, init/xorout | `zlib.crc32` continuation, RevEng check `0xCBF43926` |
| `speck_round` | rotation constants | Speck128/128 published ciphertext reproduced |
| `secded`, CPUs | **the don't-care region / the environment predicate**: an unsatisfiable or too-weak relation proves everything | mandatory non-vacuity theorem (for every ROM a compliant stimulus exists), a second implementation of the ISA by an independent author, properties of the spec proved in Lean (distance, fairness); highest review burden of all |

Easy-to-cheat flags: *sequential tasks* are where the checker's existing defences (banlist, source gate, `fourstate`,
`postsynth`, oracle) are not enough alone: the undriven/gated clock (ls-sv runs every edge process every cycle,
whatever the clock holds), declaration initializers (ls-sv honours them, synthesis drops them), latches, a one-stage
"pipeline" that is really combinational. WP-S0 section 2.3 lists the defences (`ClockedBy`, no initializers, known
outputs after reset, randomised initial netlist state); `pipe_*` adds the `D >= 1` rule. Combinational picks inherit
the existing defences unchanged; `aes_sbox` can make `postsynth` exhaustive (all 256 inputs).

## Decisions the maintainers must take

1. **Adopt the picks** (or swap `chacha_qr` for `keccak_round`); banlists: `+ - * / % **` for all three.
2. **No `CombTask` change** is needed; but a tiny trusted helper is: `ofBits` (bit-defined `BitVec`) and its lemma, used by `clmul` and
   `keccak_round` (proposal: `SvGolf/Bits.lean`, instead of copying into each `Spec`).
3. **Sequential class:** approve WP-S0's `SeqTask` plus two variants this study needs: reset-free with partial observation (`pipe_*`), then
   `LatencyTask` (start/done with exact or bounded latency), `HistoryTask`, and later `RelTask` and `ClosedLoopTask`. Each is a new trusted
   statement; none is needed before `pipe_mul` and `crc32_step`.
4. **Flop price and `dfflegalize`** (WP-S0 decision 3) and whether multi-cycle tasks add a latency axis (this study recommends fixed latency
   per task, no third axis).
5. **WP-F2** (localparam `c % W`): needed only for `keccak_round`/`keccak_core`; go or no-go. Also whether "every `W >= 1`" (a natural extension of
   Keccak beyond `W = 2^l`) is acceptable as the statement, or the range should be `W` in the seven standard widths (a finite range allows a
   per-width `decide` proof and loses the point of parametric proof).
6. **Boyar-Peralta netlist in the repo** as the reference/baseline of `aes_sbox`: a published circuit (cite J. Cryptology 2013, Yale page), translated
   gate for gate in `aes_sbox/reference/sbox_bp.sv`; confirm that is acceptable as a baseline.
7. **zk.golf idea to adopt:** each task README lists 2 to 3 outside comparison points with provenance and caveats (this study measured two).

## Files

* `README.md` (this), `zkgolf.md`, `fragment.md`; the five top candidates `01-aes-sbox.md` ... `05-crc-step.md`; `catalogue-comb.md` (A1 to A15) and
  `catalogue-seq.md` (B0 to B12).
* `aes_sbox/` (**the draft trusted `Spec.lean` of the top combinational candidate**, compiled; `oracle.py`; `validate.py`; `reference/`).
* `clmul/Spec.lean` (compiled), `chacha_qr/{Spec.lean, oracle.py, validate.py}` (compiled).
* `keccak_round/` (bonus, complete): `Spec.lean`, `SpecFacts.lean`, `SpecVectors.lean`, `oracle.py`, `validate.py`, `vectors.json` (23 rows with sources),
  `reference/*.sv`, `gen_ref.py`, `sim_check.py`, `xkcp/` (the fetched XKCP files).
* `seq_sketch/{PipeSpec,MachineSpec}.lean` (compiled shape checks, not drafts of trusted files).
* `experiments/` (generators and `score_all.sh`, which reproduces the numbers above).

## How this was checked

Lean: every `.lean` file above typechecks on `leanprover/lean4:v4.33.0-rc1` against `SvGolf.Task` through the slot wrapper
(scratch copies; the modules were renamed because a module called `Spec` collides with the `spec` library on a case-insensitive
filesystem; in the tree they would be `tasks.<name>.Spec`). No unfinished proofs and no native-code decision procedures; closed facts use `decide` or `decide +kernel`
(kernel evaluation: no extra axiom). Python: `keccak_round/validate.py`, `aes_sbox/validate.py`, `chacha_qr/validate.py` and the CRC/clmul
checks in `experiments/` all pass. Everything quoted as *recalled* in the files (published gate counts, optimal sorting networks, Montgomery's
Karatsuba-like formulas, AES MixColumns XOR counts) comes from memory and must be checked before it appears on a board.

# `clmul`: review of the trusted statement

Hard gate 6 of `PLAN2.md`: "reviewed trusted `Spec.lean`". The file under review is [Spec.lean](Spec.lean)
(it is in the `tasks` library: `lake build tasks.clmul.Spec` builds it). The task is registered with the
status in `task.json` (a draft until the reference proof lands, then ready); changing the statement after
your review is a small follow-up (the reference proof uses the names `a`, `b`, `p`, the functions `coeff`
and `ofBits`, and nothing else of the Spec).

## The statement in plain words

A submission is one module with exactly these ports, in this order, and ONE parameter `N`:

```systemverilog
module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
```

It satisfies the task when (this is `CombTask.Statement`, the same shape as `add` and `mul`): for every
`N ≥ 1` the ports are exactly `a`, `b` (inputs, `N` bits) and `p` (output, `2N-1` bits); every run
terminates; no process is clocked (`Unclocked`); and in every cycle whose stimulus drives `a` and `b` with
KNOWN values, the snapshot's `p` is the coefficient vector of the product of the polynomials over GF(2)
that `a` and `b` encode (bit `i` is the coefficient of `x^i`):

    p_k = XOR over all pairs (i, j), 0 ≤ i, j < N, with i + j = k, of (a_i AND b_j),    0 ≤ k ≤ 2N-2.

This is the UNREDUCED carry-less product (no modulus): `PCLMULQDQ`, the core of GHASH, the polynomial
multiplication of every binary-field, CRC and BCH construction. It is `mul` with every carry removed.

In Lean (`ofBits n f` is the `n`-bit vector whose bit `k` is `f k`):

```lean
def coeff (N : Nat) (a b : BitVec N) (k : Nat) : Bool :=
  (List.range N).foldl (fun acc i =>
    (List.range N).foldl (fun acc j => acc ^^ (decide (i + j = k) && a.getLsbD i && b.getLsbD j)) acc) false
def task : CombTask where
  inRange N := 1 ≤ N
  inputs N := [("a", N), ("b", N)]
  outputs N := [("p", 2 * N - 1)]
  fn N := fun (a, b, ()) => (ofBits (2 * N - 1) (coeff N a b), ())
```

(As reviewed. Since 2026-11-06 the range is `1 ≤ N ∧ N < 2 ^ 30`, so that the widths `2N-1` and `2N-2`, `int`
expressions of the module, stay below `2^31`: `Spec.lean`, README "The statement".)

## Why the definition can be trusted (independent evidence, none of it part of the statement)

All of this is run by `tests/run.py` (`tests/clmul/validate/validate.py`, `Spec.lean`'s `example`s):

* **The definition is the words.** `coeff` is the literal double sum over `i, j < N` with `i + j = k`:
  no natural-number subtraction (the week-2 draft summed over `i` with `b.getLsbD (k - i)` and a guard
  `i ≤ k`, which leans on truncated subtraction and on out-of-range bit reads being `false`; both are
  correct but a reviewer has to check them; the double sum has nothing to check).
* **`oracle.py`** (shift-and-XOR on Python integers, a different algorithm: XOR of `a << i` over the set bits
  `i` of `b`) equals an **independent implementation by Kronecker substitution** (spread the bits
  `bit_length(N) + 1` apart, multiply as integers, read the parity of each group) on every pair at
  `N ≤ 6` and on random pairs up to `N = 100`.
* **The Lean spec equals the oracle**: `Dump.lean` evaluates the trusted `task.fn` through Lean's
  interpreter on EVERY pair at `N = 1 .. 7` (21 844 pairs) and on sample pairs up to `N = 64`;
  `validate.py` compares each with the oracle.
* **Closed `decide` examples in `Spec.lean`**: `(x+1)^2 = x^2+1`, `(x^2+1)(x+1) = x^3+x^2+x+1`, the
  `N = 1` AND, `(1+...+x^15)^2 = 1+x^2+...+x^30` (`0x55555555`, N = 16), and the two products of FIPS 197
  Section 4.2: `0x57 (x) 0x83 = 0x2b79` and `0x57 (x) 0x13 = 0x0589`, which reduce modulo `0x11b` to the
  standard's `{c1}` (2001 edition) and `{fe}` (2023 edition, Eq. (4.7)); `validate.py` does the reduction.
* **Verilator** simulates the reference, every baseline and every wrong design against a testbench that
  computes the product by whole-word shift-and-XOR (exhaustive at `N ≤ 8`, 100 000 random pairs up to `N = 64`).
* **Algebra**: `validate.py` also checks commutativity, distributivity over XOR and the `x`-shift law on
  random operands.

## The modelling choices to look at

1. **Output width `2N-1`.** The product of two polynomials of degree below `N` has degree at most `2N-2`:
   `2N-1` bits is exact, no constant-zero top bit (`2N` would force one; `tests/clmul/negative/wide_out.sv` is
   the design that does it and is refused by the interface conjunct). At `N = 1` the output is ONE bit, the
   AND of the inputs. A design must therefore also handle `N = 1` and the generate loops with zero
   iterations (the upper part of the reference is a loop over `N-1` positions).
2. **Bit orientation: bit `i` is the coefficient of `x^i`** (little-endian, the opposite of GHASH's reflected
   convention). A "GCM multiply" variant would be a separate statement. `negative/reversed_p.sv` (the
   reflected orientation) is refused.
3. **`ofBits` in the Spec.** The draft proposed a shared trusted `SvGolf/Bits.lean` (`ofBits` and its lemma,
   also used by the `keccak_round` draft); this Spec keeps a private copy to leave `SvGolf` untouched. If
   you adopt the shared file, `Spec.lean` imports it instead (the reference proof proves the lemma it needs,
   `getLsbD_ofBits`, itself).
4. **The banlist is `+ - *`** (`task.json`), NOT the `+ - * / % **` of `add` and `mul`. Your rule of
   2026-10-31: word-level operators are available to every task except those about implementing the
   arithmetic itself; `clmul` is about building a product, so the operators that build integer products
   and sums are banned at run time, and constant arithmetic (parameters, genvar indices) stays legal.
   Measured: the Kronecker design (`negative/kronecker_mul.sv`, a CORRECT carry-less multiplier written
   with the integer multiplier on bit-spread operands) synthesizes to exactly the same netlist as the array
   reference (772.267 GE, depth 6, at `N = 16`): Yosys folds the constant zeros. So the ban of `*` does not
   protect the score, it protects the task: without it the one-line trick `sp = sa * sb` would be a design,
   and the proof would be about the integer multiplier. `+` is banned because a one-bit `+` is an XOR with
   the carry dropped (`negative/plus_xor.sv`, a correct array, also the same netlist). `/ % **` are not
   banned: none of them reaches this function and Yosys does not merge them into the cells of `+ *`.
   Say if you prefer the full `+ - * / % **` set for uniformity with `add` and `mul`.
   UPDATE 2026-11-06: the banlist is now `+ - * / % **`, for another reason than uniformity: every task bans
   run-time `/ % **` (the svGolf README, "Rules"), because a zero divisor makes an x from known inputs that
   ls-sv and Yosys resolve differently (`tests/clmul/attacks/div_zero_x.sv`).
5. **Range `1 ≤ N`, scoring point `N = 16`, reported at 8 and 32** (`mul`'s choice; the study measured the
   Karatsuba crossover at those sizes).
6. **No hidden state, one statement**: the unchanged `CombTask`; no change to `SvGolf/Task.lean`.

## What it does NOT ban

`<<`, `>>`, `?:`, `&`, `|`, `^`, `~`, reductions, `case`, `generate if`, procedural code within ls-sv's tier:
legal and scored. The shift-and-XOR word form `p ^= b[i] ? a << i : 0` is a legal (if tactic-unfriendly)
design.

## How people write clmul, and what the pipeline does with it (your instruction of 2026-11-01)

The full table is in [README.md](README.md), "How people write clmul"; the evidence is the 23 files from 19
repositories fetched for it (URLs and licences there; fetched as untrusted data, nothing copied) and 18
test designs, one per style, under `tests/clmul/attacks/` (correct for every `N`, simulated, pinned as advisory
entries of `tests/expected.json`). The eight-family survey that landed after it (`svgolf/design/real-world-sv/SURVEY.md`)
agrees on every clmul-shaped probe I compared; its headline for this task is that the natural procedural loop
"dies three times" (the extractor's `Unsupported ForLoopStatement`, the loop variable's `LocalDecl`, the fourstate
rule `sg-fs-loop-index`), and a work package (WP-PROC) is designing the lowering. The honest summary:

* More than half of the real multiplier cores (9 of 16) are written with a **procedural `for` loop**
  (`for (int i = 0; i < N; i++) if (b[i]) p ^= a << i;`, or the nested `r[i+j] ^= a[i] & b[j]`). Every such design
  is **refused at the `fourstate` stage** today, before ls-sv or the tactics see it: the loop counter is a
  32-bit `int`, hence a run-time index that "can address outside the declared range". The message does not say
  that loops themselves are the problem. Register ids: `st-for` (value rank 1), `ex-user-call` (2, functions),
  `st-compound` (17, `^=`), plus generate-local declarations; `le-recursion` (14) for recursive Karatsuba.
* The scorer cannot read a function with `return` (the pinned Yosys frontend: syntax error): a gap outside ls-sv.
* The styles that reach the proof stage (generate-for with word-level `<<` and `?:`, reductions with indexed part
  selects, Karatsuba on instances) are stopped by the tactics: replication, indexed part select, a generate-for
  start that is not a literal, shifts, module instances.
* Scores do not depend on the style (every schoolbook form lands within 0.7 % of the array at `N = 16`).
* What our reference covers: the generate-for AND/XOR array on a 2-D packed accumulator, which is also the shape
  Marian's GF(2^128) multiplier has after unrolling.

## Cheating surfaces and which defence applies (all pinned by `tests/run.py`)

| trick | defence | test |
|---|---|---|
| the integer product (carries kept) | not a carry-less product: the proof and the oracle reject it | the proof; `postsynth` oracle warning |
| Kronecker: spread, multiply, read parities | banlist `*` (front check and Yosys `$mul` backstop) | `negative/kronecker_mul` |
| a one-bit `+` as XOR | banlist `+` (`$add`) | `negative/plus_xor` |
| correct only at the scoring point `N = 16` (generate-if on `N`) | the statement is for every `N ≥ 1`: a concrete run at `N = 1` refutes it | `negative/only_n16` (`Refute.lean`) |
| a wrong bit, a dropped term, OR for XOR | the proof is for all inputs at all `N`; the advisory oracle reports the mismatch before the proof | `negative/top_shift`, `drop_top`, `or_accumulate` |
| the reflected (GHASH) orientation | the proof; the oracle warning | `negative/reversed_p` |
| a `2N`-bit `p` (right value, wrong port) | the interface conjunct | `negative/wide_out` (`Refute.lean`) |
| an undriven or gated clock, a latch, a clocked process | clock discipline, `fourstate`, `Unclocked`, `Terminates2` | (the `add` and `_example` tests) |
| `x`/`z` literals, `unique`/`priority`, out-of-range selects | source gate, `fourstate`, post-synthesis | (the shared attacks) |

Not a surface but worth knowing: for a flat netlist the order of the statements moves the score (the
`aes_sbox` finding). The reference array here is a generate family whose score did not move under the
`canon` step's reorderings and renamings (`tests/expected.json`, `canonical_layout`); the flat baselines
under `tests/clmul/baselines/` are the generator's emission order byte for byte, which is their canon.

## Questions for you

1. Output width `2N-1` with the `N = 1` single-bit output: acceptable (vs. a constant-zero top bit at `2N`)?
2. The double-sum `coeff` (vs. the draft's single sum with `k - i`): keep?
3. Private `ofBits` in the Spec (vs. a shared `SvGolf/Bits.lean`): keep private?
4. Banlist `+ - *` (vs. the full `+ - * / % **`): keep?
5. Scoring point `N = 16`, reported at 8 and 32: confirmed?
6. Little-endian orientation (bit `i` = coefficient of `x^i`): confirmed?
7. The natural procedural styles are refused at `fourstate` today (the table above): do you want the task to
   wait for `st-for` / `ex-user-call` / `st-compound` (so that contestants can write the loop), or is a
   generate-for array the intended idiom for this task? (Nothing in `LeanModels/Sv` was touched.)

## Decisions (2026-11-02: the maintainers left the seven questions to the lead, asking for the task to be as relevant and interesting to golfers as possible)

All seven answers keep the statement as it is: no change to `Spec.lean` or `task.json`.

1. **Keep `2N-1`.** It is the exact width. The `N = 1` one-bit output and the zero-iteration loops are a real corner that every
   correct design has to handle, which is the kind of thing "proved for every `N`" is meant to test.
2. **Keep the double sum.** It is the words of the definition; there is nothing for a reviewer to check.
3. **Keep `ofBits` private.** Promote it to a shared `SvGolf/Bits.lean` when the second task that needs it (`keccak_round`) is
   registered; the move is mechanical and no proof here depends on where it lives.
4. **Keep the banlist `+ - *`.** It protects what the task is about (building a product from XOR and AND) without touching the
   score: the Kronecker and one-bit-`+` tricks synthesize to the same netlist as the array. `/ % **` cannot reach this function.
5. **Keep the scoring point `N = 16`, reported at 8 and 32.** The (area, depth) frontier at 16 already has a real tension: the
   array is shallow, Karatsuba is about 20 % smaller (36 % at `N = 32`, README table) and deeper.
6. **Keep little-endian.** The reflected GHASH orientation plus the reduction modulo `x^128 + x^7 + x^2 + x + 1` is a different,
   larger statement; if wanted it is a separate task (a `GF(2^128)` multiplier), not a variant of this one.
7. **Do not wait for the procedural styles; the generate-for array is the intended idiom today.** The `for`-loop styles arrive with
   WP-PROC and widen the set of accepted designs without changing the statement, so every proof and score stays valid. The
   `fourstate` message that refuses them today ("can address outside the declared range") does not say that loops are the problem
   and should say "write a generate-for"; that is a checker-message change, held until the nightly suite is done.

What makes the task interesting to golfers, so it is not lost: every schoolbook form lands within 0.7 % of the array, so the
leaderboard only moves with a different algorithm. The target is visible (Karatsuba is 20 % smaller at `N = 16`) and nobody has a
proved design for it; the tactics do not read module instances or recursion yet, so a proof is by hand in Lean (the checker only
needs the theorem). Because the statement is for every `N`, a design that changes algorithm with `N` (schoolbook below a
threshold, Karatsuba above) is legal and is proved per branch.

# `aes_sbox`: review of the trusted statement

Hard gate 6 of `PLAN2.md`: "reviewed trusted `Spec.lean`". The file under review is [Spec.lean](Spec.lean) (it typechecks against
`SvGolf.Task`; re-compiled by the lead). Nothing is registered in `tests/expected.json` until you approve it.

## The statement in plain words

A submission is one module with exactly these ports, in this order:

```systemverilog
module aes_sbox (input logic [7:0] x, output logic [7:0] y);
```

It satisfies the task when (this is `CombTask.StatementFixed`, the same shape as `fdiv16`): the ports are exactly `x` (input, 8 bits)
and `y` (output, 8 bits); every run terminates; no process is clocked (`Unclocked`); and in every cycle whose stimulus drives `x`
with a KNOWN value, the snapshot's `y` equals `sbox x`.

`sbox` is defined algebraically, as FIPS 197 §5.1.1 defines it, not as a 256-entry table:
`sbox x = affine (ginv x)` where `ginv` is the multiplicative inverse in GF(2^8) = GF(2)[x]/(x^8+x^4+x^3+x+1) (0 maps to 0) and
`affine b = b ^ rotl b 1 ^ rotl b 2 ^ rotl b 3 ^ rotl b 4 ^ 0x63`. Bit order: `x[7]` is the most significant bit; `BitVec 8`.

## Why the definition can be trusted (independent evidence, none of it part of the statement)

* The algebra reproduces the FIPS 197 table on all 256 inputs by `decide +kernel` inside `Spec.lean` (an `example`), and the S-box
  is a permutation (also an `example`). The table was PARSED from the NIST PDF (Table 4), not typed.
* The standard's own worked values hold: `S(00) = 63`, `S(53) = ed`, `S(ff) = 16`; `{57} * {83} = {c1}`.
* `oracle.py` is a separate implementation in Python (`validate.py`: all 256 entries, five anchors, the FIPS 197 Appendix C.1 AES-128
  example, and 300 random AES-128 blocks against OpenSSL through this S-box).
* The Boyar-Peralta 113-gate circuit, translated gate for gate (`reference/sbox_bp.sv`), equals the table on all 256 inputs.

## The one modelling choice to look at

`ginv a` is computed as `a^254` by repeated squaring (`a2 * a4 * ... * a128`). That equals the inverse because the multiplicative group
has order 255, and it gives 0 for 0. The alternative is a relational definition ("the unique `y` with `gmul x y = 1`, and 0 for 0"),
which needs no group fact but is not computable, so the `decide` cross-checks above would not run. I kept the computable form; the
256-entry cross-check against the NIST table is what ties it to the standard. Say if you prefer the relational form.

## What it does NOT ban (your decision of 10/30)

No operator is banned: a lookup `case` table, `+ - *`, anything. The `$macc/$mul/$alu` backstop is off for this task. The scoring point is
the fixed size. Measured with the pinned scorer: the `case` table 786.9 GE (depth 11), the Boyar-Peralta circuit 201.0 GE (depth 21).

## Cheating surfaces and which defense applies

| trick | defense |
|---|---|
| a `case` that omits entries and falls to `default: y = 'x` (or reads x/z) | source gate (x/z literals), fourstate stage, the post-synthesis check |
| `unique case` / `priority` so synthesis assumes a missing entry | source gate refuses the qualifiers |
| comparing with `===` / `casex` to exploit x | source gate / fourstate |
| an undriven or gated clock, a latch | clock discipline (loader), fourstate, `Unclocked`, `Terminates2` |
| a design the loader keeps as Unsupported | `design` stage rejects `hasUnsupported` |
| a design that differs from the S-box on a few inputs | the proof is for all 256 inputs; the advisory oracle also reports mismatches before the proof; the post-synthesis check can run all 256 vectors (the input space is tiny) |

## Questions for you

1. Port and module names `aes_sbox`, `x`, `y`: acceptable?
2. `ginv` as `a^254`: keep, or switch to the relational definition?
3. Fixed size only (statement at the single point `N = 0`, like `fdiv16`): confirmed? (The parametric analogues, `gfmul` and `gfinv`, come
   later; the S-box itself is inherently 8-bit.)
4. May the Boyar-Peralta circuit be in the repo as a cited baseline (J. Boyar and R. Peralta, "A new combinational logic minimization
   technique with applications to cryptology", SEA 2010; gate count and depth "recalled" until checked against the circuit)?

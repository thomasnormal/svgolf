# `aes_sbox`: review of the trusted statement

Hard gate 6 of `PLAN2.md`: "reviewed trusted `Spec.lean`". The file under review is [Spec.lean](Spec.lean)
(it is in the `tasks` library: `lake build tasks.aes_sbox.Spec` builds it, 15 s). The task is registered
as a READY task: the Boyar-Peralta reference is proved (`reference/sbox_bp.lean`); changing the statement
after your review is a small follow-up (the proof is generated from the netlist and uses only the names
`x`, `y` and the function `sbox`).

## The statement in plain words

A submission is one module with exactly these ports, in this order:

```systemverilog
module aes_sbox (input logic [7:0] x, output logic [7:0] y);
```

It satisfies the task when (this is `CombTask.StatementFixed`, the same shape as the former 16-bit divider task): the ports are
exactly `x` (input, 8 bits) and `y` (output, 8 bits); every run terminates; no process is clocked
(`Unclocked`); and in every cycle whose stimulus drives `x` with a KNOWN value, the snapshot's `y` equals
`sbox x`.

`sbox` is defined algebraically, as FIPS 197 §5.1.1 defines it, not as a 256-entry table:
`sbox x = affine (ginv x)` where `ginv` is the multiplicative inverse in
GF(2^8) = GF(2)[z]/(z^8+z^4+z^3+z+1) (0 maps to 0) and
`affine b = b ^ rotl b 1 ^ rotl b 2 ^ rotl b 3 ^ rotl b 4 ^ 0x63`. Bit order: `BitVec 8`, `x[7]` is the
most significant bit.

## Why the definition can be trusted (independent evidence, none of it part of the statement)

All of this is run by `tests/run.py` (`tests/aes_sbox/validate/validate.py`, `Spec.lean`'s `example`s):

* **The FIPS table, two parses.** The algebra reproduces the 256-entry table of FIPS 197 Table 4 (2023
  edition) by `decide +kernel` inside `Spec.lean` (an `example`); `vectors.json` holds the table parsed from
  the NIST PDF (<https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf>, sha256 `62c86eb5...becd1`
  at fetch time 2026-10-30) by the task study, and WP-A1 re-parsed the PDF with a second extraction
  (`pdftotext -layout`, a regex over the 16 rows of Table 4) and got the same 256 bytes.
* **The standard's own worked values**: `S(53) = ed` (§5.1.1: `s_{r,c} = {53}` gives `{ed}`), `S(00) = 63`,
  `S(ff) = 16`, the first row of Table 4, `{57} * {13} = {fe}` (2023, Eq. 4.7), `{57} * {83} = {c1}` (2001).
  The S-box is a permutation (also a `Spec.lean` example).
* **AES end to end**: a textbook AES-128 built on the oracle's table reproduces the FIPS 197 (2001)
  Appendix C.1 ciphertext (`69c4e0d8...c55a`) and agrees with OpenSSL's AES-128 on 300 random blocks. A
  wrong table entry would be hit by the random blocks.
* **`oracle.py`** is a separate implementation in Python (the same algebra, written separately).
* **An independently derived circuit**: the Boyar-Peralta 113-gate netlist (the authors' own file, fetched
  and checked gate for gate against `reference/sbox_bp.sv`) equals the table on all 256 inputs; so does the
  authors' depth-16 netlist. They are the product of a search, not of this algebra, so the S-box they
  compute and the one `Spec.lean` defines agree for an independent reason.
* **Verilator** simulates the reference and the baselines on all 256 inputs against the oracle.

## The modelling choices to look at

1. `ginv a` is computed as `a^254` by repeated squaring (`a2 * a4 * ... * a128`). That equals the inverse
   because the multiplicative group has order 255, and it gives 0 for 0. The alternative is a relational
   definition ("the unique `y` with `gmul x y = 1`, and 0 for 0"), which needs no group fact but is not
   computable, so the `decide` cross-checks would not run. I kept the computable form; the 256-entry
   cross-check against the NIST table ties it to the standard. Say if you prefer the relational form.
2. Names `x`, `y` (the first draft used `a`; the study settled on `x`/`y`, as FIPS 197 calls the input byte
   `xy`).
3. Fixed size only (statement at the single point `N = 0`, like the former 16-bit divider task). The parametric analogues
   (`gfmul`, `gfinv` over any field) would be separate tasks.

## What it does NOT ban (your decision of 10/30)

No operator is banned: a lookup `case` table, `+ - *`, anything. `task.json` has `banlist.operators: []`,
which also switches the Yosys `$macc/$mul/$alu` backstop off. The scoring point is the fixed size. Measured with the pinned scorer: the
`case` table 786.894 GE (depth 11), the Boyar-Peralta circuit 200.986 GE (depth 21), the depth-16 circuit
216.322 GE (depth 18).

## Cheating surfaces and which defence applies (all pinned by `tests/run.py`)

| trick | defence | test |
|---|---|---|
| a `case` that omits entries and falls to `default: y = 8'bx` | source gate (x/z literals); the exhaustive post-synthesis check alone also rejects it (ls-sv gives x on the omitted input) | `attacks/case_missing_x` |
| the same with no default (a latch) | `fourstate` (Yosys infers a latch) | `attacks/case_missing_nodefault` |
| `unique case` / `priority` so synthesis assumes a missing entry, or a never-matching arm for a 0 GE netlist | source gate refuses the qualifiers; post-synthesis alone rejects | `attacks/unique_case_partial`, `attacks/unique_zero_ge` |
| an x-valued unreachable default in an otherwise right table | source gate | `negative/x_default` |
| an undriven output bit | `fourstate` (no driver) | `negative/undriven_bit` |
| an undriven or gated clock, a latch, a clocked process | clock discipline (loader), `fourstate`, `Unclocked`, `Terminates2` | (the `add` and `_example` tests) |
| a design the loader keeps as Unsupported | the `design` stage rejects `hasUnsupported` | (the `_example` tests) |
| a design that differs from the S-box on a few inputs (one entry, one bit, wrong constant, bit order, inverse S-box) | the proof is for all 256 inputs; the post-synthesis check is exhaustive here (256 of 256 vectors in both the full and the light mode); the advisory oracle reports the mismatch before the proof | `negative/one_entry`, `no_constant`, `reversed_bits`, `inverse_sbox` |
| right circuit, wrong interface (names) | the interface conjunct | `negative/wrong_names` |

Not a surface but worth knowing: for a flat netlist, the order of the statements moves the score by
about +-5% (README, Findings). It is a golf degree of freedom the canonical flow does not remove. Decided
(2026-10-31): that is fine; golfers can run ABC themselves and search for the best-scoring statement order before they
submit.

## Questions for you (answered 2026-10-31: all four accepted as written)

1. Port and module names `aes_sbox`, `x`, `y`: acceptable?
2. `ginv` as `a^254`: keep, or switch to the relational definition?
3. Fixed size only (statement at the single point `N = 0`, like the former 16-bit divider task): confirmed?
4. May the Boyar-Peralta circuits be in the repo as cited baselines (the authors' netlist files are
   public; the repo keeps a translation and, in `tests/aes_sbox/validate/`, a copy of each file with its
   sha256; papers: SEA 2010, J. Cryptology 2013, IFIP SEC 2012; gate figures verified from the files,
   attribution of which paper printed which figure "recalled")?

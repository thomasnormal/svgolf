# 02. `clmul`: N-bit carry-less multiplier (polynomial product over GF(2)), for every N

**Pitch.** `mul` with the carries removed: AND for the partial products, XOR for the sums, no adders. It is
inside today's proof fragment with no tactic work, its schoolbook proof is easier than `mul`'s, and it has a real
optimisation space with a famous name on it: **Karatsuba** (measured: 20% smaller at N = 16, 34% smaller at N = 32,
with a depth price). It is also the first task whose best designs want recursion (`le-recursion`, rank 14, names
Karatsuba), so it tells us what the module system must deliver.

**Header.**

```systemverilog
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p          // degree of the product is at most 2N-2: no constant-zero top bit
);
```

**Trusted statement.** For every `N >= 1`: exactly the ports `a`, `b` (input, `N` bits) and `p` (output, `2N-1`
bits); no clocked process; every run terminates; whenever `a` and `b` are driven with known values,
`p_k = XOR over i + j = k of (a_i AND b_j)` for `0 <= k <= 2N-2` (bit `i` of a vector is the coefficient of `x^i`).
Unchanged `CombTask`/`CombTask.Statement`; the task is one-parameter, in range `1 <= N`.

**`Spec.lean`** (draft, compiles: `clmul/Spec.lean`):

```lean
def ofBits : (n : Nat) → (Nat → Bool) → BitVec n            -- bit k of the result is f k
  | 0, _ => 0#0
  | n + 1, f => ofBits n (fun k => f (k + 1)) ++ BitVec.ofBool (f 0)
def coeff (N : Nat) (a b : BitVec N) (k : Nat) : Bool :=
  (List.range N).foldl (fun acc i => acc ^^ (decide (i ≤ k) && a.getLsbD i && b.getLsbD (k - i))) false
def task : CombTask where
  inRange N := 1 ≤ N
  inputs N := [("a", N), ("b", N)]
  outputs N := [("p", 2 * N - 1)]
  fn N := fun (a, b, ()) => (ofBits (2 * N - 1) (coeff N a b), ())
```

`ofBits` is shared with the Keccak draft; if adopted it belongs in a small trusted `SvGolf/Bits.lean` with its
lemma `getLsbD_ofBits` (proved in `keccak_round/SpecFacts.lean`) instead of being copied into each `Spec`.
The draft's `decide` examples: `(x+1)^2 = x^2+1`; `(x^2+1)(x+1) = x^3+x^2+x+1`; `(1+...+x^15)^2 = 1+x^2+...+x^30`
(N = 16, `0x55555555`); and the two products of FIPS 197 Section 4.2: unreduced `0x57 (x) 0x83 = 0x2b79`,
`0x57 (x) 0x13 = 0x0589`, which reduce modulo `0x11b` to the standard's `{c1}` and `{fe}`.

**Oracle and independent checks.** `oracle`: shift-and-XOR in Python. Independent implementation used to
validate it: **Kronecker substitution** (spread the bits `k = bit_length(N)+1` apart, multiply as integers,
read the parity of each group): equal on random pairs for N in {1, 2, 3, 8, 16, 32, 64, 100}. Published
anchors: the FIPS 197 products above (verified after reduction; `{57}*{13}={fe}` is Equation (4.7) of the 2023 edition,
`{57}*{83}={c1}` is in the 2001 edition). For a later "reduced" variant, the GHASH
vectors of the NIST GCM spec test cases are the published source (they need the bit-reflected reduction).

**Banlist, scoring point.** Ban `+ - * / % **` (so `*` cannot be used through a Kronecker trick, and nobody
builds the product from an integer multiplier). Scoring point `N = 16`, reported at 8 and 32.

**Measured headroom** (generated flat netlists, each simulated against the oracle; pinned flow;
`experiments/clmul_gen.py`, `experiments/score_all.sh`):

| N | design | AND | XOR | area GE | depth |
|---|---|---|---|---|---|
| 16 | schoolbook | 256 | 225 | 775.597 | 5 |
| 16 | Karatsuba all the way down | 81 | 360 | 745.297 | 9 |
| 16 | Karatsuba, schoolbook base 2 | 108 | 279 | 675.635 | 9 |
| 16 | Karatsuba, schoolbook base 4 | 144 | 225 | **622.297** | 8 |
| 16 | Karatsuba, schoolbook base 8 | 192 | 207 | 655.282 | 7 |
| 32 | schoolbook | 1024 | 961 | 3226.053 | 6 |
| 32 | Karatsuba, base 4 | 432 | 799 | **2124.225** | 10 |

An area/depth Pareto front with an interior optimum (base 4), exactly the shape a leaderboard wants; and
beyond Karatsuba the literature has 3-way and Toom-like formulas over GF(2) (Montgomery's 5-, 6- and 7-term
formulas with 13, 17 and 22 multiplications are the ones to look up; Bernstein, Cenk-Ozbudak, Fan-Hasan for
bit-parallel multipliers), so the bar to beat is outside the repo.

**What it needs.**
* Schoolbook reference: today's fragment (2-D packed arrays, two-deep generate loops, part-select targets), same
  shape as `mul_n` with XOR where `mul_n` has a full adder. Rows are laid out skewed (`row[i]` placed at offset `i`
  by a part-select target `s[i][i+N-1:i]`) so that no index is `i*j`.
* One-level Karatsuba reference (three half-size schoolbook blocks, `N = 2M`): in the fragment as three generate
  families plus pre/post XOR layers, range `N` even, `localparam integer M = N / 2` (`/` by a literal is in WP-F).
* Recursive Karatsuba for every N: needs instances and recursion (WP-I, F3b). Not this week; the task is useful
  without it, and its absence is the motivation.

**Proof strategy.** Define `bfXor f n = XOR_{j<n} f j` next to `bfVal` in CombLib with the same family of lemmas
(`congr`, `split`, `shift`, `and`). Schoolbook: row `i` of the accumulator satisfies
`acc[i+1][k] = acc[i][k] XOR (b_i AND a_{k-i})` for `i <= k < i+N` and is unchanged elsewhere; induction on `i`
gives `acc[N][k] = coeff N a b k` through one prefix lemma
`coeff` of `b` masked below `i+1` = `coeff` masked below `i` XOR `(b_i && a_{k-i})`. No carries and no `Nat`
arithmetic: easier than `mul_n` (235 lines with tactics), I would estimate 150 to 200. Karatsuba one level:
`clmul` is bilinear and commutes with shifts (`clmul_xor_left`, `clmul_shift`, two inductions), then the identity
`(aL + x^M aH)(bL + x^M bH) = L + x^M (M' + L + H) + x^2M H` over coefficient vectors, which is ring algebra in
GF(2)[x] done on coefficient functions.

**Effort: M** (2 to 3 days for spec, oracle, schoolbook reference and proof; +2 days for one-level Karatsuba and its
algebra lemmas, which also seed the CRC/GHASH library).

**Risks.** (1) Off-by-one in the output width: `2N-1` is exact; `2N` would force a constant-zero top bit
(harmless but clutter). Chosen `2N-1`; the draft and the oracle agree on it. (2) Bit orientation: bit `i` is the
coefficient of `x^i`, the opposite of GHASH's reflected convention; a task variant "GCM multiply" would need its own
statement. (3) The parametric Karatsuba is the interesting design and is out of the fragment for now.

**Cheating and checker coverage.** Total function; no hidden state. The only borderline tool is integer `*`
(banned); the front check also bans `.sum()`/`.product()` and `$countones`, the other ways to smuggle arithmetic.
All existing defences apply (source gate, `fourstate`, banlist, `postsynth` sampling with harvested constants).

**Appeal: 4/5.** Crisp, parametric ("for every N"), measurable theory-meets-practice gradient (Karatsuba crossover),
generalises to a family (reduction polynomials for AES, GCM, BCH; CRC), and sets the proof library for them.

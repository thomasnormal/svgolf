# zk.golf, as far as it can be read from outside (fetched 2026-10-30)

Sources: the site's `llms.txt` (the agent API and submission contract), its public challenge API
(`/api/agent/v1/challenges`: 13 challenges with baselines, best scores and comparison points), the
challenge tarball (`/challenges.tar.gz`, the Lean project `zksecurity/zk-golf-challenges`: `Challenge/Specs`,
`Challenge/Instances/*/{Interface,Challenge,Cost}.lean`, `configs/*.json`, `Tests/`), and the site's own "How it
works" text. Everything below is a paraphrase; nothing is copied. A local copy of the raw files is in the WP-T0
work directory, not in the repo.

## What the challenges are

Thirteen zero-knowledge circuit problems, each a real primitive that production provers already ship, so each
has outside baselines:

| family | challenges (best known score vs baseline, lower is better) |
|---|---|
| warm-up | assert that 16 field elements are bytes (240 vs 272) |
| hashes over a prime field | SHA-256 of up to 256 bytes with in-circuit padding (131 995 vs 413 810), Keccak-f[1600] (168 960 vs 307 200) |
| hashes over GF(2) ("canonical R1CS") | SHA-256 compression (44 430 vs 95 904), BLAKE3 compression (20 596 vs 173 760), KangarooTwelve's 12-round Keccak-p[1600] (38 400, untouched), Keccak-p[800,12] (19 200, untouched) |
| signatures | RSA-4096 PKCS#1 v1.5 verification (292 727 vs 827 136) |
| elliptic curves | secp256k1 and BLS12-381 G1 scalar multiplication, variable and fixed base (16.5M to 25M baselines, best 25 724 to 565 299) |
| parsing | extract and validate the claims of a Google ID token (JSON, schema, UTF-8): 209 799 vs 2 817 511 |

## How they are scored

One additive number: `cost = allocations + constraints` of an R1CS circuit over the challenge's field (the
caller's inputs are free; for the GF(2) family an extra "identity C" shape rule fixes what a row may look like).
The claimed cost must be proved in Lean (`mainCost`), so the score is a theorem, not a measurement. Each
challenge lists a baseline circuit and "comparison points" (circom with `--O2`, gnark with lookups disabled,
zk-email, xJsnark, Flock) with the interface differences written out, so a reader can tell whether a number is
apples to apples. The leaderboard keeps the record-setting frontier; every verified submission's source is
downloadable, and an `assisted_by` field names the model, with effort, that helped.

## What the trusted statement is

A human-readable `Spec` (usually built on a native reference implementation in Lean, e.g. a Keccak-f written
with lanes as naturals, or a JSON parser), a precondition `Assumptions` that the caller is responsible for
(`IsBitString`), and two proofs about the circuit, built in the Clean circuit DSL: **soundness** (every
assignment satisfying the constraints satisfies the spec) and **completeness** (every honest input has a
witness). Requiring both rules out the cheapest cheat, an unsatisfiable circuit, which is sound for every
spec.

## What it does about cheating

* The submission's theorem statements are compared with the organizers' by Lean's `comparator`, with a
  per-challenge list of permitted axioms (the usual three plus the challenge's own field-prime axiom);
  native-code decision procedures are not accepted; submissions are flat files with a mandatory `Main.lean`; Mathlib, Clean and the
  toolchain are pinned (changing them makes the verifier time out; hard limit 1 200 s).
* Structural obligations make the cost model honest: `isR1CS` (every assert is one rank-1 row, so cost cannot be
  smuggled into a higher-degree constraint), `witgenIsIR` (witness generation must be data, not an opaque
  closure), `computableWitness` (a witness may depend only on the inputs and earlier witnesses, so a prover hint
  cannot carry the answer), `requirementsChannelsLawful`.
* Social defences: everything verified is public; baselines come from outside tools; the organizers' `main`
  branch is the trusted starting point.

## What makes a challenge attractive (the pattern to copy)

1. **A tiny spec with a big design space.** The statement is one reference function; the circuit can be anything
   (bit packing, lookup-free decompositions, GF(2) tricks, limb sizes). Gaps of 2x to 10x between baseline and
   best are normal.
2. **A published bar.** Each task has an outside number (circom/gnark/zk-email/Flock/xJsnark) that a newcomer
   can try to beat; progress is legible.
3. **Hard to game.** The statement is total (completeness), the cost is proved, the model rejects escape hatches.
4. **Layered difficulty.** Hello-world, then primitives (Keccak, SHA), then composites (RSA, JSON); the same
   primitive appears in several cost models (prime-field Keccak, GF(2) Keccak-p[800,12], K12).

## What to take for svGolf

* The **comparison point with provenance** (tool, version, flags, what differs) is cheap and makes a board
  readable: svGolf already lists non-record reference points in README; each new task should carry 2 to 3 with
  the Yosys score of the published structure (this study measured two: Boyar-Peralta's S-box, Karatsuba).
* The **same primitive under several cost models** is the zk.golf trick for keeping a task alive; svGolf's
  analogue is one spec scored in area/depth (combinational), then in flops plus period (pipelined), then
  iterated (sequential core) with the same `Spec`: the Keccak round is the model case.
* **Soundness plus completeness** has an svGolf counterpart in `Terminates2` plus `Computes`; the one place the
  statement is weaker is partial specifications (don't-care outputs), which need a relational task class.
* zk.golf proves its cost; svGolf measures it with a pinned flow. The price is the post-synthesis check, which
  covers the proof-versus-netlist gap that zk.golf closes by construction.

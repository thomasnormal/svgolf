# `add`: simulation validation (untrusted tooling)

Nothing here is part of the trusted base or the `lake build`; it is the
evidence that the task's designs do in a simulator what the statement says,
and that ls-sv reads them the way a simulator does.

## `validate.py`: Verilator vs ls-sv `run2` vs arithmetic

```bash
python3.12 tests/add/validate/validate.py [--quick] [--lean-wrap CMD]
```

For each design (the reference `tasks/add/reference/add_n.sv`, the baselines
in `tests/add/baselines/` (Sklansky, Kogge-Stone and the banned
comparison-carry adder `cmp_carry.sv`), Yosys's own `+` baseline `tests/add/negative/plus.sv`,
and the four functional negatives), at each width `N`:

1. the source gate's canonical text is extracted by the pinned lean-surfaces
   extractor, through svGolf's one extraction path `check/envelope.py` (as
   `check.py` does);
2. Verilator simulates the design on every vector (one C++ model per width,
   built and driven by `check/postsynth.py`'s harness: all vectors in, one row
   per vector out; Verilator is 2-state, so an `x` output is not visible
   here, the checker's static rules and `postsynth` stage are the x/z defence);
3. `Run.lean` (`lake env lean --run`) loads the envelope at run time,
   instantiates `PDesign.instantiateGD2 [N]` (exactly `name.sem N`) and runs
   one `run2` cycle per vector under both schedules `σ_src` and `σ_rev`
   (`load_design_sv2`'s load-time gates, the cross-checks, are not replayed
   here: `check.py` runs them);
4. the expected outputs are `s = (a + b + cin) mod 2^N`,
   `cout = (a + b + cin) div 2^N` in Python integers.

Vectors: every input combination for `N = 1..5` (`2^(2N+1)`: 8 to 2048), and
for `N = 6, 7, 8, 13, 16, 31, 32, 33, 64` the corner cases (all zeros, all
ones, a full carry ripple, alternating bits, every single bit, the top bit)
plus 300 random vectors (fixed seed 20261028). `--quick` runs `N = 1, 2, 3`
exhaustively and `N = 16, 64` with 50 random vectors. A full run takes
about an hour (before 10/29, with Icarus: an hour as well), almost all of it
the interpreted `run2` on the prefix adders at `N = 64` (a few seconds per
vector each); Verilator's share is the C++ build, about 2 s per design and
width.

Verdicts: a correct design must match the expected outputs in Verilator, in
`run2/σ_src` and in `run2/σ_rev` on every vector. A functional negative must
be CAUGHT (Verilator and `run2` both disagree with the expected outputs on at
least one vector) and Verilator and `run2` must agree with each other on every
vector. Exit status 0 iff all verdicts hold.

The last full run is `tests/add/results/validate.log`, HISTORICAL: it was made
with Icarus 12 (hence its `icarus_bad` keys) and before `cmp_carry.sv` joined
the list (it was then validated in Icarus alone): all eight designs, 5737
vectors each; the three adders and the `+` baseline match the arithmetic in
Icarus and in `run2` under both schedules on every vector; the four functional
negatives are caught (1405 to 4984 wrong vectors each) by Icarus and `run2`
alike, and Icarus and `run2` agree on every vector of every design. The
Verilator version of the script has run its quick plan only (`--widths
1,2,3,8,16 --samples 20`, 254 vectors per design): all five correct designs
match, the four negatives are caught (64 to 166 wrong vectors each).

`--verilator-only` (was `--icarus-only`) skips ls-sv (no Lean) for random
samples at other widths, e.g. `--verilator-only --widths 9,10,24 --samples
2000`; `verilator.py` is the tool for big samples.

`tests/run.py` runs a quick plan every time (`--widths 1,2,3,8,16 --samples
20`: every design, 254 vectors each, about 1.5 minutes of Verilator builds plus
the Lean run; `cmp_carry.sv` included, and it matches in Verilator and in
`run2`), and this full plan with `--full`.

## `verilator.py`: bulk and exhaustive runs

```bash
python3.12 tests/add/validate/verilator.py [--widths 5,16,33,64] [--vectors 200000]
```

Verilator 5.042 builds each of the three adders (the reference and the two
prefix baselines) at each width and a C++ testbench
compares `s`, `cout` with `a + b + cin` in 128-bit integers on a fixed-seed
random stream plus all-ones corner cases; `--exhaustive` enumerates every
input combination instead (widths up to 12). `validate.py` now uses Verilator
too, so this script is no longer a "second simulator"; what it adds is the
vector count (the arithmetic is checked in C++), not independence. `tests/add/results/verilator.log`
holds the last five runs, all without a mismatch: the three adders at
`N = 5, 16, 33, 64` with 200000 random vectors each, at
`N = 1, 2, 3, 7, 8, 31, 63` with 100000 each, EXHAUSTIVELY at `N = 1..12`
(up to 2^25 vectors; two runs, `1..10` and `11, 12`), and at EVERY width
`N = 1..64` with 100000 random vectors each.

## `postsynth.py`: the scored netlist computes the adder

```bash
python3.12 tests/add/validate/postsynth.py [--widths 16,32,64] [--vectors 5000]
```

Each design (the reference, the two prefix baselines, the `+` baseline and
the banned `cmp_carry.sv`) is scored by exactly the pinned flow
(`score/score.py`: the two-stage canonical flow, from the source gate's
canonical text), which writes the scored gate netlist, and Verilator simulates
THAT netlist (with Yosys's `simcells.v`, through the harness of
`check/postsynth.py`) against `a + b + cin`. The
checker's `postsynth` stage compares the scored netlist with ls-sv's reading
of the design; this script compares it with the task's function, and runs on
the unproved baselines too. Last full run (`tests/add/results/postsynth.log`,
under the old one-process flow, which wrote the netlist with expressions):
all five designs at `N = 16, 32, 64`, 5005 vectors each, no mismatch.
`tests/run.py` runs it every time at `N = 16, 32` with 500 vectors (seconds).

## Scores

Every design's score at `N = 16, 32, 64` (gate mix, area in exact milli-GE,
depth) is in `tests/expected.json`, and `tests/run.py` re-measures each with
the pinned flow (`score/score.py`, source gate included).

## `tests/add/baselines/cmp_carry.sv`: Yosys's adder through comparisons (banned)

Not a reference and not a negative: an adder whose every carry is a run-time
comparison (`c[i] = (a[i-1:0] > ~b[i-1:0]) | ((a[i-1:0] == ~b[i-1:0]) & cin)`).
Yosys's `alumacc` builds each comparison through an `$alu`, i.e. its own
carry logic, and the pinned flow scores it at 195.975 GE, depth 17
(`N = 16`), lower depth than every proved design. It was the policy probe of
the question "should a comparison count as the banned operator in an adder
task?", and the answer (decided 2026-11-05) is yes, at the Yosys level: in a
task that bans `+` or `-`, the banlist's backstop runs `alumacc` after
`proc; opt` and rejects every `$alu` it builds, i.e. every run-time ordering
comparison (`score/banlist.py`; equality and comparisons Yosys folds as
constants stay allowed). So it is now a BANNED baseline, scored with the
banlist lifted like `tests/add/negative/plus.sv` (`tests/expected.json`
`"banned": true`; `tests/run.py` checks that the banlist rejects it, at its
comparison's line). The extractor accepts it; it is correct in Verilator and
in ls-sv's `run2` (`validate.py`'s quick plan: exhaustive `N <= 3`, sampled
`N = 8, 16`) and has no proof.

## The dead-clock negatives: where ls-sv and the simulators disagree

`tests/add/negative/dead_clock.sv` and `dead_clock_tied.sv` register a correct
sum with `always_ff @(posedge clk)` on a clock nothing drives, or one tied to
`1'b0`. They are NOT in `validate.py`, because they are not functionally
wrong under ls-sv: `run2` runs every `always_ff` once per cycle whatever its
clock holds, so its snapshots carry the right `{cout, s}` (a reviewer's
multi-cycle `run2` check: 0 mismatches, exhaustive at `N = 1..4` and 200
vectors at `N = 16`, under `σ_src` and `σ_rev`). An event-driven simulator
disagrees (Icarus 12, measured 10/28, `N = 4`: `a = 9, b = 8, cin = 1` gives
`s = xxxx`, `cout = x` for both; Verilator, being 2-state, gives `s = 0000`,
`cout = 0`, measured 10/29), and the pinned flow scores both at 0.0 GE,
depth 0 (Yosys removes the never-clocked flip-flops and drives the outputs
with `x`). The statement rejects them by its "no clocked process"
requirement, not by any run (`tests/add/negative/Refute.lean`).

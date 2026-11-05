# `add`: designs that must be rejected

Each design here tries one way to look like an adder without meeting the
statement. Every Lean-level case is REFUTED in `Refute.lean` (built by
`lake build`): a kernel-checked proof of
`¬ SvGolf.Tasks.Add.Statement <design>.sem`, standard axioms only, at the
smallest width `N = 1`.

| design | what it tries | how it fails | refutation | checker stage |
|---|---|---|---|---|
| `no_cin.sv` | a ripple adder that ignores the carry in (`c[0] = 1'b0`) | at `N = 1`, `a = 0`, `b = 0`, `cin = 1`: the snapshot has `s = 0`, the task says 1 | `noCin_refuted` (one concrete run) | `solution` |
| `cout_off.sv` | an off-by-one carry out, `cout = c[N-1]` (the carry INTO the top bit) | at `N = 1`, `a = b = 1`, `cin = 0`: `cout = c[0] = 0`, the task says 1 | `coutOff_refuted` (one concrete run) | `solution` |
| `carry_bug.sv` | a wrong carry gate, `(a & b) \| (c & a)` instead of the majority | at `N = 1`, `a = 0`, `b = 1`, `cin = 1`: `cout = 0`, the task says 1 | `carryBug_refuted` (one concrete run) | `solution` |
| `only_n16.sv` | correct at the scoring point only: `generate if (N == 16)` the ripple adder, else a carry-free `s = a ^ b`, `cout = 0` | it simulates and scores like the reference at `N = 16`, but the statement covers every `N ≥ 1`: at `N = 1`, `a = b = 0`, `cin = 1` it gives `s = 0` | `onlyN16_refuted` (one concrete run) | `solution` |
| `wide_s.sv` | one `(N+1)`-bit output `s = {cout, sum}` and no `cout` port (right bits, other interface) | the interface conjunct pins the outputs to `s` (`N` bits) and `cout` (1 bit) | `wideS_refuted` | `solution` |
| `cin_name.sv` | the carry in named `ci` (a correct adder under its own name) | the interface conjunct pins the input names; the statement's stimulus drives `cin` | `cinName_refuted` | `solution` |
| `dead_clock.sv` | a correct ripple adder into internal `sc`/`c`, outputs registered by `always_ff @(posedge clk) begin s <= sc; cout <= c[N]; end` on a `clk` nothing drives | ls-sv runs every `always_ff` once per cycle whatever its clock holds, so every ls-sv snapshot holds the right sum and `Computes` HOLDS; every simulator and Yosys see a clock that never rises (`x` outputs; `score.py` gives 0.0 GE, depth 0, no gates). The statement's `Unclocked` conjunct rejects any clocked process | none since WP-Q0: the loader refuses the clock (`Clock:source`) and Yosys `check` refuses it first | `fourstate` |
| `dead_clock_tied.sv` | the same with `assign clk = 1'b0` | as `dead_clock.sv` (0.0 GE, depth 0) | none since WP-Q0: the loader refuses a clock that is not an input port (`Clock:source`) | `design` |
| `plus.sv` | the right function through banned run-time `+`: Yosys's own `assign {cout, s} = a + b + cin;` | banned run-time `+` (`score/banlist.py`, before Lean) | none: it computes the task's function (`tests/add/validate/` checks it in Verilator and in ls-sv's `run2`); the banlist is what rejects it | `banlist` |

`only_n16.sv` is the reason the statement covers every `N`: at the scoring
point it scores exactly like the reference (112.0 GE, depth 33, 48 NAND +
32 XOR), and it passes the banlist and simulation there; at `N = 8` it is 8
XOR gates (16.0 GE, depth 1; both scores are in `tests/expected.json`). Only the for-all-`N` statement tells them apart.

`plus.sv` doubles as the task's baseline: scored with the banlist lifted it is
117.994 GE, depth 33 at `N = 16` (a `baselines` entry of `tests/expected.json`,
with `N = 32, 64`), which the ripple reference beats on area.

`tests/expected.json` lists these under the task's `negatives` with the
checker stage each must fail at; `tests/run.py` runs `check.py` on them with
the reference proof `tasks/add/reference/add_n.lean`. The reference proof does not prove the statement for a different
design, so the Lean-level cases fail at the `solution` stage; the
refutations above show that NO proof could succeed. The four functional
negatives are also caught by simulation: `tests/add/validate/validate.py` runs them in
Verilator and in ls-sv's `run2` and requires both to disagree with
`a + b + cin` somewhere, and to agree with each other everywhere.

The two dead-clock designs are the only negatives here that ls-sv's `run2`
gets RIGHT: they are not caught by any run, only by the statement's
requirement that no process is clocked (`SvGolf/Task.lean`, conjunct 2), which
the reference meets for free (`satisfiedAt_of_comb` derives it from the comb
profile). They pass the source gate, the extraction with its probe
cross-check, the banlist and ls-sv's loader; without that requirement a
for-all-`N` proof about them would have scored 0 GE.

## How the refutations work

`decide +kernel` gets stuck on `PDesign.instantiate2` itself (measured:
`(design.sem 1).processes.size = 4` does not reduce), so each functional
negative is first instantiated at
`N = 1` symbolically, by the reference proof's route
(`semAt1_eq`: `PDesign.instantiate2_of_ok` with `simp` on the stages; the
generate loop through `GenItem.expand2_genFor_ascending_processes`, the
generate-if of `only_n16.sv` through `GenItem.expand2_genIf_of_eq`), and then
ONE run of the resulting small `Design2` is evaluated by `decide +kernel`
(`CombTask.not_computes_of_counterexample`). The interface cases need only
the declaration stage: `decls_or_nil` shows the instantiated declarations
are the declaration stage's, or empty if instantiation failed, and neither
matches the task's ports. The dead-clock cases need no instantiation at all:
`not_satisfiedAt_of_clocked` shows that an envelope with a top-level
`always_ff` (or `always @(posedge …)`, or async-reset) process template fails
every combinational task at every parameter point, because a successful
instantiation lowers the template to an edge-phase process (the one-driver
guard only appends a loud process), and a failed one is the loud error
design, which never completes a run (`errorDesign_not_terminates`). The
template's presence is decided by `decide` on the envelope's process list.

## Loading the designs

`Refute.lean` loads each design with `load_sv` (`SvGolf/LoadSv.lean`), which
extracts it at elaboration time through `check/envelope.py` (the source gate,
then the pinned extractor with the task's probe points, exactly as `check.py`
does) into the cache `.lake/envelopes/`; no envelope is committed. `lake
build` re-elaborates `Refute.lean` when a design changes. To look at an
envelope by hand (from the repository's root):

```bash
python3.12 check/envelope.py tests/add/negative/no_cin.sv   # prints the cached envelope's path
```

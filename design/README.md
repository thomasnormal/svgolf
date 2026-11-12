# design/: the working notes

This folder holds the maintainers' working notes from svGolf's development: design studies, spikes,
measurements and reduced probes, each dated. It is history, not maintained, and not part of the competition:
the rules are README.md's, the trusted statements are the `Spec.lean` files and `SvGolf/`, and a note here
that disagrees with them is out of date. Where code, a statement or a test cites a note by its path (for
example `design/soundness/TXTASK-V2-REVIEW.md`, `design/sequential/CONTRACT.md`, `design/ppa/sky130.md`), the
note stays at that path.

Three probes of the development tree that state `sorry` (in `real-world-sv/proc/lowered/` and
`word-level/spike/`) are left out of the public repository; the notes that describe them keep their text.
Some notes name paths of the working directory of the time; they are provenance only.

| folder | what it holds |
|---|---|
| `always-comb/` | the `always_comb` fragment of the tactics: spikes and notes G20 to G25 |
| `architecture/` | the architecture study: semantics authority, views, the execution plan and its measurements |
| `bv-decide/` | allowing `bv_decide` in submissions: the study, dormant since 2026-11-01 |
| `exh/` | an exhaustive proof of the S-box netlist (`sbox_bp_exh.lean`) and its drafts |
| `fdiv-param/` | the parametric IEEE 754 divider: the format, the certificates, the probes |
| `hierarchy/` | module instances in the tactics |
| `loop/` | procedural loops: the loop note and its measurements |
| `nondeterminism/` | how LRM-legal nondeterminism would be modelled |
| `ppa/` | the sky130 study behind the score (`sky130.md`) and its spike |
| `reactive/` | the reactive controller tasks (the arbiter) |
| `real-world-sv/` | the survey of how SystemVerilog is written in the wild, with its reduced probes |
| `sequential/` | the clocked statements' contract, sketches and the counter's cycle models |
| `soundness/` | the review of the second clocked statement |
| `tasks-week2/` | the study of task candidates beyond the first combinational tasks |
| `word-level/` | word-level operators in the tactics: notes B2 and G26 and the spike |
| `ideal_*.lean` | the mathematics an ideal `add` or `mul` proof is left with, in plain Lean |

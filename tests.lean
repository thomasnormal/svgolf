/-
The `tests` library: the kernel-checked refutations of every task's negative
designs (`tests/<name>/negative/Refute.lean`), the non-vacuity evidence for
the task statements. Add a task's refutations here.

Each refutation loads its designs with `load_sv` (`SvGolf/LoadSv.lean`), which
extracts them at elaboration time; the library `needs` the `.sv` files and the
extraction scripts (`lakefile.toml`), so changing a design re-elaborates it.
`tests/run.py` runs everything else (references, negatives, baselines and
attacks through `check.py`, scores, simulation).

Not imported here, so not in the default `lake build`: the refutations of
`add`, `mul` and `clmul` (`tests.add.negative.Refute`, `tests.mul.negative.Refute`,
`tests.clmul.negative.Refute`). They do not build at the pinned library yet: the
pinned ls-sv's loader refuses their `only_n16.sv` (`PDesign.int32Agrees`), so they do
not build at the pin. They are unchanged, and `tests/run.py`'s `negatives` step
still builds each one and pins its known failure (`PENDING_REFUTES`); once one
builds, that step fails until it is imported here again.
-/
import tests._example.negative.Refute
import tests.fdivp.negative.Refute
import tests.arbiter.negative.Refute
-- kernel refutations of a sample of the arbiter reference's generated mutants (tests/mutate.py)
import tests.arbiter.negative.Mutants
-- the sorter's and matmul's attacks and a sample of their references' generated mutants, refuted for every latency
-- function (tests/txsweep.py's sweep, 2026-11-08)
import tests.sorter.negative.Refute
import tests.sorter.negative.Mutants
import tests.matmul.negative.Refute
import tests.matmul.negative.Mutants
-- the clocked checker's fixture task statement (PLAN4 Gate 2; check.py builds it too)
import tests.seq_counter.Spec
-- its txtask-v2 refutations (the soundness probe's H1 and F1 twins, hand-built)
import tests.seq_counter.negative.Refute
-- txtask-v2's acceptance table (the maintainers' fixtures 0 to 11, round 1's W1 to W4, the attack on
-- revision 2's fixtures 12 to 16, hand-built)
import tests.seq_counter.negative.Table
-- the clocked lemmas of `SvGolf.Clocked`, each at two sizes
import tests.clocked.Lemmas

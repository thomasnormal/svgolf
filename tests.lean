/-
The `tests` library: the kernel-checked refutations of every task's negative
designs (`tests/<name>/negative/Refute.lean`), the non-vacuity evidence for
the task statements. Add a task's refutations here.

Each refutation loads its designs with `load_sv` (`SvGolf/LoadSv.lean`), which
extracts them at elaboration time; the library `needs` the `.sv` files and the
extraction scripts (`lakefile.toml`), so changing a design re-elaborates it.
`tests/run.py` runs everything else (references, negatives, baselines and
attacks through `check.py`, scores, simulation).
-/
import tests._example.negative.Refute
import tests.add.negative.Refute
import tests.mul.negative.Refute
import tests.fdivp.negative.Refute
import tests.clmul.negative.Refute
-- the clocked checker's fixture task statement (PLAN4 Gate 2; check.py builds it too)
import tests.seq_counter.Spec

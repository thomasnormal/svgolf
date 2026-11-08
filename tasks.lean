/-
The `tasks` library: every task's TRUSTED statement (`tasks/<name>/Spec.lean`).
Add a task by adding its `Spec` module here. A task ships no proof library:
reusable proof code goes to `LeanModels/Sv/Lib`, the rest into the task's
reference proof.

Reference solutions are not in this library: `tests/run.py` checks them with
`check.py`, exactly as submissions are checked. The refutations of the
negative designs are the `tests` library (`tests.lean`).

Each task's `Properties.lean` (imported last) is NOT trusted: it names the
parts of the statement, one definition per property a design must satisfy,
and proves `statement_iff_properties` (the statement holds exactly when every
property does), which the kernel checks. The site shows one card per property
(`tasks/<name>/properties.json`).
-/
import tasks._example.Spec
import tasks.add.Spec
import tasks.mul.Spec
import tasks.fdivp.Spec
-- the sequential tasks (txtask-v2 statements, `TxTask.StatementV2`, `StreamTask.StatementV2`): matmul and sorter (ready, references proved)
import tasks.matmul.Spec
import tasks.sorter.Spec
import tasks.aes_sbox.Spec
import tasks.clmul.Spec
-- the reactive tasks (ReactTask, SvGolf/TaskReact.lean, 2026-11-05; txtask-v2's rules 2026-11-06; final trusted text, decided 2026-11-07): the arbiter (ready, reference proved)
import tasks.arbiter.Spec
-- the statements as named properties (proved, not trusted)
import tasks._example.Properties
import tasks.add.Properties
import tasks.mul.Properties
import tasks.fdivp.Properties
import tasks.matmul.Properties
import tasks.sorter.Properties
import tasks.aes_sbox.Properties
import tasks.clmul.Properties

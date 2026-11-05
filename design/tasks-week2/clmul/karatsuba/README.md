# clmul: one level of Karatsuba for every N (WP-T-CLMUL, gate 3: NOT a reference, the proof is unfinished)

Scratch material of the stretch gate, kept because its measurements are the finding (`tasks/clmul/README.md`, "Beyond the reference").
None of it is in a Lake library or under `tasks/`; the checker never reads it.

| file | what |
|---|---|
| `clmul_k1u.sv` | the design, 19 sites: padded operand vectors `ap`, `bp` (2H+1 bits, written by two generate families each), three H x H arrays, combination families, output. Correct for every N (Verilator), 651.950 GE depth 7 at N = 16, 2556.137 / 8 at 32, 167.320 / 6 at 8 |
| `clmul_k1v.sv` | the same function with ONE operand vector `abz = {1'b0, b, 1'b0, a}` (16 sites): same netlist, same scores |
| `Karatsuba.lean` | the plain-Lean arithmetic (`import tasks.clmul.Spec`; compiles): the XOR-sum `bx`, the Spec's double sum as `cl`, the row invariant of the array (`view_spec`, as in `reference/clmul_n.lean`), the Karatsuba identity over coefficient functions (`karatsuba`, `cl_sum`, `karatsuba_full`), `comb_spec`, `cl_congr`, `cl_trunc` |
| `G3h.lean` | the proof of `clmul_k1u.sv` against the staged `Submission.Design`: structure (`kKey`, `k_struct`), interface, the `sv_bridge` fields of the three arrays, the combination equations, the whole chain to the Spec. It compiles EXCEPT the coverage goals `cover_3` to `cover_17`, which `sv_cover` cannot close (the last line is the standard closer; it fails there) |

Measured (2026-11-01, `lake env lean -DElab.async=false`, one shared machine): `k_struct` about 60 s of CPU at 19 sites (110 s at the first 27-site
version); the rest of `solution` about 30 s; every `sv_bridge` field closed first time. The coverage goals come out of `sv_equations` in the
site-witness form `∃ b, (b = site₀ ∨ … ) ∧ Q b` whenever the design is larger than about 40 reads of the operand vector (variants: 13 and 16
sites with fewer reads come out explicit and are handled by the 2-D rule), and `sv_cover`'s site route fails on a bit covered by several
writer families and on this localparam design. See the README of the task for the proposed tool changes.

**Update (2026-11-01, WP-COV): `G3h.lean` now compiles WHOLE** (about 62 s of CPU, `lake env lean` against the staged
`clmul_k1u.sv`, standard axioms only), the last line `all_goals first | (intros; omega) | sv_cover` unchanged. The coverage goals
were not left in the site-witness form because the design is large: the whole coverage obligation is normalized by ONE
`sv_simp` call that ran out of `simp` steps (the form depends on reads times sites of the WHOLE obligation, which is why 13 and 16
sites with 20 reads came out explicit); `sv_equations` now renormalizes such a goal on its own (`sv_cover_renorm`), and the
explicit form is closed by the 2-D rule of `sv_cover`. `G25-NOTE.md` section 13 has the diagnosis. To stage the design for a
proof file: `check.py tasks/clmul <this directory>/clmul_k1u.sv --unproved --keep --stage-dir DIR` (the staged
`Submission.Design` is `DIR/build`; at this tip `tasks/clmul/task.json` still sets `allow_bv_decide: true`, which `check.py`
now refuses as an infrastructure error, so clear it in a scratch copy to stage).


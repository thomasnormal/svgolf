# `tests/fdivp/unproved/`: test material without a proof

Every design the site shows has a kernel-checked proof (decided 2026-11-12), so the designs here are on no page,
chart, table or data file of the site. They stay in the repository as test material: `tests/run.py` simulates them
(`validate`, tests/fdivp/validate/validate.py).

- `fdivp_d1.sv`: D1, the natural parametric form (`$clog2`, `2**`, replication, sized localparams, a logarithmic
  normalizer and shifter). ls-sv does not run it yet (its sized localparams' constant-expression conversions load as
  an unsupported node), so no proof about it can be written today.
- `flat_binary16.sv`: the flat binary16 netlist of the former 16-bit task under the parametric header. It is right at
  (W, P) = (5, 11) ONLY (every width inside is a literal 16-bit one), so no proof of the parametric statement can
  exist for it.

Their measured numbers are history in `tasks/fdivp/README.md`.

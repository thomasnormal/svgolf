# Validation of task `aes_sbox`

`validate.py` (a few seconds; `python3.12 tests/aes_sbox/validate/validate.py --help`, its docstring lists the
steps) cross-checks the oracle against the standard and simulates every design on ALL 256 inputs:

* `vectors.json`: the 256-entry table parsed from Table 4 of FIPS 197 (2023 edition) in the NIST PDF
  (<https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf>, fetched 2026-10-30, sha256
  `62c86eb567f13edb8f71826e985da870b04ef6381634f303cdb16e84d47becd1`), the worked values, the AES-128
  example of FIPS 197 (2001) Appendix C.1. (WP-A1 re-parsed the PDF with `pdftotext -layout` and got the same
  256 bytes.)
* `SLP_AES_113.txt` (sha256 `de1d21c85eaa1e4146f24b59a4f8bae515757f2a7d0011527841ebb5518b55c0`) and
  `SLP_AES_125_depth16.txt` (the page's `AESDEPTH16SIZE125`, sha256
  `b72f635d5a58e06b44d4040b95901da27418ec5a037f9123392155e96966f162`): the Boyar-Peralta straight-line
  programs of <https://www.cs.yale.edu/homes/peralta/CircuitStuff/> (fetched 2026-10-30; re-fetched and equal
  2026-11-04); the `.sv` translations are checked against them gate for gate. The page states no licence, so the
  files are NOT committed: the `bp` step downloads each from its pinned URL (`NETLISTS` in `validate.py`), verifies
  the sha256 above before anything is written, and caches it here under the name above (gitignored). Offline and
  without a cached copy, the step is skipped and says so.

`gen_bp_proof.py` and `sbox_bp.lean.tmpl` generate the reference proof `tasks/aes_sbox/reference/sbox_bp.lean`
from the netlist (`--check`: exit 1 unless the committed file is what the generator writes; `tests/run.py`
runs it in the `layout` step). The template is the Lean text with `@@PLACEHOLDERS@@` for the tables: the gate
list, the net each environment index stands for, the rank, the 113 projections out of `sv_equations`'s `key`
and the 221 coverage witnesses.

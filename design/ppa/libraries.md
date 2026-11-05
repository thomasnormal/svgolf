# Open cell libraries for svGolf's cost models

What the scorer needs from a library: per-cell **area** (the unit of the score), **pin capacitances** and
**NLDM delay/transition tables** (weighted delay), **internal-power tables and leakage** (energy), a
**boolean function** per output (so a Python simulator needs no hand-written cell models), and, for the
physical flow only, LEF/tech files and an RC (RCX) rule file. All of it in a form a script can fetch at a
pinned hash. Sizes are from the GitHub contents API of OpenROAD-flow-scripts (ORFS) on 10/30 unless noted.

## Comparison

| | Nangate45 (FreePDK45) | ASAP7 | Sky130 `sky130_fd_sc_hd` | GF180MCU | IHP SG13G2 |
|---|---|---|---|---|---|
| node, kind | 45 nm planar, **predictive** (never fabbed) | 7 nm FinFET, **predictive** (ASU/ARM) | 130 nm, real (SkyWater MPW) | 180 nm, real (GF MPW) | 130 nm SiGe BiCMOS, real (IHP MPW) |
| licence | Apache-2.0 for the ORFS platform directory (`LICENSE`, 10 kB); the liberty file's own header still carries Nangate's 2011 "License Agreement containing restrictions on its use" notice; Si2/Silvaco reportedly relicensed the library as Apache-2.0, the NCSU kit itself is Apache-2.0 (since v1.2). **Unclear for redistribution: fetch, do not vendor** | BSD-3-Clause (GitHub licence field of the ASAP7 PDK and cell-library repos) | Apache-2.0 | Apache-2.0 | Apache-2.0 |
| liberty, pinned fetch | one file, `NangateOpenCellLibrary_typical.lib`, **6.7 MB**, 135 cell groups (X1 to X32 drive strengths, flops, latches, fillers); blob `90e4afb274`, sha256 `8d540a4d...` (pinned in `spike/fetch_lib.py`, commit `6c6fc7e2`) | split by cell family and corner: for RVT/TT: AO 4.2 MB.gz, OA 3.8 MB.gz, INVBUF 69 kB.gz, SIMPLE about 0.45 MB.gz, SEQ 1.5 MB: **about 10 MB in 5 files**, three Vt flavours + SRAM Vt, FF/SS/TT | `sky130_fd_sc_hd__tt_025C_1v80.lib` **12.8 MB** (ORFS copy); other variants are much larger (`hs` TT: 72 MB) | per corner and track height, 3 MB gz each, **90 MB** for all in ORFS | per corner, **1.7 MB** each (13 MB all) |
| area unit and GE | um^2; `NAND2_X1` = 0.798. **`score/ge.json` is exactly this library's X1 area ratios** (below) | um^2 (cells are tiny, a few hundredths of a um^2); GE ratios against its NAND2 not measured (library not downloaded) | um^2; `inv_1` and `nand2_1` have the **same area** (recalled, unverified), so `NOT` would be 1.0 GE instead of 0.667: a new GE table, every score changes | um^2, much larger cells | um^2 |
| accuracy | typical corner only, 2011-vintage characterisation (Nanspice); fine for ranking designs, poor in absolute terms (nothing fabbed); has `internal_power` and `when`-conditional leakage | modern-node predictive; high accuracy of trends, many Vt flavours complicate the choice | silicon-validated models; slow (ns-scale delays) so wire delay matters less | silicon-validated, 5 V / 3.3 V options | silicon-validated |
| physical flow | ORFS platform complete (LEF, tech, `rcx_patterns.rules` 134 kB, GDS, magic tech, tapcell, PDN) and the best-trodden one | ORFS platform complete, more config (`DONT_USE`, Vt choice) | ORFS platform complete | ORFS platform complete, heavy | ORFS platform complete |
| fit for svGolf | **best fit for the scorer**: small, one file, one corner, area ratios already ours | good for a "modern" physical track later | good for a "realistic silicon" physical track | no | no |

**Tiny educational libraries.** ABC's repository ships none in a form usable here (its `lib/` has only headers);
Yosys' own `cells.lib` on this machine holds flip-flops only. Two options exist and neither needs another
download: (a) **a generated 9-cell subset of Nangate45** (`spike/mklib8.py`: INV, BUF, NAND2, NOR2, AND2, OR2,
XOR2, XNOR2, MUX2, all X1, 136 kB, cut byte for byte out of the pinned file, same gate kinds as today's
`abc -g -> GE` flow minus ANDNOT/ORNOT); (b) a hand-written genlib with unit delays, which is what `abc -g`
already uses internally and adds nothing. (a) is a derived artifact of the parent library and inherits its licence
question, so it is generated, not committed.

## Can `ge.json` be derived from the library? Yes, for 8 of 11 types (measured)

`spike/derive_ge.py` (NAND2_X1 = 0.798 um^2 = 1 GE):

| Yosys gate | Nangate45 cell(s) | um^2 | derived GE | `ge.json` |
|---|---|--:|--:|--:|
| NOT | INV_X1 | 0.532 | 0.6667 | 0.667 |
| NAND, NOR | NAND2_X1, NOR2_X1 | 0.798 | 1.0000 | 1.000 |
| AND, OR | AND2_X1, OR2_X1 | 1.064 | 1.3333 | 1.333 |
| XOR, XNOR | XOR2_X1, XNOR2_X1 | 1.596 | 2.0000 | 2.000 |
| MUX | MUX2_X1 | 1.862 | 2.3333 | 2.333 |
| ANDNOT, ORNOT | no cell; INV_X1 + NOR2_X1 (resp. NAND2_X1) | 1.330 | **1.6667** | **1.333** |
| BUF | BUF_X1 | 0.798 | 1.0000 | 0.000 |

So the present score *is* a Nangate45 X1 area score, except that `ANDNOT`/`ORNOT` are priced as an `AND2`
(1.333 GE) although the library has no such cell: the cheapest realisation costs 1.667 GE. Over the 12 designs
measured in the spike, the Nangate45-priced area (with those two gates expanded to INV + NOR2/NAND2) differs from
the GE score by 0.0% to +1.2% (`spike/README.md`), and those gates carry the whole difference. Consequence for
the plan: **the library-priced area and the old score can be made to agree** by (1) adopting Nangate45 as the
cell library, (2) deriving `ge.json` from it by a script with a test (the table above), and (3) deciding the
ANDNOT/ORNOT question once: either keep the table as is and say so ("ANDNOT and ORNOT are priced as one AND2
cell; the library realisation costs 0.33 GE more"), or reprice them at 1.667 GE (a new flow hash, all records
re-issued; the leaderboard policy already handles that). `BUF = 0` is harmless as long as `abc -g` never emits
a buffer (it does not in the 12 netlists).

If the library ever changes (ASAP7, Sky130), GE is *defined* by that library's NAND2 and the table is
re-derived; scores are then comparable only within a library, which the record already encodes by the
liberty sha256 (to be added to the record, see `flows.md`).

## Recommendation

**Nangate45 typical (pinned ORFS commit, sha256 in the record)** for flows A and B and for the physical flow D
as the first target: it is the library the existing GE table already is, the smallest to fetch, one corner,
and the one with the most complete open physical platform. Add **ASAP7 or Sky130 as a later, separate
"technology" column or contest** only when somebody wants absolute-looking numbers; a second library multiplies
every record by two and doubles the pinning surface.

Caveats to state in the README when the column ships: Nangate45 is predictive and old, so delays are
"45 nm-like" and the ranking, not the absolute picosecond, is the product; the library carries a Nangate
header whose licence status should be settled with ORFS/Si2 before the file is mirrored anywhere (the plan
fetches it from ORFS at a pinned commit and never copies it into the repository).

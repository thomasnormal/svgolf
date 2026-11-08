Compute the bitwise AND of two `N`-bit inputs, `y = a & b`, combinationally, and prove it for every
`N ≥ 1`.

The optimum is obvious: one AND gate per bit, {{band.area}} with a {{band.time}} critical path on sky130
for `N = 16` ({{band.ge}}, depth {{band.depth}}). The task exists to run
the whole pipeline (statement, proof, checker, banlist, scoring) on a design small enough to read in one
sitting, and to be the template for real tasks. Its reference proofs are complete for every width:
`band_tactics` with the `sv_comb` tactics, the route of the real tasks and the proof the walk-through starts
from, and `band` by hand, walking the design's structure symbolically. The run-time operators `+ - * / % **` are banned only to exercise
the banlist.

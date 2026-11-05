Compute the bitwise AND of two `N`-bit inputs, `y = a & b`, combinationally, and prove it for every
`N ≥ 1`.

The optimum is obvious: one AND gate per bit, 100.1 µm² with a 0.28 ns critical path on sky130 for
`N = 16` (21.328 GE, depth 1). The task exists to run
the whole pipeline (statement, proof, checker, banlist, scoring) on a design small enough to read in one
sitting, and to be the template for real tasks. Its reference proof is complete and walks the design's
structure symbolically for every width. The run-time operators `+ - * / % **` are banned only to exercise
the banlist.

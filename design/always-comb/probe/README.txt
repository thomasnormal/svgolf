WP-G Gate 1 four-state probe (2026-10-30).
  python3 gen.py      -> probe.sv, probe.json   (23 DUTs, 386 cycles: procedural if, ?:, !/~, order, carry cell)
  python3 gen2.py     -> probe2.sv, probe2.json (5 DUTs, 79 cycles: block-local temp, per-bit latch, context)
  probe3.sv           the 3-bit carry chain of always_comb blocks (r3)
  Xcelium 24.03-s004:  xrun -sv -q -timescale 1ns/1ns -xmlibdirname xcelium.d <file>.sv
  xrun1.out xrun2.out xrun3.out   the raw outputs (r1, r2, r3)
  python3 model.py xrun1.out      compares every cycle with the Python transcription of the ls-sv rules
                                  (LeanModels/Sv/Basic.lean: condTrue, isKnownZero, ternary merge, lnot, bnot):
                                  386 rows, 0 mismatches; xrun2.out: 79 rows, 0 mismatches.
The Lean model is NOT run in Gate 1; the staged rows (../rows) are its Gate 2 comparison against the same simulator.

#!/usr/bin/env python3.12
"""WS3: the six `always_comb` blocks of ibex_alu that today's route refuses (X7 B.3), each wrapped as its own
module, from the output of WS4's slicer (`svgolf/design/architecture/measure/x7_slice.py`, branch arch-measure).

    python3.12 -I x7_blocks.py --slice SLICEDIR/ibex_alu@rv32bnone/ibex_alu.sv --out OUTDIR

The slice is checked against the sha256 X7.md B.2 records (`ibex_alu@rv32bnone`, cd9b491d...); a mismatch stops the
run. Each block is copied VERBATIM (from its `always_comb begin` to the first line `  end` after it); the wrapper
declares the block's reads as input ports and its writes as output ports, at the slice's declared widths. The
output is third-party code (lowRISC/ibex, Apache-2.0): it is written to OUTDIR only (scratch), never to this
repository.
"""
import argparse
import hashlib
import os

SLICE_SHA256 = "cd9b491d1c5e4398da7c369858a5f8653bf64d079d0e30591015e4ba357fb5cd"

# (name, index of the block among the slice's `always_comb begin` lines, inputs, outputs); widths as declared
BLOCKS = [
    ("adder_flags", 0, [("operator_i", 7)],
     [("adder_op_a_shift1", 1), ("adder_op_a_shift2", 1), ("adder_op_a_shift3", 1), ("adder_op_b_negate", 1)]),
    ("adder_in_a", 1, [("multdiv_sel_i", 1), ("adder_op_a_shift1", 1), ("adder_op_a_shift2", 1),
                       ("adder_op_a_shift3", 1), ("multdiv_operand_a_i", 33), ("operand_a_i", 32)],
     [("adder_in_a", 33)]),
    ("adder_in_b", 2, [("multdiv_sel_i", 1), ("adder_op_b_negate", 1), ("multdiv_operand_b_i", 33),
                       ("operand_b_neg", 33), ("operand_b_i", 32)],
     [("adder_in_b", 33)]),
    ("shifter", 7, [("shift_sbmode", 1), ("shift_left", 1), ("operand_a_rev", 32), ("operand_a_i", 32),
                    ("shift_rot", 1), ("shift_arith", 1), ("shift_amt", 5)],
     [("shift_operand", 32), ("shift_fill", 32), ("shift_result_ext", 64), ("shift_result", 32),
      ("unused_shift_result_ext", 32), ("shift_result_rev", 32)]),
    ("bwlogic", 9, [("bwlogic_or", 1), ("bwlogic_and", 1), ("bwlogic_or_result", 32), ("bwlogic_and_result", 32),
                    ("bwlogic_xor_result", 32)],
     [("bwlogic_result", 32)]),
    ("result_mux", 10, [("operator_i", 7), ("bwlogic_result", 32), ("adder_result", 32), ("shift_result", 32),
                        ("shuffle_result", 32), ("xperm_result", 32), ("cmp_result", 1), ("minmax_result", 32),
                        ("bitcnt_result", 6), ("pack_result", 32), ("sext_result", 32), ("singlebit_result", 32),
                        ("rev_result", 32), ("clmul_result", 32)],
     [("result_o", 32)]),
]


def port(direction, name, w):
    return "  %s logic %s%s" % (direction, "" if w == 1 else "[%d:0] " % (w - 1), name)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--slice", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    raw = open(a.slice, "rb").read()
    got = hashlib.sha256(raw).hexdigest()
    if got != SLICE_SHA256:
        raise SystemExit("not the recorded slice: sha256 %s, want %s" % (got, SLICE_SHA256))
    lines = raw.decode().split("\n")
    starts = [i for i, l in enumerate(lines) if l == "  always_comb begin"]
    if len(starts) != 11:
        raise SystemExit("expected 11 always_comb blocks, found %d" % len(starts))
    os.makedirs(a.out, exist_ok=True)
    for name, k, ins, outs in BLOCKS:
        s = starts[k]
        e = next(j for j in range(s + 1, len(lines)) if lines[j] == "  end")
        body = "\n".join(lines[s:e + 1])
        ports = [port("input ", n, w) for n, w in ins] + [port("output", n, w) for n, w in outs]
        text = ("// [x7-block] ibex_alu@rv32bnone (X7 slice, sha256 %s), always_comb #%d, source lines %d-%d of"
                " the slice, verbatim.\nmodule x7_%s (\n%s\n);\n%s\nendmodule\n"
                % (SLICE_SHA256[:8], k, s + 1, e + 1, name, ",\n".join(ports), body))
        open(os.path.join(a.out, name + ".sv"), "w").write(text)
        print(name, "lines %d-%d" % (s + 1, e + 1), hashlib.sha256(text.encode()).hexdigest()[:12])


if __name__ == "__main__":
    main()

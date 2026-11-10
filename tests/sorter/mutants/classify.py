#!/usr/bin/env python3.12
"""The sorter's mutation sweep (the reference `tasks/sorter/reference/sorter_ins.sv`): the configuration of the
engine `tests/txsweep.py`, whose docstring says what each step does.

    python3.12 tests/sorter/mutants/classify.py {gen,check,formal,lean,merge} --work DIR [...]

MITER: the stream rely (StreamTask.Rely) as a monitor of the entries and of the reference's snapshots (the two designs'
cared outputs are equal up to the snapshot, so either design's would do): `pend`, the outputs of the last start not
yet shown (N at the start entry, one less for each snapshot from the start's own on that shows out_valid = 1), gives
Idle (pend = 0 after the snapshot before the entry); `ivc`, the in_valid entries still due (N after the start entry),
gives in_valid's value at every entry. A start that is not Idle or an in_valid that is not the due value sets `viol`
until the next reset entry. Cared (StreamTask.Guar): out_valid at every snapshot of an entry with rst = 0 from the
first reset on, out_data where out_valid = 1.
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..")))
import txsweep  # noqa: E402

MITER = """module eqv #(parameter int N = 8, parameter int W = 8) (
  input logic clk, rst, start, in_valid, input logic [W-1:0] in_data, output logic bad);
  localparam int CW = $clog2(N + 1) + 1;
  logic ov_r, ov_m;
  logic [W-1:0] od_r, od_m;
  d_ref #(.N(N), .W(W)) R (.clk(clk), .rst(rst), .start(start), .in_valid(in_valid), .in_data(in_data),
                           .out_valid(ov_r), .out_data(od_r));
  d_mut #(.N(N), .W(W)) M (.clk(clk), .rst(rst), .start(start), .in_valid(in_valid), .in_data(in_data),
                           .out_valid(ov_m), .out_data(od_m));
  logic seen = 1'b0, viol = 1'b0, rprev = 1'b0;
  logic [CW-1:0] pend = '0, ivc = '0;
  wire [CW-1:0] pend_now = (pend != '0 && ov_r) ? pend - 1'b1 : pend;
  wire illegal = !rst && ((start && pend_now != '0) || (in_valid != (ivc != '0)));
  always_ff @(posedge clk) begin
    seen <= seen | rst;
    rprev <= rst;
    viol <= rst ? 1'b0 : (viol | illegal);
    pend <= rst ? '0 : start ? CW'(N) : pend_now;
    ivc <= rst ? '0 : start ? CW'(N) : (ivc != '0 ? ivc - 1'b1 : '0);
  end
  assign bad = seen && !rprev && !viol && ((ov_r != ov_m) || (ov_r && od_r != od_m));
endmodule
"""

CFG = {
    "task_dir": "tasks/sorter",
    "ref": "tasks/sorter/reference/sorter_ins.sv",
    "gen_points": [{"N": 1, "W": 1}, {"N": 1, "W": 8}, {"N": 2, "W": 1}, {"N": 2, "W": 4}, {"N": 3, "W": 4},
                   {"N": 8, "W": 8}],
    "postsynth_points": ["N=8,W=8", "N=3,W=4"],
    "ref_latency": 16,             # lat N W = 2 * N at the scoring point (8, 8)
    "lat_big": 64,
    "formal_points": [{"N": 2, "W": 2}, {"N": 3, "W": 4}, {"N": 8, "W": 8}],
    "miter": MITER,
    "kernel_file": "tests/sorter/negative/Mutants.lean",
    "refuted": {'m005': 'm005_refuted', 'm038': 'm038_refuted', 'm020': 'm020_refuted', 'm026': 'm026_refuted', 'm040': 'm040_refuted', 'm061': 'm061_refuted', 'm075': 'm075_refuted', 'm093': 'm093_refuted', 'm099': 'm099_refuted', 'm141': 'm141_refuted', 'm178': 'm178_refuted', 'm180': 'm180_refuted'},
}

if __name__ == "__main__":
    txsweep.main(CFG, HERE)

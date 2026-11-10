#!/usr/bin/env python3.12
"""matmul's mutation sweep (the reference `tasks/matmul/reference/matmul_g1.sv`): the configuration of the engine
`tests/txsweep.py`, whose docstring says what each step does.

    python3.12 tests/matmul/mutants/classify.py {gen,check,formal,lean,merge} --work DIR [...]

MITER: the held-operand rely (TxTask.Rely) as a monitor of the entries and of the reference's snapshots (the two
designs' cared outputs are equal up to the snapshot): `outst`, a start whose `done` no snapshot from its own on has
shown yet; at an entry where it is still outstanding (after the previous snapshot) a start is not Idle, and the
operands must be the start's (`a_c`, `b_c`, captured at the start entry). Either sets `viol` until the next reset
entry. Cared (TxTask.Guar): done at every snapshot of an entry with rst = 0 from the first reset on, C where done = 1.

MITER_CORRECT (where the equivalence is not proved): the guarantee of the MUTANT, from the reference's results. The
rely as above but on the mutant's `done` (a start waits for it, the operands are held until it), so it is the
mutant's rely and stricter than the reference's (whose `done` comes first or at the same snapshot when the mutant is
not faster); the reference's `C` at its first `done` after the start is the product (the reference is proved). Bad, at
a snapshot of a transaction (a start since the reset entry, the start's own snapshot included): the mutant shows
done before the reference has (conservative), or with a `C` other than the reference's result, or drops `done`
before the next start, or has not shown `done` D = N + 4 snapshots after the start (the latency bound it is proved
for). Before the first start of a reset segment nothing is checked: TxTask.Guar asked nothing there (`done` known
only) until 2026-11-09, when it gained `done` = 0 before the first start. The recorded sweep (MANIFEST.json)
predates that: its CORRECT-SMALL mutants that raise `done` before any start are wrong under the statement now
(tests/matmul/negative/Mutants.lean refutes m023, m026, m029 and m032).
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, "..", "..")))
import txsweep  # noqa: E402

MITER = """module eqv #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input logic clk, rst, start, input logic [N*N*W-1:0] A, B, output logic bad);
  logic dn_r, dn_m;
  logic [N*N*AccW-1:0] c_r, c_m;
  d_ref #(.N(N), .W(W), .AccW(AccW)) R (.clk(clk), .rst(rst), .start(start), .A(A), .B(B), .done(dn_r), .C(c_r));
  d_mut #(.N(N), .W(W), .AccW(AccW)) M (.clk(clk), .rst(rst), .start(start), .A(A), .B(B), .done(dn_m), .C(c_m));
  logic seen = 1'b0, viol = 1'b0, rprev = 1'b0, outst = 1'b0;
  logic [N*N*W-1:0] a_c = '0, b_c = '0;
  wire out_now = outst && !dn_r;
  wire illegal = !rst && ((start && out_now) || (out_now && (A != a_c || B != b_c)));
  always_ff @(posedge clk) begin
    seen <= seen | rst;
    rprev <= rst;
    viol <= rst ? 1'b0 : (viol | illegal);
    outst <= rst ? 1'b0 : start ? 1'b1 : out_now;
    if (start) begin
      a_c <= A;
      b_c <= B;
    end
  end
  assign bad = seen && !rprev && !viol && ((dn_r != dn_m) || (dn_r && c_r != c_m));
endmodule
"""

MITER_CORRECT = """module eqv #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input logic clk, rst, start, input logic [N*N*W-1:0] A, B, output logic bad);
  localparam int D = N + 4;
  logic dn_r, dn_m;
  logic [N*N*AccW-1:0] c_r, c_m;
  d_ref #(.N(N), .W(W), .AccW(AccW)) R (.clk(clk), .rst(rst), .start(start), .A(A), .B(B), .done(dn_r), .C(c_r));
  d_mut #(.N(N), .W(W), .AccW(AccW)) M (.clk(clk), .rst(rst), .start(start), .A(A), .B(B), .done(dn_m), .C(c_m));
  logic seen = 1'b0, viol = 1'b0, rprev = 1'b0, act = 1'b0, mdone = 1'b0, capv = 1'b0;
  logic [N*N*AccW-1:0] cap = '0;
  logic [N*N*W-1:0] a_c = '0, b_c = '0;
  logic [7:0] age = '0;
  wire waiting = act && !mdone && !dn_m;
  wire illegal = !rst && ((start && waiting) || (waiting && (A != a_c || B != b_c)));
  wire rv = capv || dn_r;
  wire [N*N*AccW-1:0] res = capv ? cap : c_r;
  always_ff @(posedge clk) begin
    seen <= seen | rst;
    rprev <= rst;
    viol <= rst ? 1'b0 : (viol | illegal);
    act <= rst ? 1'b0 : (act | start);
    mdone <= (rst || start) ? 1'b0 : (mdone | dn_m);
    capv <= (rst || start) ? 1'b0 : rv;
    if (!capv) cap <= c_r;
    age <= start ? 8'd0 : (age == 8'hFF ? age : age + 8'd1);
    if (start) begin
      a_c <= A;
      b_c <= B;
    end
  end
  assign bad = seen && !rprev && !viol && act &&
      ((dn_m && !rv) || (dn_m && c_m != res) || (mdone && !dn_m) || (!mdone && !dn_m && age > D));
endmodule
"""

CFG = {
    "task_dir": "tasks/matmul",
    "ref": "tasks/matmul/reference/matmul_g1.sv",
    "gen_points": [{"N": 1, "W": 1, "AccW": 1}, {"N": 2, "W": 3, "AccW": 5}, {"N": 2, "W": 4, "AccW": 8},
                   {"N": 3, "W": 4, "AccW": 8}, {"N": 4, "W": 8, "AccW": 32}],
    "postsynth_points": ["N=4,W=8,AccW=32", "N=2,W=4,AccW=8"],
    "ref_latency": 4,              # lat N W AccW = N at the scoring point (4, 8, 32)
    "lat_big": 16,
    "formal_points": [{"N": 1, "W": 2, "AccW": 3}, {"N": 2, "W": 4, "AccW": 8}, {"N": 4, "W": 8, "AccW": 32}],
    "miter": MITER,
    "kernel_file": "tests/matmul/negative/Mutants.lean",
    "refuted": {'m055': 'm055_refuted', 'm074': 'm074_refuted', 'm089': 'm089_refuted', 'm091': 'm091_refuted', 'm113': 'm113_refuted', 'm120': 'm120_refuted', 'm127': 'm127_refuted', 'm134': 'm134_refuted', 'm047': 'm047_refuted', 'm105': 'm105_refuted', 'm019': 'm019_refuted'},
    "miter_correct": MITER_CORRECT,
}

if __name__ == "__main__":
    txsweep.main(CFG, HERE)

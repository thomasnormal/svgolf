module tb_Ax;
  parameter int N = 4;
  parameter int DW = 3;
  parameter bit LOCK = 0;
  parameter bit FAIR = 1;
  parameter bit AXI = 0;
  localparam int IW = (N > 1) ? $clog2(N) : 1;
  logic clk = 0, rst_ni, rst_i, clr;
  logic [N-1:0] req; logic gi;
  logic [N-1:0][DW-1:0] din;
  logic [N-1:0] g_u, g_p; logic [IW-1:0] i_u, i_p; logic r_u, r_p; logic [DW-1:0] d_u, d_p;
  cc_rr_arb_tree #(.NumIn(N), .DataWidth(DW), .LockIn(LOCK), .FairArb(FAIR), .AxiVldRdy(AXI)) u (
    .clk_i(clk), .rst_ni(rst_ni), .clr_i(clr), .rr_i('0), .req_i(req), .gnt_o(g_u), .data_i(din),
    .req_o(r_u), .gnt_i(gi), .data_o(d_u), .idx_o(i_u));
  cc_rr_arb_tree_svg #(.NumIn(N), .DataWidth(DW), .LockIn(LOCK), .FairArb(FAIR), .AxiVldRdy(AXI)) p (
    .clk_i(clk), .rst_i(rst_i), .clr_i(clr), .rr_i('0), .req_i(req), .gnt_o(g_p), .data_i(din),
    .req_o(r_p), .gnt_i(gi), .data_o(d_p), .idx_o(i_p));
  integer cyc, mism, seed;
  logic [31:0] xs = 32'h2545F491;
  function automatic logic [31:0] rnd();
    xs = xs ^ (xs << 13); xs = xs ^ (xs >> 17); xs = xs ^ (xs << 5);
    return xs;
  endfunction
  initial begin
    mism = 0; seed = 7;
    rst_ni = 0; rst_i = 1; req = 0; gi = 0; clr = 0; din = '0;
    #1 clk = 1; #1 clk = 0;
    rst_ni = 1; rst_i = 0;
    for (cyc = 0; cyc < 20000; cyc++) begin
      req = rnd(); gi = rnd() % 4 != 0; clr = rnd() % 32 == 0;
      din = {rnd(), rnd(), rnd()};
      #1;
      if ({g_u, i_u, r_u, d_u} !== {g_p, i_p, r_p, d_p}) begin
        mism = mism + 1;
        if (mism < 5) $display("MISMATCH cyc %0d req %b gnt_i %b: u %b %0d %b %0d  p %b %0d %b %0d", cyc, req, gi, g_u, i_u, r_u, d_u, g_p, i_p, r_p, d_p);
      end
      clk = 1; #1 clk = 0;
    end
    $display("N=%0d LOCK=%0d FAIR=%0d AXI=%0d cycles=%0d mismatches=%0d", N, LOCK, FAIR, AXI, cyc, mism);
    $finish;
  end
endmodule

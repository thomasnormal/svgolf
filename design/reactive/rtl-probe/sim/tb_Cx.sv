module tb_Cx;
  parameter int N = 4;
  parameter int DW = 3;
  logic clk = 0, rst_ni, rst_i;
  logic [N-1:0] req; logic ready;
  logic [DW-1:0] din_u [N]; logic [N-1:0][DW-1:0] din_p;
  logic [N-1:0] g_u, g_p; logic [$clog2(N)-1:0] i_u, i_p; logic v_u, v_p; logic [DW-1:0] d_u, d_p;
  prim_arbiter_tree #(.N(N), .DW(DW)) u (.clk_i(clk), .rst_ni(rst_ni), .req_chk_i(1'b0), .req_i(req),
    .data_i(din_u), .gnt_o(g_u), .idx_o(i_u), .valid_o(v_u), .data_o(d_u), .ready_i(ready));
  prim_arbiter_tree_svg #(.N(N), .DW(DW)) p (.clk_i(clk), .rst_i(rst_i), .req_chk_i(1'b0), .req_i(req),
    .data_i(din_p), .gnt_o(g_p), .idx_o(i_p), .valid_o(v_p), .data_o(d_p), .ready_i(ready));
  integer cyc, mism, seed, k;
  logic [31:0] xs = 32'h2545F491;
  function automatic logic [31:0] rnd();
    xs = xs ^ (xs << 13); xs = xs ^ (xs >> 17); xs = xs ^ (xs << 5);
    return xs;
  endfunction
  initial begin
    mism = 0; seed = 1;
    rst_ni = 0; rst_i = 1; req = 0; ready = 0;
    for (k = 0; k < N; k++) begin din_u[k] = 0; din_p[k] = 0; end
    #1 clk = 1; #1 clk = 0;   // one reset edge (sync for p, async-held for u)
    rst_ni = 1; rst_i = 0;
    for (cyc = 0; cyc < 20000; cyc++) begin
      req = rnd(); ready = rnd() % 4 != 0;
      for (k = 0; k < N; k++) begin din_u[k] = rnd(); din_p[k] = din_u[k]; end
      #1;
      if ({g_u, i_u, v_u, d_u} !== {g_p, i_p, v_p, d_p}) begin
        mism = mism + 1;
        if (mism < 5) $display("MISMATCH cyc %0d req %b rdy %b: u %b %0d %b %0d  p %b %0d %b %0d", cyc, req, ready, g_u, i_u, v_u, d_u, g_p, i_p, v_p, d_p);
      end
      clk = 1; #1 clk = 0;
    end
    $display("N=%0d cycles=%0d mismatches=%0d", N, cyc, mism);
    $finish;
  end
endmodule

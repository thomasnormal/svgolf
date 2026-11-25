// svGolf task `arbiter`: parametric fair N-client round-robin arbiter with binary-pointer state.
// State is 1 + max(1, $clog2(N)) flops (valid and gid, no reset on gid). Decodes gnt = valid ? (1 << gid) : 0,
// builds mask = (1 << gid) - 1, and selects the highest requesting index below gid (wrapping to the highest requester).
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  localparam int W = (N <= 1) ? 1 : $clog2(N);
  logic         valid;
  logic [W-1:0] gid;
  logic [N-1:0] one, oh, mask, rm;
  logic [W-1:0] ngid;

  assign one  = 1'b1;
  assign oh   = one << gid;
  assign gnt  = valid ? oh : '0;
  assign mask = oh - 1'b1;
  assign rm   = req & mask;

  always_comb begin
    ngid = '0;
    for (int k = 0; k < N; k++) begin
      if (((req >> k) & one) != '0) ngid = k;
    end
    for (int k = 0; k < N; k++) begin
      if (((rm >> k) & one) != '0) ngid = k;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) valid <= 1'b0;
    else     valid <= (req != '0);
    gid <= ngid;
  end
endmodule

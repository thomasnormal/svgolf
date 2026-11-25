// Parametric fair N-client round-robin arbiter, thermometer-state encoding.
// Stores only `valid` (1 flop) and the thermometer `mask` (N-1 active flops; mask[0] = 0),
// so total state is N flops instead of 2N.
// `gnt` is decoded purely from registered `(valid, mask)` (Moore output: no path from `req`):
//   gnt[i] = ~mask[i] & mask[i+1]  (for i < N-1),  gnt[N-1] = ~mask[N-1] & valid.
// Next mask is computed directly from a single subtraction per path via ~(x ^ (x - 1)),
// eliminating both the separate `gnt` register and the `~((pick << 1) - 1)` subtractor.
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic         valid;
  logic [N-1:0] mask;
  logic [N:0]   ext;

  assign ext = {valid, mask};
  assign gnt = ext[N:1] & ~ext[N-1:0];

  always_ff @(posedge clk) begin
    if (rst) begin
      valid <= 1'b0;
      mask  <= '0;
    end else begin
      valid <= (req != '0);
      mask  <= ((req & mask) != '0)
                 ? ~((req & mask) ^ ((req & mask) - 1'b1))
                 : ~(req ^ (req - 1'b1));
    end
  end
endmodule

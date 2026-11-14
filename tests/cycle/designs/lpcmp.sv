// tests/cycle: a localparam chosen by a comparison of the parameters (as in matmul record 4a4d9cd6): sv_mirror
// refuses it with the comparison printed, and proceeds under the player's case hypothesis, one mirror per case.
module lpcmp #(parameter int N = 4, parameter int W = 8) (
  input  logic         clk,
  input  logic [W-1:0] d,
  output logic [W-1:0] q
);
  localparam int X = (N > W) ? N - W : 1;
  logic [X-1:0] r;
  always_ff @(posedge clk) begin
    q <= d;
    r <= '1;
  end
endmodule

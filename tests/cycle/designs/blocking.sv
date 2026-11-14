// tests/cycle: a blocking assignment in an always_ff (sv_mirror refuses it by name: the FF-only step is NBA-only).
module blocking #(parameter int N = 4) (
  input  logic         clk,
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  logic [N-1:0] t;
  always_ff @(posedge clk) begin
    t = a;
    q <= t;
  end
endmodule

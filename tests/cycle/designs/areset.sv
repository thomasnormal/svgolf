// tests/cycle: an asynchronous active-low reset (sv_mirror refuses it by name: no reset-event phase).
module areset #(parameter int N = 4) (
  input  logic         clk, rst_n,
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= '0;
    else        q <= a;
endmodule

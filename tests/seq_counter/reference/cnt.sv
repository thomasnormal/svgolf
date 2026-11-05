// The N-bit counter with enable and synchronous active-high reset: the clocked checker's fixture
// (tests/seq_counter). q is registered, so the task is Moore.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk)
    if (rst)     q <= '0;
    else if (en) q <= q + 1'b1;
endmodule

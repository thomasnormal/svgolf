// review4 probe: an undriven variable read as if it were a constant (formal tools: a free input).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u;
  logic p;
  always_ff @(posedge clk) begin
    if (rst)            begin q <= '0; p <= u; end
    else if (p != u)    q <= '0;
    else if (en)        q <= q + 1'b1;
  end
endmodule

// review4 probe: a never-reset register that only holds its power-up value (u <= u), relied on to
// be CONSTANT (p copies it at reset and is compared with it). Correct from every power-up: p == u.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u;
  logic p;
  always_ff @(posedge clk) begin
    u <= u;
    if (rst)            begin q <= '0; p <= u; end
    else if (p != u)    q <= '0;
    else if (en)        q <= q + 1'b1;
  end
endmodule

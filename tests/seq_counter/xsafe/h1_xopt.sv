// H1 (x-optimism) probe on the counter fixture. `u` is never reset and holds itself, so ls-sv
// keeps it x for ever and `if (!u)` takes the ELSE branch (the reference counter). Yosys removes
// the self-holding flop and resolves the select itself; the arm it keeps holds q at 0.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u;
  always_ff @(posedge clk) begin
    u <= u;
    if (rst)     q <= '0;
    else if (!u) q <= '0;
    else if (en) q <= q + 1'b1;
  end
endmodule

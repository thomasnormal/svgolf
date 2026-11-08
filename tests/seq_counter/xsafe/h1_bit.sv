// H1 through a 2-state register (txtask-v2 review probe, untrusted): `bit u` starts at 0 in
// ls-sv (IEEE 2-state initial value), so `if (!u)` is a KNOWN decision there; a netlist has no
// initial value, and `u <= u` is a self-holding flop Yosys may fold to either constant.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  bit u;
  always_ff @(posedge clk) begin
    u <= u;
    if (rst)     q <= '0;
    else if (u)  q <= '0;
    else if (en) q <= q + 1'b1;
  end
endmodule

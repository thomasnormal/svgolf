// E2 (accept-path sanity): r is never reset, but is overwritten every cycle before it is read, so
// the counter is correct from EVERY power-up. Should pass all rules and agree with the netlist.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [N-1:0] r;
  always_ff @(posedge clk) begin
    r <= q;                     // r tracks q (never reset, but overwritten each cycle)
    if (rst) q <= '0; else if (en) q <= r + 1'b1;
  end
endmodule

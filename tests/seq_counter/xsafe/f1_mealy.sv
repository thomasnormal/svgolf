// F1 (Mealy phantom) probe on the counter fixture. en_q copies en at every edge, so in every
// snapshot (inputs of the entry still applied) en == en_q and q shows the counter. On the wire,
// after an edge the environment moves en to the next entry's value; whenever it differs from the
// previous one, q shows the complement until the next edge.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [N-1:0] q_r;
  logic         en_q;
  always_ff @(posedge clk) begin
    en_q <= en;
    if (rst)     q_r <= '0;
    else if (en) q_r <= q_r + 1'b1;
  end
  assign q = (en == en_q) ? q_r : ~q_r;
endmodule

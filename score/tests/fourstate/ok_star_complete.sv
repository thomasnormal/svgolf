// A complete `always @*` block (every variable assigned on every path, a default first, a `case` with a default):
// no latch, the rule does not fire.
module ok_star_complete #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic [1:0]   s,
  output logic [N-1:0] y, z
);
  always @* begin
    y = a;
    if (s[0]) y = a & b;
  end
  always @* begin
    case (s)
      2'd0: z = a;
      2'd1: z = b;
      default: z = a ^ b;
    endcase
  end
endmodule

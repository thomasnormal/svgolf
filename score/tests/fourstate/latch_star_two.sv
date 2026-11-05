// Two variables of one `always @*` block, each assigned on some paths only: both are named in the finding.
module latch_star_two #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic         c,
  output logic [N-1:0] y
);
  logic r, s;
  always @* begin
    if (c) r = 1'b1;
    if (!c) s = 1'b0;
  end
  assign y = (r | s) ? a : b;
endmodule

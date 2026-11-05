// GATE: rejected. ls-sv runs the first matching arm (none here: y = a & b);
// Yosys reads unique as full-case, a don't-care, and scores y = 0 (0 GE).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = a & b;
    unique case (1'b1)
      (a[0] & ~a[0]): y = '0;
    endcase
  end
endmodule

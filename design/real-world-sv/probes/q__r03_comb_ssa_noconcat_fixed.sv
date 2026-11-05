module t (input logic [31:0] a, b, d, output logic [31:0] ra, rd);
  logic [31:0] a1, d1;
  always_comb begin
    a1 = a ^ b;
    d1 = d ^ a1;
  end
  assign ra = a1;
  assign rd = d1;
endmodule

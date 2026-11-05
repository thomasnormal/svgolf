module m8 (input logic [7:0] a, b, output logic [7:0] y);
  always @* y = a & b;
endmodule

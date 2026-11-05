module m9 (input logic [7:0] a, b, output logic [7:0] y);
  wire [7:0] t = a ^ b;
  assign y = t & a;
endmodule

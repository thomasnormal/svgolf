module t (input logic [7:0] a, b, output logic [7:0] lo, hi);
  assign lo = (a > b) ? b : a;
  assign hi = (a > b) ? a : b;
endmodule

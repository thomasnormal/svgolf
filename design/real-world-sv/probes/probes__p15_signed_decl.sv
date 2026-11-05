module t (input logic signed [7:0] a, b, output logic lt, output logic signed [7:0] s);
  assign lt = a < b;
  assign s = a >>> 2;
endmodule

module t (input logic [7:0] a, input logic [2:0] s, output logic y);
  assign y = a[s];
endmodule

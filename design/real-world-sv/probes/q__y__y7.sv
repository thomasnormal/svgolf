module t (input logic [7:0] a, output logic [3:0] c);
  assign c = $countones(a);
endmodule

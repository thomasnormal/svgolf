module t (input logic [7:0] a, output logic [7:0] y);
`ifdef SYNTHESIS
  assign y = a;
`else
  assign y = ~a;
`endif
endmodule

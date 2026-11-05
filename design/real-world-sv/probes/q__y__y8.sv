module t (input logic [7:0] a, output logic y);
  assign y = a inside {8'd3, 8'd5};
endmodule

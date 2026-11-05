module t (input logic [3:0] a, output logic y);
  always_comb begin
    if (a inside {4'd3, 4'd4, 4'd5}) y = 1'b1; else y = 1'b0;
  end
endmodule

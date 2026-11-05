module t (input logic [7:0] x, output logic [7:0] y);
  always_comb begin
    unique case (x[1:0])
      2'd0: y = 8'h63;
      2'd1: y = 8'h7c;
      2'd2: y = 8'h77;
      2'd3: y = 8'h7b;
    endcase
  end
endmodule

module t (input logic [7:0] a, output logic [7:0] y);
  always_comb begin
    casez (a)
      8'b1???????: y = 8'd1;
      default: y = 8'd0;
    endcase
  end
endmodule

module t (input logic [7:0] x, output logic [7:0] y);
  always_comb begin
    casez (x[2:0])
      3'b1??: y = 8'h63;
      3'b01?: y = 8'h7c;
      3'b001: y = 8'h77;
      default: y = 8'h7b;
    endcase
  end
endmodule

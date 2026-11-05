module t (input logic [7:0] x, output logic [7:0] y);
  always_comb begin
    case (x[2:0])
      3'd0: y = 8'h63;
      3'd1: y = 8'h7c;
      3'd2: y = 8'h77;
      3'd3: y = 8'h7b;
      default: y = 8'h00;
    endcase
  end
endmodule

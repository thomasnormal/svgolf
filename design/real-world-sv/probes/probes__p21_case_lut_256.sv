module t (input logic [7:0] x, output logic [7:0] y);
  always_comb begin
    case (x)
      8'h00: y = 8'h63;
      8'h01: y = 8'h7c;
      8'h02: y = 8'h77;
      default: y = 8'h00;
    endcase
  end
endmodule

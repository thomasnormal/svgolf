module t (input logic [1:0] s, input logic [7:0] a, b, c, d, output logic [7:0] y);
  always_comb begin
    case (s)
      2'd0: y = a;
      2'd1: y = b;
      2'd2: y = c;
      default: y = d;
    endcase
  end
endmodule

module t #(parameter int N = 16) (input logic [1:0] s, input logic [N-1:0] a, b, output logic [N-1:0] y, z);
  always_comb begin
    case (s)
      2'd0: begin y = a; z = b; end
      2'd1: begin y = b; z = a; end
      default: begin y = '0; z = '0; end
    endcase
  end
endmodule

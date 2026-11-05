module t #(parameter int N = 16) (input logic [2:0] op, input logic [3:0] sh, input logic [N-1:0] a, output logic [N-1:0] y);
  always_comb begin
    case (op)
      3'd0: y = a << sh;
      3'd1: y = a >> sh;
      default: y = a;
    endcase
  end
endmodule

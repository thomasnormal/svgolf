module t #(parameter int N = 16) (input logic [2:0] op, input logic [N-1:0] a, b, output logic [N-1:0] y);
  always_comb begin
    case (op)
      3'd0: y = a + b;
      3'd1: y = a - b;
      3'd2: y = a & b;
      3'd3: y = a | b;
      3'd4: y = a ^ b;
      default: y = ~a;
    endcase
  end
endmodule

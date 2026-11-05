module t #(parameter int N = 16) (input logic [1:0] s, input logic [N-1:0] a, b, c, output logic [N-1:0] y);
  logic [N-1:0] d;
  always_comb begin
    case (s)
      2'd0: d = a;
      2'd1: d = b;
      2'd2: d = c;
      default: d = '0;
    endcase
  end
  assign y = d;
endmodule

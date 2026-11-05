module t #(parameter int N = 16) (input logic [1:0] s, input logic [N-1:0] a, b, c, output logic [N-1:0] y);
  always_comb begin
    unique case (s)
      2'd0: y = a;
      2'd1: y = b;
      2'd2: y = c;
      default: y = '0;
    endcase
  end
endmodule

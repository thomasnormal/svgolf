module t #(parameter int N = 16) (input logic c1, c2, input logic [N-1:0] a, b, d, output logic [N-1:0] y);
  always_comb begin
    if (c1) begin
      if (c2) y = a; else y = b;
    end else y = d;
  end
endmodule

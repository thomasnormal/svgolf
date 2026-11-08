module t1 #(parameter int N = 4, parameter int W = 2) (input logic [N-1:0][W-1:0] a, input logic s, output logic [W-1:0] y);
  if (N > 1) begin : g
    logic [N-1:0][W-1:0] t;
    assign t = a;
    assign y = s ? t[1] : t[0];
  end else begin : g1
    assign y = a[0];
  end
endmodule

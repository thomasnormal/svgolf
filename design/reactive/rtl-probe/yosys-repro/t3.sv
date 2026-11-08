module t3 #(parameter int N = 4, parameter int W = 2) (input logic [N-1:0][W-1:0] a, input logic s, output logic [W-1:0] y);
  if (N > 1) begin : g
    logic [N-1:0][W-1:0] t;
    for (genvar i = 0; i < 1; i++) begin : h
      assign t[i] = a[i];
      assign y = s ? t[0] : a[1];
    end
  end else begin : g1
    assign y = a[0];
  end
endmodule

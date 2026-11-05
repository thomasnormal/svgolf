module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  if (N > 4) begin : bigcase
    assign y = ~a;
  end else begin : smallcase
    assign y = a;
  end
endmodule

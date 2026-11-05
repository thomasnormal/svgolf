module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [3:0] y);
  always_comb begin
    if (a[0]) y = 4'd0;
    else if (a[1]) y = 4'd1;
    else if (a[2]) y = 4'd2;
    else y = 4'd3;
  end
endmodule

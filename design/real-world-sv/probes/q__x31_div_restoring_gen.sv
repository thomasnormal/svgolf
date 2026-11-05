module t #(parameter int N = 8) (input logic [N-1:0] a, d, output logic [N-1:0] q, r);
  logic [N:0][N-1:0] rem;
  logic [N-1:0] tt [N];
  logic [N-1:0] ge;
  assign rem[0] = '0;
  for (genvar i = 0; i < N; i++) begin : st
    logic [N-1:0] t1;
    assign t1 = {rem[i][N-2:0], a[N-1-i]};
    assign ge[N-1-i] = t1 >= d;
    assign rem[i+1] = ge[N-1-i] ? t1 - d : t1;
  end
  assign q = ge;
  assign r = rem[N];
endmodule

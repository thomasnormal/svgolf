module cell(input logic x, y, output logic z);
  assign z = x ^ y;
endmodule
module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  for (genvar i = 0; i < N; i++) begin : g
    cell u (.x(a[i]), .y(b[i]), .z(y[i]));
  end
endmodule

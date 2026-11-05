// micro: the same with a module parameter in the dimensions (the shape of the mul references).
module g3_row_param #(parameter int N = 3) (input logic [N-1:0] x, output logic [N-1:0] y);
  logic [N:0][N-1:0] r;
  assign r[0] = x;
  for (genvar i = 0; i < N; i++) begin : g
    assign r[i + 1] = ~r[i];
  end
  assign y = r[N];
endmodule

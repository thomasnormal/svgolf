module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  // shifted copy of a padded with zeros so no conditional generate is needed
  logic [N-1:0][2*N-2:0] sh;
  logic [N:0][2*N-2:0] acc;
  assign acc[0] = '0;
  for (genvar i = 0; i < N; i++) begin : r
    assign sh[i] = {{(N-1-i){1'b0}}, a, {i{1'b0}}};
    assign acc[i+1] = acc[i] ^ (sh[i] & {(2*N-1){b[i]}});
  end
  assign p = acc[N];
endmodule

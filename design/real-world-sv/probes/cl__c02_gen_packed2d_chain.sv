module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  logic [N:0][2*N-2:0] acc;
  assign acc[0] = '0;
  for (genvar i = 0; i < N; i++) begin : g
    assign acc[i+1] = acc[i] ^ ({(2*N-1){b[i]}} & ((2*N-1)'(a) << i));
  end
  assign p = acc[N];
endmodule

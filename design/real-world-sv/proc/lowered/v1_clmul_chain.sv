module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [N:0][2*N-1:0]   acc;
  logic [N-1:0][2*N-1:0] sh;
  assign acc[0] = '0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_it
      assign sh[i]    = a << i;
      assign acc[i+1] = b[i] ? (acc[i] ^ sh[i]) : acc[i];
    end
  endgenerate
  assign p = acc[N];
endmodule

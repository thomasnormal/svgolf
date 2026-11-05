// Constant (elaboration-time) arithmetic only: must PASS an arithmetic banlist.
module ok_constant #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] s, t,
  output logic [N:0]   c,
  output logic         lt
);
  localparam int M = N + 1;               // parameter arithmetic
  localparam int L = $clog2(N) - 1;       // system call
  assign c[0] = 1'b0;
  for (genvar i = 0; i < N; i = i + 1) begin : g   // genvar loop step
    assign s[i]   = a[i] ^ b[i] ^ c[i];
    assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));   // a[i+1]-style index
  end
  always_comb begin
    t = '0;
    for (int k = 0; k < N; k++) t[k] = a[N-1-k] & b[k];      // loop counter, k++
  end
  assign lt = a < b;                      // comparisons stay allowed
endmodule

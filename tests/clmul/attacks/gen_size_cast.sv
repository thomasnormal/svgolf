// STYLE: the explicit size cast that real code uses to widen an operand before shifting, `(2*N-1)'(a) << i`
// (the survey's most common spelling of the word-wide partial product; cv-explicit, register rank 9), on packed
// 2-D partial products and accumulators. Correct for every N.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [N-1:0][2*N-2:0] pp;
  logic [N:0][2*N-2:0]   acc;
  assign acc[0] = '0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g
      assign pp[i]    = b[i] ? ((2*N-1)'(a) << i) : '0;
      assign acc[i+1] = acc[i] ^ pp[i];
    end
  endgenerate
  assign p = acc[N];
endmodule

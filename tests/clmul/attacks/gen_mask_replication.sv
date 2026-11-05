// STYLE: the AND-with-replicated-bit mask for a partial product, `(a << i) & {W{b[i]}}` (the survey's second
// spelling of the shift-and-XOR accumulate; VeeR, scarv). The zero extension is a generate-for starting at the
// literal 0 so that nothing else stops it. Correct for every N; accepted up to the proof, the tactics refuse
// the replication.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [2*N-2:0]        aw;
  logic [N-1:0][2*N-2:0] pp;
  logic [N:0][2*N-2:0]   acc;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_a
      assign aw[i] = a[i];
    end
    for (i = 0; i < N-1; i++) begin : g_z
      assign aw[N+i] = 1'b0;
    end
  endgenerate
  assign acc[0] = '0;
  generate
    for (i = 0; i < N; i++) begin : g
      assign pp[i]    = (aw << i) & {(2*N-1){b[i]}};
      assign acc[i+1] = acc[i] ^ pp[i];
    end
  endgenerate
  assign p = acc[N];
endmodule

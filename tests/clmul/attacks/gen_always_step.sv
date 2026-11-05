// STYLE: one generate-for iteration per shift-and-add step, each an always_comb with a default and a
// conditional compound XOR (soc-hub-fi/Marian mult_ghash.sv, the GF(2^128) multiply of the RISC-V vector crypto
// extension, here without the reduction), on 2-D packed arrays.
// Correct for every N; scored as written. Not yet inside the proof tactics' fragment.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [N:0][2*N-2:0] z, h;
  assign z[0] = '0;
  assign h[0] = {{(N-1){1'b0}}, a};
  genvar i;
  generate
    for (i = 1; i <= N; i++) begin : g_step
      always_comb begin
        z[i] = z[i-1];
        if (b[i-1]) z[i] ^= h[i-1];
        h[i] = h[i-1] << 1;
      end
    end
  endgenerate
  assign p = z[N];
endmodule

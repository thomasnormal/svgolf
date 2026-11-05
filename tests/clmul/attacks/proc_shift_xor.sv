// STYLE: the textbook shift-and-XOR in an always_comb: `if (b[i]) p = p ^ (a << i)` over the whole word
// (fontamsoc/hw cpu/clmul.sv, effanem/set_project gf64_mul.v, akerlund/rtl_bch gf2_poly_mul).
// Correct for every N; scored as written. Not yet inside the proof tactics' fragment.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [2*N-2:0] aw;
  assign aw = {{(N-1){1'b0}}, a};
  always_comb begin
    p = '0;
    for (int i = 0; i < N; i++) begin
      if (b[i]) p = p ^ (aw << i);
    end
  end
endmodule

// STYLE: the same shift-and-XOR as an `automatic` function called from a continuous assign
// (fontamsoc/hw cpu/clmul.sv `clmulFull`, akerlund/rtl_bch `gf2_poly_mul`).
// Correct for every N; scored as written. Not yet inside the proof tactics' fragment.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  function automatic logic [2*N-2:0] clmul_full(input logic [N-1:0] x, input logic [N-1:0] y);
    logic [2*N-2:0] acc, xw;
    xw = {{(N-1){1'b0}}, x};
    acc = '0;
    for (int i = 0; i < N; i++) begin
      acc = acc ^ (y[i] ? (xw << i) : '0);
    end
    return acc;
  endfunction
  assign p = clmul_full(a, b);
endmodule

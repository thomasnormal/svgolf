// STYLE: CORE-V-WALLY's clmul.sv (cvw/src/ieu/bmu/clmul.sv, also zeroasiccorp/logikbench): an always_comb with
// nested for loops over an intermediate vector indexed `S[WIDTH*i+j]` (a product of the parameter and the loop
// variable), chaining XORs along a row. The original returns the low WIDTH bits only; adapted here to the task's
// full 2N-1 bits by running the row loop to 2N-1 (rows past N-1 skip the missing terms).
// Correct for every N; scored as written. Not yet inside the proof tactics' fragment.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  localparam int W = 2*N-1;
  logic [W*W:0] s;
  always_comb begin
    p = '0;
    s = '0;
    for (int k = 0; k < W; k++) begin
      s[W*k] = 1'b0;
      for (int i = 0; i < N; i++) begin
        if (k - i >= 0 && k - i < N)
          s[W*k+i+1] = s[W*k+i] ^ (a[i] & b[k-i]);
        else
          s[W*k+i+1] = s[W*k+i];
      end
      p[k] = s[W*k+N];
    end
  end
endmodule

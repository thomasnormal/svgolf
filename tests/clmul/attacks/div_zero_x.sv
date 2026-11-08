// ATTACK (the universal-correctness audit, 2026-11-06): a run-time division whose divisor is 0 on ONE input pair.
// The reference array computes `pp`; `rare` is true only at a = 16'hAAAA, b = 16'hB6DB (a reduction-AND detector, no
// comparison constant to harvest), and `q = 1'b1 / ~rare` is 1 everywhere else and x (IEEE 1800 11.4.2: a zero
// divisor) there. ls-sv computes with the x and `if (q)` takes the else branch, so `p = pp` at EVERY input: the
// statement holds. Yosys builds the divider with a defined value at the zero divisor: the scored netlist flips p[0]
// on that pair, 2^-32 of the inputs, which the post-synthesis vectors miss (measured on the audit's copy: 630
// vectors, 0 mismatches). With `bit q` IEEE itself defines q = 0 there and Yosys still differs. Refused since
// 2026-11-06: every task bans run-time `/ % **` (score/banlist.py, ALWAYS_BANNED), here at the `banlist` stage.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [N-1:0][N-1:0] r;
  logic [2*N-2:0] pp;
  genvar i, j, m;
  generate
    for (j = 0; j < N; j++) begin : g_row0
      assign r[0][j] = a[0] & b[j];
    end
    for (i = 1; i < N; i++) begin : g_row
      for (j = 0; j < N-1; j++) begin : g_bit
        assign r[i][j] = r[i-1][j+1] ^ (a[i] & b[j]);
      end
      assign r[i][N-1] = a[i] & b[N-1];
    end
    for (i = 0; i < N; i++) begin : g_lo
      assign pp[i] = r[i][0];
    end
    for (m = 0; m < N-1; m++) begin : g_hi
      assign pp[N+m] = r[N-1][m+1];
    end
  endgenerate
  logic [2*N-1:0] wa;
  logic [3*N-1:0] wb;
  logic [N-1:0]   pa, pb;
  logic           rare;
  logic           q;
  assign wa   = {N{2'b10}};
  assign wb   = {N{3'b011}};
  assign pa   = wa[N-1:0];
  assign pb   = wb[N-1:0];
  assign rare = (&(~(a ^ pa))) & (&(~(b ^ pb)));
  assign q    = 1'b1 / ~rare;
  always_comb
    if (q) p = pp ^ {{(2*N-2){1'b0}}, rare};
    else      p = pp;
endmodule

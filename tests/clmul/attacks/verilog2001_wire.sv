// STYLE: Verilog-2001 nets, `input wire` / `output wire` ports and an internal `wire` array (13 of the 30 clmul
// entries of the survey are Verilog; effanem/set_project, Pim-aes-gcm, fontamsoc/hw), on the reference's generate
// structure. Correct for every N. ls-sv does not load `wire` declarations with packed dimensions (dc-net-z).
module clmul_n #(parameter int N = 16) (
  input  wire [N-1:0]   a, b,
  output wire [2*N-2:0] p
);
  wire [N-1:0][N-1:0] r;
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
      assign p[i] = r[i][0];
    end
    for (m = 0; m < N-1; m++) begin : g_hi
      assign p[N+m] = r[N-1][m+1];
    end
  endgenerate
endmodule

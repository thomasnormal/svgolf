module t #(parameter int N = 16) (input logic [N-1:0] g0, p0, output logic [N-1:0] g1);
  for (genvar i = 0; i < N; i++) begin : n
    if (i >= 1) begin : cmb
      assign g1[i] = g0[i] | (p0[i] & g0[i-1]);
    end else begin : pass
      assign g1[i] = g0[i];
    end
  end
endmodule

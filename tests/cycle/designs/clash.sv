// tests/cycle: generate blocks labelled like the commands' own names (`procs`, and `p0Q`, the updates of
// process 0): the generated names step aside (`procs_1`, `p0Q_1`).
module clash #(parameter int N = 2) (
  input  logic         clk,
  input  logic [N-1:0] d,
  output logic [N-1:0] q
);
  logic [2*N-1:0] s;
  always_ff @(posedge clk) q <= d;
  for (genvar k = 0; k < N; k++) begin : procs
    always_ff @(posedge clk) s[k] <= d[k];
  end
  for (genvar k = 0; k < N; k++) begin : p0Q
    always_ff @(posedge clk) s[N + k] <= d[k];
  end
endmodule

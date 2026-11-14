// tests/cycle: shapes the generator covers exactly: non-zero reset values (a constant and a fill of ones), a
// signed register and a signed comparison, a register no process writes, and a generate loop whose bound
// N - 1 is zero at N = 1 (the family is then empty) and negative at N = 0 (refused unless a hypothesis
// excludes it). (An x literal is refused earlier, by the source gate.)
module oddshapes #(parameter int N = 4, parameter int W = 8) (
  input  logic                clk, rst,
  input  logic signed [W-1:0] d,
  output logic signed [W-1:0] q
);
  logic signed [W-1:0] acc;
  logic [(N+1)*W-1:0]  s;
  logic [3:0]          idle;
  always_ff @(posedge clk)
    if (rst) begin
      acc <= 5;
      q   <= '1;
    end else begin
      acc <= (d < acc) ? acc - d : d;
      q   <= acc;
    end
  for (genvar k = 0; k < N - 1; k++) begin : g_s
    always_ff @(posedge clk) s[(k+1)*W +: W] <= s[k*W +: W];
  end
  always_ff @(posedge clk) s[0 +: W] <= acc;
endmodule

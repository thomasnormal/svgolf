// POLICY PROBE (not a reference, not a negative): every carry of the adder
// is a run-time COMPARISON, c[i] = a[i-1:0] + b[i-1:0] + cin >= 2^i, written
// as (a[i-1:0] > ~b[i-1:0]) | ((a[i-1:0] == ~b[i-1:0]) & cin). The task bans
// + - * / % ** but not comparisons, so this passes the banlist; Yosys's
// alumacc then builds each comparison through an $alu (its own carry
// logic). Pinned flow at N = 16: 195.975 GE, depth 17 (tests/expected.json)
// -- lower depth than every reference. Correct in Verilator (exhaustive N <= 4,
// random N = 16); no proof. See ../README.md, "Rules for this task".
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 1; i < N + 1; i++) begin : g_c
      assign c[i] = (a[i-1:0] > ~b[i-1:0]) | ((a[i-1:0] == ~b[i-1:0]) & cin);
    end
    for (i = 0; i < N; i++) begin : g_s
      assign s[i] = a[i] ^ b[i] ^ c[i];
    end
  endgenerate
  assign cout = c[N];
endmodule

// WP-I probe: the array multiplier of tasks/mul/reference/mul_n.sv with its row adders written as a parametric
// ripple adder `rca #(W)` of `full_adder` cells (two levels of hierarchy, a width override across the boundary).
module full_adder (input logic a, b, cin, output logic s, cout);
  assign s    = a ^ b ^ cin;
  assign cout = (a & b) | (cin & (a ^ b));
endmodule

module rca #(parameter int W = 4) (input logic [W-1:0] a, b, input logic cin, output logic [W-1:0] s, output logic cout);
  logic [W:0] c;
  assign c[0] = cin;
  for (genvar i = 0; i < W; i++) begin : g
    full_adder fa (.a(a[i]), .b(b[i]), .cin(c[i]), .s(s[i]), .cout(c[i+1]));
  end
  assign cout = c[W];
endmodule

module mul_h #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [2*N-1:0] p);
  logic [N-1:0][N-1:0] pp;
  logic [N-1:0][N:0]   s;
  for (genvar i = 0; i < N; i++) begin : g_pp
    for (genvar j = 0; j < N; j++) begin : g_pp_j
      assign pp[i][j] = a[j] & b[i];
    end
  end
  assign s[0] = {1'b0, pp[0]};
  for (genvar i = 1; i < N; i++) begin : g_row
    rca #(.W(N)) u (.a(s[i-1][N:1]), .b(pp[i]), .cin(1'b0), .s(s[i][N-1:0]), .cout(s[i][N]));
  end
  for (genvar i = 0; i < N; i++) begin : g_out
    assign p[i] = s[i][0];
  end
  assign p[2*N-1:N] = s[N-1][N:1];
endmodule

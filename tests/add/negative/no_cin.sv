// NEGATIVE (wrong function): a ripple-carry adder that ignores the carry in
// (c[0] is tied to 0). Refuted in Refute.lean by one run at N = 1:
// a = 0, b = 0, cin = 1 gives s = 0, the task says s = 1.
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0] c;
  assign c[0] = 1'b0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign s[i]   = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign cout = c[N];
endmodule

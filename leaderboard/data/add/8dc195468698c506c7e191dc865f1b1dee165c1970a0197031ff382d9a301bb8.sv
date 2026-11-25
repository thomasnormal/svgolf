// svGolf task `add`: the same ripple-carry adder as add_proc.sv with the
// WHOLE bit cell in ONE `always_comb` body that writes two windows, c[i+1] and s[i]. p[i] is the propagate bit;
// when p[i] the carry out is the carry in, otherwise the operands agree and the carry is their common value a[i].
// c[i] is the carry INTO bit i; c[0] = cin, cout = c[N].
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0]   c;
  logic [N-1:0] p;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign p[i] = a[i] ^ b[i];
      always_comb begin
        if (p[i]) c[i+1] = c[i];
        else      c[i+1] = a[i];
        s[i] = p[i] ^ c[i];
      end
    end
  endgenerate
  assign cout = c[N];
endmodule

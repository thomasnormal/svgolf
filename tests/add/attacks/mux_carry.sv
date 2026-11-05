// CHECKER-LEGAL, TACTIC-ACCEPTED (not an attack): a CORRECT ripple adder whose carry is a
// multiplexer, c[i+1] = (a[i] ^ b[i]) ? c[i] : a[i] (propagate selects the carry in, else the
// operands agree and carry their common value). `check.py --unproved` passes it (it scores
// and passes every stage up to postsynth). Until WP-G S2 `check.py --unproved --tactics` reported
//   sv_structure: outside the supported fragment -- site `g_bit#1`: conditional expression
//   `?:` (outside the v1 fragment)
// and the proof would have been by hand; since S2 the sv_comb tactics read the `?:` (the equation is
// `if st.boolAt "a" i ^^ st.boolAt "b" i = true then ... else ...`, PROVING.md section 14) and the advisory
// reports `in_fragment: true`.
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
    for (i = 0; i < N; i++) begin : g_bit
      assign s[i]   = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] ^ b[i]) ? c[i] : a[i];
    end
  endgenerate
  assign cout = c[N];
endmodule

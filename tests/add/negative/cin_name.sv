// NEGATIVE (interface, port name): the carry in is called `ci`, not `cin`.
// A correct adder under its own name, but the statement's stimulus drives
// `cin`, and the interface conjunct pins the input names. Refuted in
// Refute.lean through the interface conjunct.
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         ci,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0] c;
  assign c[0] = ci;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign s[i]   = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
  endgenerate
  assign cout = c[N];
endmodule

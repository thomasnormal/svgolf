// Negative (WP-G): a CORRECT ripple adder whose carry cell is an `always_comb` `case` statement with an arm
// in `begin … end`. The function is right and every design check passes, but a `case` arm that is not a
// single assignment is outside the fragment of the sv_comb tactics (a plain `case` with single-assignment
// arms and a `default` is inside since WP-G S3a): `sv_structure` refuses it ("`case` arm is not a single
// assignment"), and the proof file
// add_proc_case.lean (the add_proc reference proof, unchanged) therefore does not compile. check.py must
// reject it at the `solution` stage: an error logged by the new tactic elaborators plus an admitted goal can
// never be ACCEPTED (the compile error, and the sorryAx in the axiom check).
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
        case (p[i])
          1'b1: begin c[i+1] = c[i]; end
          default: c[i+1] = a[i];
        endcase
      end
      assign s[i] = p[i] ^ c[i];
    end
  endgenerate
  assign cout = c[N];
endmodule

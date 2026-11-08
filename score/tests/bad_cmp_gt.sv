// Run-time ordering comparisons on multi-bit operands (one against a
// constant). In a task that bans + or - the backstop rejects each: alumacc
// lowers it to an $alu, Yosys's adder (decided 2026-11-05). The front check
// passes it, and so does a task that bans neither + nor -.
module bad_cmp_gt #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic         g, l
);
  assign g = a > b;
  assign l = a <= 5;
endmodule

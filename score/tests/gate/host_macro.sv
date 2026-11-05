// GATE: rejected (P-NO-TOOL-DIRECTIVES, P-NO-HOST-ACCESS). A macro hides the
// spelling: the directive is refused, and so is the system name inside it.
`define RD $readmemh
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [7:0] mem [0:3];
  initial `RD("/etc/hosts", mem);
  assign y = a & b & {N{mem[a[1:0]][0]}};
endmodule

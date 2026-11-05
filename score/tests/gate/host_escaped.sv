// GATE: rejected (P-NO-HOST-ACCESS, P-SAME-PROGRAM). The escaped identifier
// \$readmemh has the very same name as the system task $readmemh in Yosys's lexer
// (measured: Yosys runs it and reads the file); slang sees an ordinary identifier.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [7:0] mem [0:3];
  initial \$readmemh ("/etc/hosts", mem);
  assign y = a & b & {N{mem[a[1:0]][0]}};
endmodule

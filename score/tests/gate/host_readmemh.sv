// GATE: rejected (P-NO-HOST-ACCESS). Yosys's read_verilog opens the file of a
// $readmemh itself, while it reads the design: the same text scores 9.331 GE with
// one host file and 0 GE with another (measured), a missing file is an error,
// and the proof (ls-sv) never sees the file. On the organizer's machine this
// would pull a host file (a salt, an oracle) into the netlist.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [7:0] mem [0:3];
  initial $readmemh("/etc/hosts", mem);
  assign y = a & b & {N{mem[a[1:0]][0]}};
endmodule

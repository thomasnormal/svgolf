// GATE: passes, and the whole flow accepts it (check.py --unproved). The words of the
// refused constructs are only prose here: this comment names $readmemh("/etc/hosts", mem),
// $fopen, $system and `import "DPI-C"`, a block comment does too, so do the string
// literals below, and one identifier merely contains a `$`.
/* $dumpfile("x.vcd"); $value$plusargs("X=%d", v); export "DPI-C" function f; */
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  localparam S1 = "$readmemh(\"/etc/hosts\", mem)";
  localparam S2 = "import DPI-C; $system $fopen $test$plusargs";
  logic [N-1:0] \t$x ;
  assign \t$x = a & b;
  assign y = \t$x ;
endmodule

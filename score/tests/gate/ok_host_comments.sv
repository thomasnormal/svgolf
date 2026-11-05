// GATE: passes, and the whole flow accepts it (check.py --unproved). The words of the
// refused constructs are prose only: $readmemh("/etc/hosts", mem), $fopen, $system,
// $value$plusargs, $dumpfile, import "DPI-C" and export "DPI-C" appear in comments.
/* initial $readmemh("secret.hex", mem);   import "DPI-C" function int f(int x); */
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,   // $test$plusargs("X") would read the command line
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  assign y = a & b;       // no $fopen here, no \$readmemh either
endmodule

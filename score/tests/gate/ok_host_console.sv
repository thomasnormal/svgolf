// GATE: passes (a gate-only fixture: ls-sv refuses `initial` and a console task as a
// statement, so check.py stops at the design stage; the gate itself has no quarrel with
// it). The console and simulation-control tasks $display and $write touch no host
// resource, and the refused names are only prose here: this comment names
// $readmemh("/etc/hosts", mem), $fopen, $system and `import "DPI-C"`, a block comment
// does too, and so do the string literals below.
/* $dumpfile("x.vcd"); $value$plusargs("X=%d", v); export "DPI-C" function f; */
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  localparam S1 = "$readmemh(\"/etc/hosts\", mem)";
  localparam S2 = "import DPI-C; $system $fopen $test$plusargs";
  initial begin
    $display("band %m: %s %s", S1, S2);
    $write("done\n");
  end
  assign y = a & b;
endmodule

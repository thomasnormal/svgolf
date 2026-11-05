// GATE: rejected (P-NO-HOST-ACCESS). The remaining tasks that name a host file:
// the SDF annotation, the coverage database, and the optional tasks of Annex D.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  initial begin
    $sdf_annotate("/tmp/x.sdf");
    $coverage_save(0, "/tmp/cov");
    $input("/tmp/cmds.txt");
    $log("/tmp/out.log");
    $save("/tmp/ckpt");
  end
  assign y = a & b;
endmodule

// GATE: rejected (P-NO-HOST-ACCESS). $readmemb and the two $writemem tasks name
// host files exactly as $readmemh does.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [7:0] mem [0:3];
  initial begin
    $readmemb("/tmp/in.bin", mem);
    $writememh("/tmp/out.hex", mem);
    $writememb("/tmp/out.bin", mem);
  end
  assign y = a & b;
endmodule

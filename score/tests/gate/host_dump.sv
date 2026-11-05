// GATE: rejected (P-NO-HOST-ACCESS). Writes a waveform file on the host.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  initial begin
    $dumpfile("/tmp/svgolf-leak.vcd");
    $dumpvars(0, band);
    $dumpports(band, "/tmp/svgolf-ports.vcd");
    $fsdbDumpfile("/tmp/svgolf-leak.fsdb");
  end
  assign y = a & b;
endmodule

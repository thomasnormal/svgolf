// GATE: rejected (P-NO-HOST-ACCESS). Opens and writes a host file.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  integer fd;
  initial begin
    fd = $fopen("/tmp/svgolf-leak.txt", "w");
    $fdisplay(fd, "hi");
    $fwrite(fd, "%d", a);
    $fstrobe(fd, "s");
    $fmonitor(fd, "%d", b);
    $fclose(fd);
  end
  assign y = a & b;
endmodule

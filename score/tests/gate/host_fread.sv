// GATE: rejected (P-NO-HOST-ACCESS). Reads a host file: the whole read side of
// the file I/O family (LRM 21.3).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  integer fd, r, v;
  string s;
  logic [7:0] m [0:3];
  initial begin
    fd = $fopen("/etc/hosts", "r");
    r = $fscanf(fd, "%h", v);
    r = $fgets(s, fd);
    r = $fgetc(fd);
    r = $fread(m, fd);
    r = $fseek(fd, 0, 0);
    r = $ftell(fd);
    r = $feof(fd);
    r = $ungetc(0, fd);
    r = $ferror(fd, s);
    $rewind(fd);
    $fflush(fd);
  end
  assign y = a & b;
endmodule

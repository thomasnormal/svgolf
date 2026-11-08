// A run-time write through a SIGNED index: t[i], a signed 2-bit i, addresses -2..1. The standard
// reads a negative index as out of range (the write has no effect) and ls-sv reads every index as
// unsigned, so the write exception of rule (d) does not apply. And a select inside a written
// target's index is a read: u[a[j]] writes in range, but a[j] reads a[7:4], which a 4-bit a lacks.
module oob_signed_write #(parameter int N = 4) (
  input  logic [N-1:0]      a,
  input  logic signed [1:0] i,
  input  logic [2:0]        j,
  output logic [N-1:0]      y
);
  logic [3:0] t, u;
  always_comb begin
    t = 4'b0000;
    t[i] = 1'b1;
    u = 4'b0000;
    u[a[j]] = 1'b1;
  end
  assign y = a ^ t ^ u;
endmodule

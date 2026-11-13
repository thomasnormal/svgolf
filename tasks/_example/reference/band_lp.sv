// svGolf task `_example` -- the AND circuit of band.sv, with localparams:
// the header localparam `W` sizes the ports, and the body localparam `MSB` is
// constant arithmetic (allowed under the task's arithmetic banlist). The
// checker compares only the overridable parameters (`N`) with the task.
module band #(parameter int N = 4, localparam int W = N) (
  input  logic [W-1:0] a,
  input  logic [W-1:0] b,
  output logic [W-1:0] y
);
  localparam int MSB = W - 1;
  assign y = a & b;
endmodule

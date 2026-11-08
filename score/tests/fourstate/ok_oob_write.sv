// A run-time WRITE whose unsigned index can pass the top of the range: t[k], a 2-bit k into [2:0].
// An out-of-range write has no effect (IEEE 1800-2023 §11.5.1), in ls-sv and in Yosys, so nothing
// here can produce an x (the write exception of rule (d)).
module ok_oob_write #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [1:0]   k,
  output logic [N-1:0] y
);
  logic [2:0] t;
  always_comb begin
    t = 3'b000;
    t[k] = 1'b1;
  end
  assign y = a ^ {1'b0, t};
endmodule

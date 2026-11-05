// A flip-flop: not a combinational netlist, the GE table does not price it.
module reg1 (input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) q <= d;
endmodule

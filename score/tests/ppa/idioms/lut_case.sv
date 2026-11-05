// A constant-table case: output bits aliased to constants and to each other, and escaped wires full of constant concatenations.
// A PPA netlist-reader test design (score/tests/ppa/idioms.json): not a task submission, never banned or proved.
module idiom #(parameter int N = 8) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [5:0] t;
  always_comb begin
    case (b[2:0])
      3'd0:    t = 6'h3f;
      3'd1:    t = 6'h06;
      3'd2:    t = 6'h5b;
      3'd3:    t = 6'h4f;
      3'd4:    t = 6'h66;
      default: t = 6'h6d;
    endcase
  end
  assign y = {2'b00, t};
endmodule

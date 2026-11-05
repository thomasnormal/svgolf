// A 4:1 case mux with 8-bit arms: the $pmux leaves \_N_.B [23:8] = { a, b }, a part select after an escaped name.
// A PPA netlist-reader test design (score/tests/ppa/idioms.json): not a task submission, never banned or proved.
module idiom #(parameter int N = 8) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    case (b[1:0])
      2'd0:    y = a;
      2'd1:    y = b;
      2'd2:    y = a & b;
      default: y = a | b;
    endcase
  end
endmodule

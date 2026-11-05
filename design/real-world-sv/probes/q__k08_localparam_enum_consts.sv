module t #(parameter int N = 16) (input logic [1:0] o, input logic [7:0] a, b, output logic [7:0] y);
  localparam logic [1:0] OP_AND = 2'd0, OP_OR = 2'd1;
  always_comb begin
    case (o)
      OP_AND: y = a & b;
      OP_OR:  y = a | b;
      default: y = a;
    endcase
  end
endmodule

// H2 style S12: unique case (fpnew / cva6 FSM style) in a combinational block.
module s12_unique (input logic [1:0] sel, input logic [3:0] a, b, c, output logic [3:0] y);
  always_comb begin
    unique case (sel)
      2'd0: y = a;
      2'd1: y = b;
      default: y = c;
    endcase
  end
endmodule

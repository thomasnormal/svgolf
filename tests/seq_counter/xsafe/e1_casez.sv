// E1: casez with z/? wildcards (allowed by the gate). Both ls-sv and Yosys treat z/? as wildcards.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [1:0] s;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; s <= 2'b00; end
    else begin
      s <= s + 2'b1;
      casez (s)
        2'b1?: q <= q + 1'b1;
        default: q <= q;
      endcase
    end
endmodule

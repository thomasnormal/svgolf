module t #(parameter int N = 16) (input logic [3:0] a, output logic [1:0] y);
  always_comb begin
    case (1'b1)
      a[3]: y = 2'd3;
      a[2]: y = 2'd2;
      a[1]: y = 2'd1;
      default: y = 2'd0;
    endcase
  end
endmodule

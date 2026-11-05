module t (input logic [7:0] a, output logic [7:0] y);
  always_comb begin
    priority case (1'b1)
      a[0]: y = 8'd1;
      a[1]: y = 8'd2;
      default: y = 8'd0;
    endcase
  end
endmodule

module t (input logic [3:0] r, output logic [1:0] idx, output logic v);
  always_comb begin
    v = 1'b1;
    casez (r)
      4'b1???: idx = 2'd3;
      4'b01??: idx = 2'd2;
      4'b001?: idx = 2'd1;
      4'b0001: idx = 2'd0;
      default: begin idx = 2'd0; v = 1'b0; end
    endcase
  end
endmodule

// H2 style S1: restoring division as a procedural `for` loop inside always_comb with a running remainder
// (the way most small integer dividers are written).
module s1_for_always (
  input  logic [10:0] n, d,
  output logic [12:0] qq,
  output logic [11:0] r
);
  always_comb begin
    r = {1'b0, n};
    for (int i = 12; i >= 0; i--) begin
      if (r >= {1'b0, d}) begin
        qq[i] = 1'b1;
        r = (r - {1'b0, d}) << 1;
      end else begin
        qq[i] = 1'b0;
        r = r << 1;
      end
    end
  end
endmodule

// H2 style S1b: S1 with a MODULE-LEVEL loop variable (`integer i;`), so no block-local declaration.
module s1b_for_module_int (
  input  logic [10:0] n, d,
  output logic [12:0] qq,
  output logic [11:0] r
);
  integer i;
  always_comb begin
    r = {1'b0, n};
    for (i = 12; i >= 0; i = i - 1) begin
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

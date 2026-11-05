// H2 probe B4b: the divider rewritten for today's fragment: the difference named, the doubling a concatenation.
module b4b_div_rw (
  input  logic [10:0] na4, nb4,
  output logic [12:0] qq,
  output logic [11:0] rem13
);
  logic [13:0][11:0] rem;
  logic [12:0][11:0] dif;
  assign rem[0] = {1'b0, na4};
  for (genvar i = 0; i < 13; i++) begin : g_div
    assign qq[12 - i]  = (rem[i] >= {1'b0, nb4});
    assign dif[i]      = rem[i] - {1'b0, nb4};
    assign rem[i + 1]  = qq[12 - i] ? {dif[i][10:0], 1'b0} : {rem[i][10:0], 1'b0};
  end
  assign rem13 = rem[13];
endmodule

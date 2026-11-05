// H2 probe B4: the 13-step restoring divider (lines 91-99), as written.
module b4_div (
  input  logic [10:0] na4, nb4,
  output logic [12:0] qq,
  output logic [11:0] rem13
);
  logic [13:0][11:0] rem;
  assign rem[0] = {1'b0, na4};
  for (genvar i = 0; i < 13; i++) begin : g_div
    assign qq[12 - i]  = (rem[i] >= {1'b0, nb4});
    assign rem[i + 1] = qq[12 - i] ? ((rem[i] - {1'b0, nb4}) << 1) : (rem[i] << 1);
  end
  assign rem13 = rem[13];
endmodule

// H2 probe B9: the special-case always_comb (lines 134-146), as written.
module b9_table (
  input  logic        s, a_nan, b_nan, a_inf, b_inf, a_zero, b_zero, ovf,
  input  logic [14:0] mag,
  output logic [15:0] q
);
  always_comb begin
    if (a_nan || b_nan || (a_inf && b_inf) || (a_zero && b_zero))
      q = 16'h7E00;
    else if (a_inf || b_zero)
      q = {s, 15'h7C00};
    else if (b_inf || a_zero)
      q = {s, 15'h0000};
    else if (ovf)
      q = {s, 15'h7C00};
    else
      q = {s, mag};
  end
endmodule

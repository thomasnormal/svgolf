// H2 probe B4c: the divider with `<< 1` shifts of ACCESSES (row, named difference row) and a named {1'b0, nb4}.
module b4c_div_shift_lp (
  input  logic [10:0] na4, nb4,
  output logic [12:0] qq,
  output logic [11:0] rem13
);
  localparam integer R = 14;
  localparam integer C = 12;
  localparam integer Q = 13;
  logic [R-1:0][C-1:0]  rem;
  logic [Q-1:0][C-1:0]  dif;
  logic [C-1:0]         nb12;
  assign nb12   = {1'b0, nb4};
  assign rem[0] = {1'b0, na4};
  for (genvar i = 0; i < 13; i++) begin : g_div
    assign qq[12 - i] = (rem[i] >= nb12);
    assign dif[i]     = rem[i] - nb12;
    assign rem[i + 1] = qq[12 - i] ? (dif[i] << 1) : (rem[i] << 1);
  end
  assign rem13 = rem[13];
endmodule

// micro: the same with literal dimensions.
module g2_row_lit (input logic [2:0] x, output logic [2:0] y);
  logic [3:0][2:0] r;
  assign r[0] = x;
  for (genvar i = 0; i < 3; i++) begin : g
    assign r[i + 1] = ~r[i];
  end
  assign y = r[3];
endmodule

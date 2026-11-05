// micro: genvar-indexed row WRITE only (reads by cells), localparam dimensions.
module g6_rowwrite_lp (input logic [2:0] x, output logic [2:0] y);
  localparam integer R = 4;
  localparam integer C = 3;
  logic [R-1:0][C-1:0] r;
  assign r[0] = x;
  for (genvar i = 0; i < 3; i++) begin : g
    assign r[i + 1] = {r[i][1], r[i][0], r[i][2]};
  end
  assign y = r[3];
endmodule

// micro: genvar-indexed CELL accesses of a 2-D array with localparam dimensions (nested loops, as in mul_n).
module g4_cell_lp (input logic [2:0] x, output logic [2:0] y);
  localparam integer R = 4;
  localparam integer C = 3;
  logic [R-1:0][C-1:0] r;
  assign r[0] = x;
  for (genvar i = 0; i < 3; i++) begin : g
    for (genvar k = 0; k < 3; k++) begin : h
      assign r[i + 1][k] = ~r[i][k];
    end
  end
  assign y = r[3];
endmodule

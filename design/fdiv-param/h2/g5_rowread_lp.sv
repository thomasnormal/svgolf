// micro: genvar-indexed row READ only (writes by cells), localparam dimensions.
module g5_rowread_lp (input logic [2:0] x, output logic [2:0] y);
  localparam integer R = 4;
  localparam integer C = 3;
  logic [R-1:0][C-1:0] r;
  logic [2:0] w;
  assign r[0] = x;
  for (genvar i = 0; i < 3; i++) begin : g
    for (genvar k = 0; k < 3; k++) begin : h
      assign r[i + 1][k] = ~r[i][k];
    end
  end
  assign w = r[1] ^ r[2];
  assign y = w;
endmodule

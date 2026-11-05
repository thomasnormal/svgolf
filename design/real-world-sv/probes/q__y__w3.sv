typedef enum logic [1:0] {A0, A1, A2, A3} st_e;
module t (input st_e s, input logic [7:0] a, output logic [7:0] y);
  assign y = (s == A1) ? a : '0;
endmodule

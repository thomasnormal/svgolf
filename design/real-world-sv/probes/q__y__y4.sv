module t (input logic [7:0] a, output logic [7:0] y);
  typedef enum logic [1:0] {A0, A1} e_t;
  e_t e;
  assign e = e_t'(a[1:0]);
  assign y = (e == A1) ? a : ~a;
endmodule

module t #(parameter int N = 16) (input logic [7:0] a, output logic [7:0] y);
  typedef struct { logic [7:0] x; } s_t;
  s_t s;
  assign s.x = a;
  assign y = s.x;
endmodule

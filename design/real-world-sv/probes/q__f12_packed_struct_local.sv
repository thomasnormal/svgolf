module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  typedef struct packed { logic [N-1:0] x; logic [N-1:0] z; } pair_t;
  pair_t s;
  assign s = {a, b};
  assign y = s.x ^ s.z;
endmodule

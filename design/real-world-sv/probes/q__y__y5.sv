typedef struct packed { logic [7:0] x; logic [7:0] z; } pair_t;
module t (input pair_t s, output logic [7:0] y);
  assign y = s.x ^ s.z;
endmodule

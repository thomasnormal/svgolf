package pk;
  localparam int W = 8;
  typedef logic [7:0] byte_t;
endpackage
module t (input pk::byte_t a, output logic [pk::W-1:0] y);
  assign y = a ^ 8'h1b;
endmodule

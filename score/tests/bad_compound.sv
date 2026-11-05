module bad_compound #(parameter int N = 4) (input logic [N-1:0] x, y, output logic [N-1:0] s);
  always_comb begin
    s = x;
    s += y;
  end
endmodule

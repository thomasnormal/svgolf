module bad_incdec #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] s);
  always_comb begin
    s = a;
    s++;
  end
endmodule

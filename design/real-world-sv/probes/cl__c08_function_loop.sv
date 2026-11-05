module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  function automatic logic [2*N-2:0] clmul(input logic [N-1:0] x, y);
    logic [2*N-2:0] r;
    r = '0;
    for (int i = 0; i < N; i++)
      if (y[i]) r = r ^ ({{(N-1){1'b0}}, x} << i);
    clmul = r;
  endfunction
  assign p = clmul(a, b);
endmodule

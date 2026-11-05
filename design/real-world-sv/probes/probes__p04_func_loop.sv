module t #(parameter int N = 8) (input logic [N-1:0] a, b, output logic [2*N-1:0] p);
  function automatic logic [2*N-1:0] clmul(input logic [N-1:0] x, y);
    logic [2*N-1:0] acc;
    acc = '0;
    for (int i = 0; i < N; i++)
      if (y[i]) acc ^= (2*N)'(x) << i;
    return acc;
  endfunction
  assign p = clmul(a, b);
endmodule

// A function called with a RUN-TIME argument is hardware: its body's `/` is banned.
module bad_runtime_fn #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);
  function automatic [N-1:0] third(input [N-1:0] v);
    third = v / 3;
  endfunction
  assign y = third(a);
endmodule

// GATE: rejected (P-NO-HOST-ACCESS). DPI export: native code may call back in.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  function int f(input int x);
    return x;
  endfunction
  export "DPI-C" function f;
  assign y = a & b;
endmodule

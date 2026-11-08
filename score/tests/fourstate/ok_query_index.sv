// Rule (d): an index slang evaluates to a constant whose names are only the arguments of type and array
// query functions is a constant select (IEEE 1800-2023 §20.6.2, §20.7): `s[$bits(s) - 1]` with `s` signed,
// `v[$high(v)]`, `v[$size(v) - 2]` (the 2026-11-06 adversarial round's finding F3: refused before as a
// run-time 32-bit index).
module ok_query_index #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic y, z, w
);
  logic signed [N-1:0] s;
  logic [N-1:0] v;
  assign s = a;
  assign v = a;
  assign y = s[$bits(s) - 1];
  assign z = v[$high(v)];
  assign w = v[$size(v) - 2];
endmodule

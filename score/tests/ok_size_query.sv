// The size queries of a signal are constants (decided 2026-11-07, banlist.py CONST_QUERIES): `$bits(a)` and
// `$size(a)` name `a` without reading it, so `/`, `%` and `+` between them are elaboration-time (the shape of
// tests/seq_counter/xsafe/t2_bits_div.sv, `q + ($bits(q) / $bits(q))`). Passes both checks.
module ok_size_query #(parameter int N = 16) (
  input  logic [N-1:0] a,
  output logic [31:0]  k
);
  assign k = ($bits(a) / $bits(a)) + ($size(a) % 3);
endmodule

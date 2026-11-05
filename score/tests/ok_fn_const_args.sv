// A function called with constant arguments whose body reads only its own
// argument is constant (Yosys folds it): passes a `/ %` banlist.
module ok_fn_const_args (input logic [15:0] a, input logic [15:0] b, output logic [15:0] q);
  function automatic logic [15:0] half(input int k);
    half = k / 2;
  endfunction
  assign q = a ^ half(6);
endmodule

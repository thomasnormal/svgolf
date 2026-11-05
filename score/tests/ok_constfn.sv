// A constant function that divides, evaluated at elaboration only: must PASS
// a `/ %` banlist.
module ok_constfn #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);
  function automatic integer lg(input integer x);
    integer r, v;
    begin
      r = 0;
      v = x;
      while (v > 1) begin
        v = v / 2;
        r = r + 1;
      end
      lg = r;
    end
  endfunction
  localparam integer L = lg(N);
  assign y = a >> L;
endmodule

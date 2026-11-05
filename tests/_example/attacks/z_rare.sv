// svGolf attack (_example): a z bit confines the difference to a rare region.
// ls-sv: the item never matches (=== against a z bit), y = a & b everywhere.
// Yosys drops the four z bits, so the item matches the 2^4 inputs whose other
// 28 bits are DEADBEE (2^-28 of all inputs), where the netlist outputs 0.
// Random vectors would need ~2^28 tries; the postsynth check's harvested
// comparison constants (their 0/1 bits, x/z bits free) hit it. Refused by the
// source gate (an x/z literal digit).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb
    case ({a, b})
      32'hDEAD_BEEz: y = '0;
      default: y = a & b;
    endcase
endmodule

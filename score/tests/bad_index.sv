// Index arithmetic over a SIGNAL is run-time arithmetic (an adder on `j`).
module bad_index #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [3:0]   j,
  output logic         y
);
  assign y = a[j + 1];
endmodule

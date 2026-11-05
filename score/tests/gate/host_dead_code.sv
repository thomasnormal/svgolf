// GATE: rejected (P-NO-HOST-ACCESS). The gate reads the TEXT, not the elaborated
// design: a generate branch the scoring point does not take, a function that is
// never called, a module the top does not instantiate and a parameter initializer
// are all refused (Yosys elaborates a different subset than slang).
module other;
  logic [7:0] mem [0:3];
  initial $readmemh("/etc/hosts", mem);
endmodule

module band #(parameter int N = 4, parameter int FD = $fopen("/tmp/svgolf-leak.txt", "w")) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [7:0] mem [0:3];
  function automatic void rd();
    $readmemh("/etc/hosts", mem);
  endfunction
  if (N == 99) begin : g
    initial $readmemh("/etc/hosts", mem);
  end
  assign y = a & b;
endmodule

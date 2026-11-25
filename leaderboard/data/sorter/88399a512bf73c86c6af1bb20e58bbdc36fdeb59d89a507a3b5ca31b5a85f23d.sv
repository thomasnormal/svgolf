// svGolf task `sorter`: direct-output insertion-cell array at latency 2N - 1 (parametric in N, W >= 1).
// Derived from the insertion-cell architecture of tasks/sorter/reference/sorter_ins.sv (record 7b878f6d1ea4,
// adapted from andrewpeck/cell-sort, MIT License, Copyright (c) 2024-2025 Andrew Peck) and record 3b1ec4b16d7a.
// Changes: drives out_valid/out_data directly from registered cell 0 (latency 2N - 1, removing the output
// register stage), removes reset/clearing on the N*W data flops by guarding comparisons with !tok[k],
// and uses unsigned >= comparisons (in_data >= data[k]).
module sorter #(parameter int N = 8, parameter int W = 8) (
  input  logic         clk, rst,
  input  logic         start, in_valid,
  input  logic [W-1:0] in_data,
  output logic         out_valid,
  output logic [W-1:0] out_data
);
  logic [N*W-1:0] data;
  logic [N-1:0]   tok;

  assign out_valid = tok[0];
  assign out_data  = data[0 +: W];

  for (genvar k = 0; k < N-1; k++) begin : gen_cell
    always_ff @(posedge clk) begin
      if (!in_valid || !tok[k+1] || (in_data >= data[(k+1)*W +: W]))
        data[k*W +: W] <= data[(k+1)*W +: W];
      else if (!tok[k] || (in_data >= data[k*W +: W]))
        data[k*W +: W] <= in_data;
      tok[k] <= (~rst) & tok[k+1];
    end
  end

  always_ff @(posedge clk) begin
    if (in_valid && (!tok[N-1] || (in_data >= data[(N-1)*W +: W])))
      data[(N-1)*W +: W] <= in_data;
    tok[N-1] <= (~rst) & in_valid;
  end
endmodule

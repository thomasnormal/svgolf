// This design is derived from the svGolf sorter reference, tasks/sorter/reference/sorter_ins.sv.
// PROVENANCE. Adapted from andrewpeck/cell-sort, https://github.com/andrewpeck/cell-sort, commit
// cfc46709eaa911858136c2300327ca73bf1eb9a0, files cell_sort.sv and unit_cell.sv, MIT License,
// Copyright (c) 2024-2025 Andrew Peck (the notice is kept below, as the license requires).
//
// MIT License
//
// Copyright (c) 2024-2025 Andrew Peck
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
`timescale 1ns / 1ps
`default_nettype none
// svgolf-latency: 16
module sorter #(parameter int N = 8, parameter int W = 8) (
  input  logic         clk, rst,
  input  logic         start, in_valid,
  input  logic [W-1:0] in_data,
  output logic         out_valid,
  output logic [W-1:0] out_data
);
  logic [N*W-1:0] data;
  logic [N-1:0]   tok;

  for (genvar k = 0; k < N-1; k++) begin : gen_cell
    always_ff @(posedge clk) begin
      if (in_valid && !(data[(k+1)*W +: W] < in_data) && data[k*W +: W] < in_data)
        data[k*W +: W] <= in_data;
      else if (!in_valid || data[(k+1)*W +: W] < in_data)
        data[k*W +: W] <= data[(k+1)*W +: W];
      tok[k] <= tok[k+1];
      if (rst) begin
        data[k*W +: W] <= '0;
        tok[k] <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (in_valid) begin
      if (data[(N-1)*W +: W] < in_data)
        data[(N-1)*W +: W] <= in_data;
    end else
      data[(N-1)*W +: W] <= '0;
    tok[N-1] <= in_valid;
    if (rst) begin
      data[(N-1)*W +: W] <= '0;
      tok[N-1] <= 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    out_valid <= tok[0];
    out_data  <= data[0 +: W];
    if (rst) out_valid <= 1'b0;
  end
endmodule

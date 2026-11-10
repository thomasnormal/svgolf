// Attack for task sorter (tests/expected.json, `attacks`; review L1 of 2026-11-08, the rule-1 decision of
// 2026-11-09): the proved reference tasks/sorter/reference/sorter_ins.sv with ONE change (the output stage),
// a design whose every claimed snapshot is the reference's: the outputs are registered as ov_q and od_q, and
// out_valid is ov_q gated by the reset (`assign out_valid = ov_q & ~rst`).
// Wrong on the wire: in the cycle of a reset entry the snapshot before it is still claimed, but the wire shows
// out_valid = 0, so a transaction's last output is hidden from a consumer when a reset follows it. Rule 1 with
// nothing exempt (`MooreOutDep d []`, since 2026-11-09) refuses the path from rst to out_valid, for every N, W.
// Every check that needs no proof passes it; the reference's proof (reference/sorter_ins.lean) must FAIL on it.
// Derived from andrewpeck/cell-sort (MIT, cfc46709; the reference's header has the provenance and changes):
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

module sorter #(parameter int N = 8, parameter int W = 8) (
  input  logic         clk, rst,
  input  logic         start, in_valid,
  input  logic [W-1:0] in_data,
  output logic         out_valid,
  output logic [W-1:0] out_data
);
  logic [N*W-1:0] data;  // cell k's value: data[k*W +: W]; cell N-1 is the top ("best") cell
  logic [N-1:0]   tok;   // cell k's valid token

  // cells 0 .. N-2: upstream's unit_cell; the upper neighbour is cell k+1
  for (genvar k = 0; k < N-1; k++) begin : gen_cell
    always_ff @(posedge clk) begin
      if (in_valid) begin
        if (in_data > data[(k+1)*W +: W])         // the neighbour is pushed: take its value
          data[k*W +: W] <= data[(k+1)*W +: W];
        else if (in_data > data[k*W +: W])        // the input beats this cell's value
          data[k*W +: W] <= in_data;
      end else
        data[k*W +: W] <= data[(k+1)*W +: W];     // drain: shift down
      tok[k] <= tok[k+1];
      if (rst) begin
        data[k*W +: W] <= '0;
        tok[k] <= 1'b0;
      end
    end
  end

  // the top cell N-1: never pushed into (upstream's push[DEPTH] = 0); drains in the empty value 0
  always_ff @(posedge clk) begin
    if (in_valid) begin
      if (in_data > data[(N-1)*W +: W])
        data[(N-1)*W +: W] <= in_data;
    end else
      data[(N-1)*W +: W] <= '0;
    tok[N-1] <= in_valid;
    if (rst) begin
      data[(N-1)*W +: W] <= '0;
      tok[N-1] <= 1'b0;
    end
  end

  // the streaming output: cell 0 and its token, registered
  logic ov_q;
  logic [W-1:0] od_q;
  always_ff @(posedge clk) begin
    ov_q <= tok[0];
    od_q <= data[0 +: W];
    if (rst) ov_q <= 1'b0;
  end
  assign out_valid = ov_q & ~rst;
  assign out_data = od_q;
endmodule

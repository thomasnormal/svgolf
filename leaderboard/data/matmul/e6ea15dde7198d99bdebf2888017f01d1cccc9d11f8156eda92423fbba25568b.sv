// Static timetable matmul.  Each output cell owns a compile-time laid-out
// stream of the A row and B column words.  A local stream register consumes
// one timetable word per busy cycle, so the schedule is spatial rather than
// a runtime loop or a dynamic operand index.
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input logic clk, rst,
  input logic start,
  input logic [N*N*W-1:0] A, B,
  output logic done,
  output logic [N*N*AccW-1:0] C
);
  logic [31:0] k;
  logic busy;
  logic [N*N*N*W-1:0] a_timetable, b_timetable;
  logic [N*N*N*W-1:0] a_stream, b_stream;

  always_ff @(posedge clk) begin
    if (rst) begin
      busy <= 1'b0;
      done <= 1'b0;
      k <= 32'd0;
      a_stream <= '0;
      b_stream <= '0;
    end else if (start) begin
      busy <= 1'b1;
      done <= 1'b0;
      k <= 32'd0;
      a_stream <= a_timetable;
      b_stream <= b_timetable;
    end else if (busy) begin
      k <= k + 32'd1;
      a_stream <= a_stream >> W;
      b_stream <= b_stream >> W;
      if (k == N - 1) begin
        busy <= 1'b0;
        done <= 1'b1;
      end
    end
  end

  for (genvar i = 0; i < N; i++) begin : g_time_row
    for (genvar j = 0; j < N; j++) begin : g_time_col
      for (genvar t = 0; t < N; t++) begin : g_time_word
        assign a_timetable[((i*N+j)*N+t)*W +: W] = A[(i*N+t)*W +: W];
        assign b_timetable[((i*N+j)*N+t)*W +: W] = B[(t*N+j)*W +: W];
      end
      always_ff @(posedge clk) begin
        if (rst) begin
          C[(i*N+j)*AccW +: AccW] <= '0;
        end else if (start) begin
          C[(i*N+j)*AccW +: AccW] <= '0;
        end else if (busy) begin
          C[(i*N+j)*AccW +: AccW] <= C[(i*N+j)*AccW +: AccW]
            + {{AccW{a_stream[(i*N+j)*N*W + W - 1]}},
               a_stream[(i*N+j)*N*W +: W]}
            * {{AccW{b_stream[(i*N+j)*N*W + W - 1]}},
               b_stream[(i*N+j)*N*W +: W]};
        end
      end
    end
  end
endmodule

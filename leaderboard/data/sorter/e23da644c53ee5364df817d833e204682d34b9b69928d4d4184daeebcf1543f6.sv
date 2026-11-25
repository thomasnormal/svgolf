// svgolf-latency: 15
module sorter #(parameter int N = 8, parameter int W = 8) (
  input  logic         clk, rst,
  input  logic         start, in_valid,
  input  logic [W-1:0] in_data,
  output logic         out_valid,
  output logic [W-1:0] out_data
);
  logic [N*W-1:0] data;
  logic [N-1:0]   tok, g;

  assign out_valid = tok[0];
  assign out_data  = data[0 +: W];

  for (genvar k = 0; k < N; k++) begin : gen_cmp
    assign g[k] = in_valid && tok[k] && (in_data < data[k*W +: W]);
  end

  for (genvar k = 0; k < N-1; k++) begin : gen_cell
    always_ff @(posedge clk) begin
      data[k*W +: W] <= ({W{!g[k+1]}} & data[(k+1)*W +: W]) |
                        ({W{g[k+1] && !g[k]}} & in_data[W-1:0]) |
                        ({W{g[k]}} & data[k*W +: W]);
      tok[k] <= rst ? 1'b0 : tok[k+1];
    end
  end

  always_ff @(posedge clk) begin
    if (!g[N-1])
      data[(N-1)*W +: W] <= in_data;
    tok[N-1] <= rst ? 1'b0 : in_valid;
  end
endmodule

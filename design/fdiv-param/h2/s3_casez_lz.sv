// H2 style S3: casez leading-zero counter, then a run-time left shift by the count (OpenCores / PULP style).
module s3_casez_lz (
  input  logic [10:0] m,
  output logic [10:0] nm,
  output logic [3:0]  lz
);
  always_comb begin
    casez (m)
      11'b1??????????: lz = 4'd0;
      11'b01?????????: lz = 4'd1;
      11'b001????????: lz = 4'd2;
      11'b0001???????: lz = 4'd3;
      11'b00001??????: lz = 4'd4;
      11'b000001?????: lz = 4'd5;
      11'b0000001????: lz = 4'd6;
      11'b00000001???: lz = 4'd7;
      11'b000000001??: lz = 4'd8;
      11'b0000000001?: lz = 4'd9;
      11'b00000000001: lz = 4'd10;
      default:         lz = 4'd11;
    endcase
  end
  assign nm = m << lz;
endmodule
